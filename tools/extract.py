#!/usr/bin/env python3
"""Invoke the coq-lsp `coq/extract` command on a goal in an open proof.

Usage:
    extract.py <file.v> <line> <col> <name> [--root DIR] [--skip-annotations]

  By default it also inserts commented Require + `eapply <name>_proof` hints into
  the source file right above the extraction point (comments only -- coq-lsp
  ignores them, so no re-elaboration). Pass --skip-annotations to disable.

  <line>/<col> are 1-indexed (as shown in your editor). The cursor should be on
  the sentence whose *preceding* goal you want to extract (coq-lsp "Prev" mode).

It generates, next to <file.v>:
    <name>_goal.v   - the closed goal as `Definition <name>_Goal` (always rewritten)
    <name>_proof.v  - `Lemma <name>_proof : ... . Proof. intros .... Admitted.`
and prints the paths plus the `eapply <name>_proof` to drop into the proof.

Then:  coqc -R <root>/src lzma <name>_goal.v && coqc ... <name>_proof.v
       add `Require Import ...<name>_proof.` to the main file, replace the
       tactic block with `eapply <name>_proof; try eassumption.`
       (to fully prove it, paste the original tactics into <name>_proof.v
        before `Admitted` and change it to `Qed`.)
"""
import json, subprocess, os, sys, argparse, re

# The coq-lsp server to drive. Defaults to the `coq-lsp` on PATH (e.g. an
# opam-installed one, which has `coq/extract` once this branch is installed).
# Override with COQLSP=/path/to/coq_lsp.exe to use an in-tree _build binary.
SRV = os.environ.get("COQLSP", "coq-lsp")


def errors_before(diags, line0, char0):
    """Error-severity (LSP severity 1) diagnostics whose start is strictly before
    the 0-indexed (line0, char0) extraction point -- i.e. broken sentences
    upstream of it. Their presence means coq/extract cannot produce a sound goal."""
    def start(d):
        st = (d.get("range") or {}).get("start") or {}
        return (st.get("line", 0), st.get("character", 0))
    out = [d for d in (diags or [])
           if d.get("severity") == 1 and start(d) < (line0, char0)]
    out.sort(key=start)
    return out


CONFIRM_ML = 'coq-lsp.confirm-extraction'


_CONFIRM_PAT = re.compile(r'(confirm_extraction\s+")[0-9a-f]+(")')


def annotate_source(path, line_1, name, proof_module, apply_with, hash_):
    """Wire the [confirm_extraction "<hash>"] tripwire at the extraction site.

    Re-extraction (the cursor is on -- or just before -- an existing
    [confirm_extraction] tactic): refresh the hash on THAT line in place; nothing
    else. Fresh extraction: replace the goal's tactic with an active
    [confirm_extraction "<hash>"] (it admits the goal and guards staleness) and
    insert an explanatory comment block above it. Returns
    "updated"/"unchanged"/"inserted"/None."""
    lines = open(path).read().split("\n")
    idx = line_1 - 1
    if not (0 <= idx < len(lines)):
        return None
    # Request: when called on (or right before) a confirm_extraction line, just
    # update the hash on that line -- do not scan a window or insert anything.
    for j in (idx, idx + 1):
        if 0 <= j < len(lines) and "confirm_extraction" in lines[j]:
            new = _CONFIRM_PAT.sub(r"\g<1>" + hash_ + r"\g<2>", lines[j])
            if new != lines[j]:
                lines[j] = new
                open(path, "w").write("\n".join(lines))
                return "updated"
            return "unchanged"
    # Fresh site.
    src = lines[idx]
    indent = src[: len(src) - len(src.lstrip())]
    block = [
        f"{indent}(* --- coq-lsp extract: this goal is now extracted to {name}_proof.v --- *)",
        f"{indent}(* `confirm_extraction` tactic is here to ensure the extracted goal is up to date. It admits the goal. *)",
        f"{indent}(* To wire it add: *)",
        f'{indent}(* 1. near the top of this file:  Declare ML Module "{CONFIRM_ML}".',
        f"{indent}                       Require Import {proof_module}. *)",
        f"{indent}(* 2. replace the `confirm_extraction` tactic with *)",
        f"{indent}(* {apply_with}; try eassumption. *)",
    ]
    lines[idx] = f'{indent}confirm_extraction "{hash_}".'
    lines[idx:idx] = block
    open(path, "w").write("\n".join(lines))
    return "inserted"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("line", type=int, help="1-indexed line")
    ap.add_argument("col", type=int, help="1-indexed column")
    ap.add_argument("name")
    ap.add_argument("--root", default=None, help="workspace root (default: cwd)")
    ap.add_argument("--skip-annotations", action="store_true",
                    help="do not insert the commented Require + eapply hints into "
                         "the source file (annotation is on by default)")
    a = ap.parse_args()

    f = os.path.abspath(a.file)
    root = os.path.abspath(a.root) if a.root else os.getcwd()
    uri = "file://" + f
    env = dict(os.environ)
    # An opam-installed coq-lsp needs no special env. Only when driving an
    # in-tree _build binary against an opam install do the serlib companion
    # .cmxs clash on load -- set COQLSP_NO_SERLIB=1 yourself in that case.
    p = subprocess.Popen([SRV], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL, env=env)

    def send(m):
        b = json.dumps(m).encode()
        p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(b) + b)
        p.stdin.flush()

    def readmsg():
        hdr = b""
        while b"\r\n\r\n" not in hdr:
            c = p.stdout.read(1)
            if not c:
                return None
            hdr += c
        n = int([l for l in hdr.decode().split("\r\n")
                 if l.lower().startswith("content-length")][0].split(":")[1])
        body = b""
        while len(body) < n:
            ch = p.stdout.read(n - len(body))
            if not ch:
                return None
            body += ch
        return json.loads(body)

    def wait(i, extract_pos=None):
        """Wait for the response to request [i]. If [extract_pos] is given, also
        watch published diagnostics and bail out the MOMENT an error is reported
        before the extraction point. coq/extract is a postponed request: it does
        not answer until the document is checked up to the point (minutes on a big
        file), but a single broken sentence upstream already dooms the extraction
        -- so fail fast instead of waiting. Returns the response dict, None on EOF,
        or {"errors_before": [...]} on a fast-fail."""
        while True:
            m = readmsg()
            if m is None:
                return None
            if extract_pos is not None \
                    and m.get("method") == "textDocument/publishDiagnostics":
                errs = errors_before((m.get("params") or {}).get("diagnostics"),
                                     *extract_pos)
                if errs:
                    return {"errors_before": errs}
            if m.get("id") == i and ("result" in m or "error" in m):
                return m

    send({"jsonrpc": "2.0", "id": 1, "method": "initialize",
          "params": {"processId": os.getpid(), "rootUri": "file://" + root,
                     "capabilities": {}}})
    wait(1)
    send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
    send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
          "params": {"textDocument": {"uri": uri, "languageId": "coq",
                                      "version": 1, "text": open(f).read()}}})
    extract_pos = (a.line - 1, a.col - 1)
    send({"jsonrpc": "2.0", "id": 2, "method": "coq/extract",
          "params": {"textDocument": {"uri": uri},
                     "position": {"line": extract_pos[0], "character": extract_pos[1]},
                     "name": a.name}})
    r = wait(2, extract_pos=extract_pos)
    send({"jsonrpc": "2.0", "id": 3, "method": "shutdown", "params": {}})
    send({"jsonrpc": "2.0", "method": "exit", "params": {}})
    try:
        p.wait(timeout=15)
    except Exception:
        p.kill()

    if r is not None and "errors_before" in r:
        errs = r["errors_before"]
        print("FAILED: %d error%s before the extraction point (%s:%d:%d); fix the "
              "proof before extracting:"
              % (len(errs), "" if len(errs) == 1 else "s", a.file, a.line, a.col),
              file=sys.stderr)
        for d in errs[:20]:
            st = d["range"]["start"]
            msg = (d.get("message") or "").strip().splitlines()
            print("  %s:%d:%d: %s" % (a.file, st["line"] + 1, st["character"] + 1,
                                      msg[0] if msg else ""), file=sys.stderr)
        if len(errs) > 20:
            print("  ... and %d more" % (len(errs) - 20), file=sys.stderr)
        sys.exit(2)
    if not r or "result" not in r:
        print("FAILED:", json.dumps(r), file=sys.stderr)
        sys.exit(1)
    res = r["result"]
    print(json.dumps(res, indent=2))
    if not a.skip_annotations:
        gm = res.get("goal_module", "")
        proof_module = (gm[:-len("_goal")] + "_proof") if gm.endswith("_goal") \
            else a.name + "_proof"
        apply_with = res.get("apply_with", "eapply " + a.name + "_proof")
        hash_ = res.get("hash", "")
        outcome = annotate_source(f, a.line, a.name, proof_module, apply_with,
                                  hash_)
        msg = {
            "inserted": "annotated %s at line %d" % (a.file, a.line),
            "updated": "refreshed confirm_extraction hash in place in %s" % a.file,
            "unchanged": "confirm_extraction already up to date in %s" % a.file,
        }.get(outcome, "annotate: skipped (out of range) in %s" % a.file)
        print(msg, file=sys.stderr)


if __name__ == "__main__":
    main()
