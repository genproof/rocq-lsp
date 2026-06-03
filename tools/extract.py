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
import json, subprocess, os, sys, argparse

# The coq-lsp server to drive. Defaults to the `coq-lsp` on PATH (e.g. an
# opam-installed one, which has `coq/extract` once this branch is installed).
# Override with COQLSP=/path/to/coq_lsp.exe to use an in-tree _build binary.
SRV = os.environ.get("COQLSP", "coq-lsp")


def annotate_source(path, line_1, name, proof_module, apply_with):
    """Insert commented Require + delegation hints into the source file, right
    above the extraction line, so it is obvious how to wire in the lemma.
    Comments only -- compiles unchanged. Returns False if skipped."""
    lines = open(path).read().split("\n")
    idx = line_1 - 1
    if not (0 <= idx < len(lines)):
        return False
    # Skip if a hint block is already here (re-run lands on the inserted block,
    # which has shifted the original line down).
    if any("coq-lsp extract" in l for l in lines[max(0, idx - 1):idx + 5]):
        return False
    src = lines[idx]
    indent = src[: len(src) - len(src.lstrip())]
    block = [
        f"{indent}(* --- coq-lsp extract: this goal is now {name}_proof.v --- *)",
        f"{indent}(* 1. add near the top of this file:  Require Import {proof_module}. *)",
        f"{indent}(* 2. replace the tactic block below with: *)",
        f"{indent}(* {apply_with}; try eassumption. *)",
    ]
    lines[idx:idx] = block
    open(path, "w").write("\n".join(lines))
    return True


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

    def wait(i):
        while True:
            m = readmsg()
            if m is None:
                return None
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
    send({"jsonrpc": "2.0", "id": 2, "method": "coq/extract",
          "params": {"textDocument": {"uri": uri},
                     "position": {"line": a.line - 1, "character": a.col - 1},
                     "name": a.name}})
    r = wait(2)
    send({"jsonrpc": "2.0", "id": 3, "method": "shutdown", "params": {}})
    send({"jsonrpc": "2.0", "method": "exit", "params": {}})
    try:
        p.wait(timeout=15)
    except Exception:
        p.kill()

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
        if annotate_source(f, a.line, a.name, proof_module, apply_with):
            print("annotated %s at line %d" % (a.file, a.line), file=sys.stderr)
        else:
            print("annotate: skipped (out of range or already annotated)",
                  file=sys.stderr)


if __name__ == "__main__":
    main()
