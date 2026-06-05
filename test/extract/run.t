Extraction + the confirm_extraction staleness tripwire (via fcc / the server).

  $ export FCC_TEST=true

confirm_extraction: a correct recorded hash compiles with no staleness diagnostic:
  $ fcc --root proj proj/ok.v >/dev/null 2>&1
  $ grep -q STALE proj/ok.diags && echo STALE || echo clean
  clean

confirm_extraction: a wrong recorded hash is reported at the tactic site:
  $ fcc --root proj proj/stale.v >/dev/null 2>&1
  $ grep -o "STALE extraction (recorded hash deadbeef0000" proj/stale.diags
  STALE extraction (recorded hash deadbeef0000

confirm_extraction: a changed goal above (same recorded hash) is also caught:
  $ fcc --root proj proj/tamper.v >/dev/null 2>&1
  $ grep -o "STALE extraction" proj/tamper.diags
  STALE extraction

Extraction (drive the coq-lsp server) returns a stable hash + apply hint:
  $ python3 extract.py proj/m.v 8 3 tg --root proj --skip-annotations 2>/dev/null | grep -oE "\"(apply_with|hash)\": \"[^\"]*\""
  "apply_with": "eapply tg_proof"
  "hash": "d3d48680b6ac"

The generated goal and proof files both compile:
  $ ls proj/tg_goal.v proj/tg_proof.v
  proj/tg_goal.v
  proj/tg_proof.v
  $ coqc -R proj T proj/tg_goal.v 2>&1 && echo goal_ok
  goal_ok
  $ coqc -R proj T proj/tg_proof.v 2>&1 && echo proof_ok
  proof_ok

Cross-tool: the extracted hash, fed to confirm_extraction at the same goal, passes:
  $ H=$(python3 extract.py proj/m.v 8 3 tg --root proj --skip-annotations 2>/dev/null | python3 -c "import sys,json;print(json.load(sys.stdin)['hash'])")
  $ sed "s/__HASH__/$H/" proj/confirm_tpl.v > proj/confirm.v
  $ fcc --root proj proj/confirm.v >/dev/null 2>&1
  $ grep -q STALE proj/confirm.diags && echo STALE || echo crosstool_ok
  crosstool_ok

The section proof is reconstructed IN-SECTION (Section .. End around the lemma)
but does NOT duplicate the goal statement: it Requires the goal module (no Import,
to avoid clashing with the re-declared in-section helpers) and references the goal
applied to the section variables -- including Hn, which the statement never mentions
(the forcing [let] in the goal file pins the arity so this reference is well-typed):
  $ grep -c "^Section S\." proj/tg_proof.v
  1
  $ grep -c "^End S\." proj/tg_proof.v
  1
  $ grep -c "Definition tg_Goal" proj/tg_proof.v || true
  0
  $ grep -oE "^Require T\.tg_goal\." proj/tg_proof.v
  Require T.tg_goal.
  $ grep -oE "Lemma tg_proof : T\.tg_goal\.tg_Goal n Hn" proj/tg_proof.v
  Lemma tg_proof : T.tg_goal.tg_Goal n Hn
  $ grep -oE "let _force := \(n, Hn\) in" proj/tg_goal.v
  let _force := (n, Hn) in

Re-extraction is deterministic (identical hash across runs):
  $ H1=$(python3 extract.py proj/m.v 8 3 d1 --root proj --skip-annotations 2>/dev/null | python3 -c "import sys,json;print(json.load(sys.stdin)['hash'])")
  $ H2=$(python3 extract.py proj/m.v 8 3 d2 --root proj --skip-annotations 2>/dev/null | python3 -c "import sys,json;print(json.load(sys.stdin)['hash'])")
  $ [ "$H1" = "$H2" ] && echo deterministic
  deterministic

A non-section goal yields a proof that Requires the goal module, no Section:
  $ python3 extract.py proj/ns.v 4 3 nsx --root proj --skip-annotations >/dev/null 2>&1
  $ grep -c "^Section" proj/nsx_proof.v || true
  0
  $ grep -oE "Require Import [A-Za-z0-9_.]*nsx_goal" proj/nsx_proof.v
  Require Import T.nsx_goal
  $ coqc -R proj T proj/nsx_goal.v 2>&1 && coqc -R proj T proj/nsx_proof.v 2>&1 && echo ns_ok
  ns_ok

Annotation (the default; no --skip-annotations) wires hints into the source as comments:
  $ cp proj/m.v proj/ann.v && chmod +w proj/ann.v
  $ python3 extract.py proj/ann.v 8 3 ann --root proj >/dev/null 2>&1
  $ grep -c "coq-lsp extract: this goal is now ann_proof.v" proj/ann.v
  1
  $ grep -oE "Declare ML Module \"coq-lsp.confirm-extraction\"" proj/ann.v
  Declare ML Module "coq-lsp.confirm-extraction"
  $ grep -oE "confirm_extraction \"[0-9a-f]{12}\". eapply ann_proof; try eassumption." proj/ann.v
  confirm_extraction "d3d48680b6ac". eapply ann_proof; try eassumption.

The annotated source still compiles (the hints are comments):
  $ coqc -R proj T proj/ann.v 2>&1 && echo annotated_compiles
  annotated_compiles

Annotation is idempotent (re-running does not insert a second block):
  $ python3 extract.py proj/ann.v 8 3 ann --root proj >/dev/null 2>&1
  $ grep -c "coq-lsp extract: this goal is now" proj/ann.v
  1

--skip-annotations leaves the source byte-for-byte untouched:
  $ cp proj/m.v proj/noann.v && chmod +w proj/noann.v
  $ python3 extract.py proj/noann.v 8 3 na --root proj --skip-annotations >/dev/null 2>&1
  $ diff proj/noann.v proj/m.v && echo unchanged
  unchanged
