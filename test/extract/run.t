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

Annotation (the default) replaces the goal's tactic with an active confirm_extraction
(which admits the goal) and inserts the explanatory block above it (asrc.v's [admit]
at line 6, goal [n = n]):
  $ cp proj/asrc.v proj/ann.v && chmod +w proj/ann.v
  $ python3 extract.py proj/ann.v 6 3 ann --root proj 2>/dev/null | grep -oE "\"hash\": \"[^\"]*\""
  "hash": "ac41d3f9e54e"
  $ grep -c "coq-lsp extract: this goal is now extracted to ann_proof.v" proj/ann.v
  1
  $ grep -oE "confirm_extraction \"ac41d3f9e54e\"\." proj/ann.v
  confirm_extraction "ac41d3f9e54e".
  $ grep -c "^  admit\." proj/ann.v || true
  0

The annotated source compiles: Declare ML Module is present and confirm_extraction
admits the goal (the enclosing proof is Admitted):
  $ coqc -R proj T proj/ann.v >/dev/null 2>&1 && echo annotated_compiles
  annotated_compiles

Re-extraction lands on the confirm_extraction line and refreshes the hash IN PLACE,
inserting no second block. Corrupt the hash, then re-extract at the confirm line (13):
  $ sed -i 's/ac41d3f9e54e/000000000000/g' proj/ann.v
  $ python3 extract.py proj/ann.v 13 3 ann --root proj >/dev/null 2>&1
  $ grep -c "coq-lsp extract: this goal is now" proj/ann.v
  1
  $ grep -oE "confirm_extraction \"ac41d3f9e54e\"" proj/ann.v
  confirm_extraction "ac41d3f9e54e"
  $ grep -c "000000000000" proj/ann.v || true
  0

--skip-annotations leaves the source byte-for-byte untouched:
  $ cp proj/asrc.v proj/noann.v && chmod +w proj/noann.v
  $ python3 extract.py proj/noann.v 6 3 na --root proj --skip-annotations >/dev/null 2>&1
  $ diff proj/noann.v proj/asrc.v && echo unchanged
  unchanged

A generated goal file never re-imports a sibling _goal/_proof module. cyc.v
imports T.cyc_goal; extracting with name cyc regenerates cyc_goal.v -- without the
collect_requires filter that line would be copied in, so cyc_goal.v would import
itself ("Cannot load a library with the same name as the current one"):
  $ chmod +w proj/cyc_goal.v
  $ coqc -R proj T proj/cyc_goal.v 2>&1
  $ python3 extract.py proj/cyc.v 4 3 cyc --root proj --skip-annotations >/dev/null 2>&1
  $ grep -c "cyc_goal" proj/cyc_goal.v || true
  0
  $ coqc -R proj T proj/cyc_goal.v 2>&1 && echo cyc_ok
  cyc_ok

But a DIFFERENT _goal module is kept (an extracted goal may reference it), while a
_proof module is always dropped. cross.v imports T.dep_goal and T.aux_proof;
extracting cr must keep dep_goal and drop aux_proof:
  $ coqc -R proj T proj/dep_goal.v 2>&1 && coqc -R proj T proj/aux_proof.v 2>&1
  $ python3 extract.py proj/cross.v 5 3 cr --root proj --skip-annotations >/dev/null 2>&1
  $ grep -oE "Require Import T\.dep_goal" proj/cr_goal.v
  Require Import T.dep_goal
  $ grep -c "aux_proof" proj/cr_goal.v || true
  0
  $ coqc -R proj T proj/cr_goal.v 2>&1 && echo cross_ok
  cross_ok

Re-extraction refreshes the first [intros] of an existing _proof.v to the new
binders, keeping the rest of the body. upd_v1 has hyps [a b Hab]; upd_v2 adds [c].
First extraction creates the skeleton (intros a b Hab):
  $ cp proj/upd_v1.v proj/upd.v && chmod +w proj/upd.v
  $ python3 extract.py proj/upd.v 4 3 upd --root proj --skip-annotations 2>/dev/null | grep -oE "\"(created_proof|updated_proof_intros)\": (true|false)"
  "created_proof": true
  "updated_proof_intros": false
  $ grep -oE "intros a b Hab" proj/upd_proof.v
  intros a b Hab
Simulate hand-written proof work in the body, then re-extract the changed goal:
  $ sed -i 's/Admitted\./idtac "KEEP_BODY". Admitted./' proj/upd_proof.v
  $ cp proj/upd_v2.v proj/upd.v
  $ python3 extract.py proj/upd.v 4 3 upd --root proj --skip-annotations 2>/dev/null | grep -oE "\"(created_proof|updated_proof_intros)\": (true|false)"
  "created_proof": false
  "updated_proof_intros": true
The first intros is updated to the new binders, and the body is preserved:
  $ grep -oE "intros a b c Hab" proj/upd_proof.v
  intros a b c Hab
  $ grep -c "KEEP_BODY" proj/upd_proof.v || true
  1
  $ coqc -R proj T proj/upd_goal.v >/dev/null 2>&1 && coqc -R proj T proj/upd_proof.v >/dev/null 2>&1 && echo upd_ok
  upd_ok

The autogenerated [intros] line carries a DON'T-EDIT marker:
  $ grep -oE "intros a b c Hab. \(\* DON'T EDIT THIS LINE -- AUTOGENERATED \*\)" proj/upd_proof.v
  intros a b c Hab. (* DON'T EDIT THIS LINE -- AUTOGENERATED *)

extract.py FAILS FAST (exit 2) when an error is reported before the extraction
point, rather than blocking on coq/extract's postponed reply (which on a big file
does not arrive until the whole document is checked). proj/err.v has a bad [apply
no_such_lemma] before the goal we ask to extract; extract.py watches diagnostics,
sees the upstream error and bails immediately, writing no goal file. (coq/extract
itself also returns an error -- a backstop for other clients.)
  $ python3 extract.py proj/err.v 4 3 eb --root proj --skip-annotations >/dev/null 2>&1
  [2]
  $ python3 extract.py proj/err.v 4 3 eb --root proj --skip-annotations 2>&1 | grep -o "error before the extraction point"
  error before the extraction point
  $ test -e proj/eb_goal.v && echo created || echo no_goal_file
  no_goal_file

A point with more than one foreground goal is refused (there is no unambiguous
"the goal" to extract). multi.v has two goals open after [split]; extracting at
the first [exact I.] (line 4, whose PREV state is the post-[split] two-goal state)
reports the count and writes no goal file:
  $ python3 extract.py proj/multi.v 4 3 mg --root proj --skip-annotations 2>&1 | grep -o "2 open goals at the point"
  2 open goals at the point
  $ test -e proj/mg_goal.v && echo created || echo no_goal_file
  no_goal_file

Shelved and given-up goals do NOT count: gu.v [admit]s the first subgoal, so at
the second [exact I.] (line 5) exactly one foreground goal remains and extraction
succeeds despite the given-up sibling:
  $ python3 extract.py proj/gu.v 5 3 gu --root proj --skip-annotations 2>/dev/null | grep -oE "\"regenerated_goal\": true"
  "regenerated_goal": true
