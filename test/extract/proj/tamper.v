Declare ML Module "coq-lsp.confirm-extraction".
Section S.
Variable n : nat.
(* same hash as ok.v but the goal changed: n + 0 = n + 0 *)
Lemma t : n + 0 = n + 0.
Proof.
  confirm_extraction "ac41d3f9e54e".
Admitted.
End S.
