Declare ML Module "coq-lsp.confirm-extraction".
Section S.
Variable n : nat.
Lemma t : n = n.
Proof.
  confirm_extraction "ac41d3f9e54e".
  reflexivity.
Qed.
End S.
