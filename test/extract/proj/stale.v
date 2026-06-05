Declare ML Module "coq-lsp.confirm-extraction".
Section S.
Variable n : nat.
Lemma t : n = n.
Proof.
  confirm_extraction "deadbeef0000".
  reflexivity.
Qed.
End S.
