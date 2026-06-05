Lemma triv : forall a : nat, a = a /\ a = a.
Proof.
  intros a.
  split; reflexivity.
Qed.
