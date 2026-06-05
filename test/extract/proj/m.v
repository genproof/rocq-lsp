Section S.
Variable n : nat.
Hypothesis Hn : n = 5.
Lemma helper : forall k, k = n -> k + n = 10.
Proof. intros k Hk. subst k. rewrite Hn. reflexivity. Qed.
Lemma target : n + n = 10.
Proof.
  apply (helper n). reflexivity.
Qed.
End S.
