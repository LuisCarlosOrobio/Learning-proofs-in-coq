Theorem add_assoc : forall a b c : nat, a + (b + c) = (a + b) + c.
Proof.
intros a b c.
induction a as [| a' IHa'].
- reflexivity.
- simpl. rewrite -> IHa'. reflexivity.
Qed.
