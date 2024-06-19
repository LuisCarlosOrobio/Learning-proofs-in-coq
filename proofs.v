Require Import Coq.Arith.Arith.

Theorem add_assoc : forall a b c : nat, a + (b + c) = (a + b) + c.
Proof.
intros a b c.
induction a as [| a' IHa'].
- reflexivity.
- simpl. rewrite -> IHa'. reflexivity.
Qed.

Theorem mult_comm : forall a b : nat, a * b = b * a.
Proof.
  intros a b.
  induction a as [| a' IHa'].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl. rewrite IHa'.
    rewrite Nat.mul_succ_r.
    rewrite Nat.add_comm.
    reflexivity.
Qed.
