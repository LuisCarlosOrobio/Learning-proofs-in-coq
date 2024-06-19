Theorem mul_add_distr_l : forall a b c : nat, a * (b + c) = (a * b) + (a * c).
Proof.
  (* Introduce the variables a, b, and c *)
  intros a b c.
  (* Induction on a *)
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

Theorem add_assoc : forall a b c : nat, (a + b) + c = a + (b + c).
Proof.
  (* Introduce the variables a, b, and c *)
  intros a b c.
  (* Induction on a *)
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.
