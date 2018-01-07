Require Import Classical.

Parameter R : Set.
Parameter Rplus: R->R->R.

Definition isZero(z : R) := forall x : R, Rplus x z = x.

Axiom zero_exists : exists z : R, isZero z.

Axiom plus_comm: forall x y : R, Rplus x y = Rplus y x.

Theorem unique_zero: forall z1 z2 : R, isZero z1 /\ isZero z2 -> z1 = z2.
intros.
unfold isZero in H.
destruct H as [H1 H2].
pose (a:= H2 z1).
rewrite <- a.
pose (b:= H1 z2).
pose (b':=plus_comm z2 z1).
rewrite <- b at 2.
rewrite b'.
reflexivity.
Qed.





