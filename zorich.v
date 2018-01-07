Require Import Classical.

Parameter R : Set.
Parameter Rplus: R->R->R.
Parameter Rmult: R->R->R.
Parameter isZero: R->Prop.
Parameter isNeg: R->R->Prop.

Axiom zeroPlusProp: forall x z : R, isZero z -> Rplus x z = x.
Axiom negPlusProp: forall x n : R, isNeg x n -> isZero(Rplus x n).

Axiom zero_exists : exists z : R, isZero z.
Axiom neg_exists : forall x:R, exists n:R, isNeg x n.
Axiom plus_assoc: forall x y z : R, Rplus x (Rplus y z) = Rplus (Rplus x y) z.
Axiom plus_comm: forall x y : R, Rplus x y = Rplus y x.

Theorem unique_zero: forall z1 z2 : R, isZero z1 /\ isZero z2 -> z1 = z2.
intros.
destruct H.
pose (a:=zeroPlusProp z1 z2 H0).
rewrite <- a.
pose (b:=plus_comm z1 z2).
rewrite b.
pose (c:=zeroPlusProp z2 z1 H).
assumption.
Qed.





