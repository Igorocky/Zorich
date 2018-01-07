Require Import Classical.
Set Implicit Arguments.

Definition nonEmpty(A: Set)(p: A->Prop) := exists a : A, p a.
Parameter R : Set.
Parameter Rplus: R->R->R.
Infix "+" := Rplus.
Parameter Rmult: R->R->R.
Infix "*" := Rmult.
Parameter isZero: R->Prop.
Parameter isOne: R->Prop.
Parameter isNeg: R->R->Prop.
Parameter isInv: R->R->Prop.
Parameter le: R->R->Prop.
Infix "<=" := le.

Axiom zeroPlusProp: forall x z : R, isZero z -> x + z = x.
Axiom negPlusProp: forall x n : R, isNeg x n -> isZero (x + n).
Axiom oneNeqZero: forall o z : R, isOne o /\ isZero z -> o <> z.
Axiom oneMultProp: forall x o : R, isOne o -> Rmult x o = x.
Axiom invMultProp: forall x i : R, isInv x i -> isOne(x*i).

Axiom zero_exists : exists z : R, isZero z.
Axiom neg_exists : forall x:R, exists n:R, isNeg x n.
Axiom plus_assoc: forall x y z : R, x + (y + z) = (x + y) + z.
Axiom plus_comm: forall x y : R, x + y = y + x.

Axiom one_exists : exists o : R, isOne o.
Axiom inv_exists : forall x: R, ~ isZero x -> exists i:R, isInv x i.
Axiom mult_assoc: forall x y z : R, x*(y*z) = (x*y)*z.
Axiom mult_comm: forall x y : R, x*y = y*x.

(*Axiom addMultConnection: forall x y z : R, 
                        Rmult (Rplus x y) z = Rplus (Rmult x z) (Rmult y z).*)
Axiom addMultConnection: forall x y z : R, (x + y)*z = x*z + y*z.

Axiom order0: forall x:R, x <= x.
Axiom order1: forall x y:R, x <= y /\ y <= x -> x = y.
Axiom order2: forall x y z:R, x <= y /\ y <= z -> x <= z.
Axiom order3: forall x y:R, x <= y \/ y <= x.

Axiom addOrderConnection: forall x y z : R, 
                        x <= y -> x+z <= y+z.

Axiom multOrderConnection: forall x y z : R, 
                             isZero z /\ z <= x /\ z <= y -> z <= x*y.

Axiom completeness: forall (X Y : R->Prop) (x y : R), 
                       nonEmpty X /\ nonEmpty Y /\ 
                       (X x /\ Y y -> x <= y) -> exists c:R, x <= c /\ c <= y.

Theorem unique_zero: forall z1 z2 : R, isZero z1 /\ isZero z2 -> z1 = z2.
intros.
destruct H.
pose (a:=zeroPlusProp z1 H0).
rewrite <- a.
pose (b:=plus_comm z1 z2).
rewrite b.
pose (c:=zeroPlusProp z2 H).
assumption.
Qed.

Theorem unique_neg: forall x n1 n2 : R, isNeg x n1 /\ isNeg x n2 -> n1 = n2.
intros.
destruct H.
pose (a:= negPlusProp H).
pose (b := zeroPlusProp n2 a).
rewrite (plus_assoc) in b.
pose (c:=negPlusProp H0).
rewrite plus_comm in c.
pose (d:=zeroPlusProp n1 c).
rewrite plus_comm in d.
rewrite b in d.
rewrite d.
reflexivity.
Qed.