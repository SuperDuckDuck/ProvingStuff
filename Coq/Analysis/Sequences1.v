Require Import Rfunctions.
Require Import Nat.
Require Import Setoid.
Require Import ArithRing.
Require Import Omega.




Open Scope nat_scope.
Open Scope R_scope.
Search (_ / _  + _).
Check Nat.div_add.
(*c <> 0%nat -> (a + b * c) / c = a / c + b*)


Lemma Gauss {n : nat}: sum_nat_O n = n * (n + 1) / 2 .
Proof.
  induction n.
  reflexivity.
  unfold sum_nat_O at 1.
  simpl sum_nat_f_O.
  unfold sum_nat_O in IHn.
  rewrite IHn.
  rewrite <- Nat.div_add.
  f_equal.
  ring.
  intro.
  discriminate.
Qed.
