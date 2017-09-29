Require Import Nat.
Require Import Setoid.


Theorem A1 {n : nat}: S n = 1 + n.
Proof.
  reflexivity.
Qed.


Theorem A2  {n : nat}: n + 1 =  1 + n.
Proof. 
  induction n.
  reflexivity.
  rewrite A1.
  rewrite <- IHn at 2.
  reflexivity.
Qed.