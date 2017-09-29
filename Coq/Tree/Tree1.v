Require Import Le.
Require Import List.
Import ListNotations.
Open Scope list_scope.


Inductive Tree (A : Type):= 
  |Leaf: A -> Tree A
  |Branch: A -> Tree A -> Tree A -> Tree A.

Arguments Leaf [A] _.
Arguments Branch [A] _ _ _.

Fixpoint cont {A : Type} (tree : Tree A) : list A :=
  match tree with 
  |Leaf val => [val]
  |(Branch val l r) => val:: cont l ++ cont r
end.

Fixpoint sumT (tree : Tree nat) : nat :=
  match tree with
  |Leaf val => val
  |Branch val l r => val + sumT l + sumT r
end.

Definition sumL (ls : list nat): nat := fold_left (fun result curr => result + curr) ls 0.

Theorem A1 (tr : Tree nat)(ls : list nat): sumT tr = sumL ls.
Proof. 
  


