Require Import Le.

Inductive List (A : Type) := 
  |Nil : List A
  |Cons : A -> List A -> List A.

Arguments Nil [A].
Arguments Cons [A] _ _.

Notation "[ ]" := Nil.
Notation "[ x ]" := (Cons x Nil).
Notation "[ x ; .. ; y ]"  := (Cons x .. (Cons y Nil) ..).

Check [].
Check [1].
Check [1;2;3;4].



Fixpoint length {A : Type}(ls : List A): nat := 
  match ls with 
  |Nil => 0
  |Cons a rest => 1 + length rest
end.

Eval compute in (length [1;2;3;4;5]).

Lemma LS1 {A : Type}(ls : List A) : 0 < length ls ->  [] <> ls.
Proof.
  induction ls.
  intro.
  simpl in H.
  unfold lt in H.
  apply le_n_0_eq in H.
  discriminate.
  intro.
  intro.
  discriminate.
Qed.

Fixpoint head {A : Type}(ls : List A)(default : A): A := 
  match ls with 
  |Nil => default
  |Cons val next  => val
end.
