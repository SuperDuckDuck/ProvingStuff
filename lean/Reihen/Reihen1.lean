open list
open nat

notation Σ a := sum (range a)

lemma helper1 {n : nat}: n + 1 = succ n := by simp

lemma helper {n : nat}: (Σ )

lemma Gauss {n : nat} : (Σ n) = n*(n + 1) / 2 :=
nat.rec_on n
  (show (Σ 0) = 0 * (0 + 1) / 2 , from rfl)
  (
   assume hyp:(Σ n) = n*(n + 1) / 2, 
   show (Σ (succ n)) = ((succ n) * (succ n  + 1  ))/ 2, from calc
     (Σ (succ n)) = (succ n) + (Σ n) : by simp
     ... = (succ n) + n*(n + 1) / 2 : by simp[hyp]
     ... = (n + 1) + n*(n + 1) / 2 : by simp[helper1]
     ... = (n + 1) + (n*n + n)/2 : by simp
     ... = (2*n + 2)/2 + (n*n + n)/2 : by simp
     ... = (2*n + 2)/2 + (n*n + n)/2 : by simp
     ... = (2*n + 2 + n*n + n)/2 : by simp
     ... = 
     
  )
  
