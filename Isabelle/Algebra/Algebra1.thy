theory Algebra1 
imports Main 
begin 


lemma "( (n::nat) +1 )^2 = n^2  + 2*n + 1^2" 
proof -
  show ?thesis by (simp only : power2_sum) 
qed 

lemma "( Suc(n::nat)  )^2 = n^2  + 2*n + 1^2" 
proof -
  have "( Suc(n::nat)  )^2 = ((n::nat)+1  )^2" by auto
  also have "\<dots> = n^2  + 2*n + 1^2" unfolding power2_sum by auto
  finally show ?thesis by auto 
qed 

