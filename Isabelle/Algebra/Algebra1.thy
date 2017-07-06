theory Algebra1 
imports Complex
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


lemma fixes a b::nat shows  "(a + b)^2 = a^2 + b^2 + 2*a*b" 
proof - 
  have  "(a + b)^2 = (a + b)* (a + b)  "  by (simp add : power2_eq_square)
  also have "\<dots> = (a + b)*a + (a + b)*b" by    (simp add : ring_distribs)
  also have "\<dots> =  a*a + b*a + a*b+ b*b" by (simp add :ring_distribs)
  also have "\<dots> = a^2 + b*a + a*b +  b^2" by  (simp add :power2_eq_square)
  finally show ?thesis by auto
qed

