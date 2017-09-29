theory Reihen
imports Complex_Main
begin 

lemma gauss :   "(\<Sum>i=0 .. (n::nat) . i) = n*(n+1) div 2" 
proof (induct n)
  case 0
  show ?case by simp 
 next 
  case (Suc n)
  assume "\<Sum>{0..n} = n * (n + 1) div 2"
  thus ?case by simp
qed


lemma "(\<Sum>i=0..(n::nat) . (2*i - 1)) = n^2" 
  using [[simp_trace_new mode=full]]
proof (induct n)
  case 0
  show ?case by simp
 next 
  fix n
  case (Suc n)
  assume a:"(\<Sum>i = 0..n. 2 * i - 1) = n\<^sup>2" 
  have " ((\<Sum>i = 0..Suc n. 2 * i - 1) = (Suc n)\<^sup>2) =  ( (2*n+1)  + (\<Sum>i = 0.. n. 2 * i - 1) = (Suc n)\<^sup>2)" by auto
  also have " \<dots> =  ( (2*n+1)  + (\<Sum>i = 0.. n. 2 * i - 1) = (n + 1)^2)"  by simp
  also have "\<dots> =  ( (2*n+1)  + (\<Sum>i = 0.. n. 2 * i - 1) = n^2 + 2*n + 1) " unfolding power2_sum by simp
  also from a have  " \<dots> =   ( (2*n+1)  + n^2 = n^2 + 2*n + 1)  " by auto
  finally show ?case by auto
qed



lemma fixes n::nat shows"(\<Sum>i = 1 .. n . i^2) = (n*(n + 1)*(2*n + 1)) div 6" 
proof (induct n)
  case 0
  show ?case by simp
 next 
  fix n::nat
  case (Suc n)
  assume hyp:"(\<Sum>i = 1..n. i\<^sup>2) = (n * (n + 1) * (2 * n + 1)) div 6"
 
  have "Suc n * (Suc n + 1) * (2 * Suc n + 1)   = (n + 1) * (n + 2) * (2 * n + 2 + 1) " by simp
  also have " \<dots> =  (n^2 +3*n + 2) * (2 * n + 2 +1)" by (simp add : power2_eq_square)
  also have "\<dots>  =  (n^2 +3*n + 2) * (2 * n + 3)"   
  proof -
    have tmp:"(2 * n + 2 +1) = (2 * n + 3)" by auto
    show ?thesis by (simp only: tmp )
  qed
  also have "\<dots> =   (n^2 +3*n + 2)*2*n +   (n^2 +3*n + 2)*3" by (simp only : ring_distribs)
  also have "\<dots> =  (n^2 +3*n + 2)*2*n +   3*n^2 +9*n + 6 " by (simp only : ring_distribs)
  also have "\<dots>  = 2*(n^2)*n +6*n^2 + 4*n  + 3*n^2 +9*n + 6" by (simp add : ring_distribs power2_eq_square)
  also have "\<dots> = 2*n^3 +9*n^2 + 13*n + 6 " by (simp add: power2_eq_square power3_eq_cube)
  finally have " (Suc n * (Suc n + 1) * (2 * Suc n + 1)) div 6 =  (2 * n ^ 3 + 9 * n\<^sup>2 + 13 * n + 6) div 6" by simp
  note tmpResult1 = this

  have "(\<Sum>i = 1..Suc n. i\<^sup>2) =   (\<Sum>i = 1 .. (n + 1).  i\<^sup>2)" by simp 
  also have "\<dots> = (n^2 + 2*n + 1)+ (\<Sum>i = 1 .. n.  i\<^sup>2)" by (simp add : power2_eq_square) 
  also have "\<dots> = (6*(n^2 + 2*n + 1) div 6) + (\<Sum>i = 1 .. n.  i\<^sup>2)" by auto
  also have "\<dots> = ((6*n^2 + 12*n + 6) div 6) + (\<Sum>i = 1 .. n.  i\<^sup>2)" by simp
  also have "\<dots> =  ((6*n^2 + 12*n + 6) div 6) + (n * (n + 1) * (2 * n + 1)) div 6 " unfolding hyp by simp
  also have "\<dots> = ((6*n^2 + 12*n + 6) + (n * (n + 1) * (2 * n + 1)))div 6 " by simp
  also have "\<dots> = ((6*n^2 + 12*n + 6) + ((n^2 + n)* (2 * n + 1))) div 6" by (simp add : power2_eq_square ring_distribs)
  also have "\<dots> = ((6*n^2 + 12*n + 6) + (2*n^3 + 3*n^2 + n)) div 6" by (simp add : power2_eq_square power3_eq_cube ring_distribs)
  also  have "\<dots> = (2*n^3 + 9*n^2 + 13*n + 6) div 6 " by simp
  note tmpResult2 =  calculation
  from tmpResult1 and tmpResult2 show ?case by simp
qed



theorem fixes n:: nat and p::nat and q::nat shows "\<Sum> i = 0 .. n . "   


lemma " suminf (\<lambda>n. c^n) = (1 / (1 - c))"
proof 
