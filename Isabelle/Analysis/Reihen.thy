theory Reihen
imports Main
begin 

lemma   "(\<Sum>i=0 .. (n::nat) . i) = n*(n+1) div 2"
proof (induct n)
  case 0
  show ?case by simp 
 next 
  case (Suc n)
  assume "\<Sum>{0..n} = n * (n + 1) div 2"
  thus ?case by simp
qed


lemma "(\<Sum>i=0..(n::nat) . (2*i - 1)) = n^2" 
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
  


lemma " suminf (\<lambda>n. c^n) = (1 / (1 - c))"
proof 
