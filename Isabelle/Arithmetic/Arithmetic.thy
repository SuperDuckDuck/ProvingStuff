theory Arithmetic
imports Main 
begin 


(*
lemma dreiecksUngleichung : fixes x y::int shows "abs(x + y) \<le> abs x + abs y"  
proof -
  assume  "abs(x + y) \<le> abs x + abs y"  
  have "x^2 + 2*x*y + y^2 \<le> x^2 + 2*abs(x * y) + y^2" by auto
*)

lemma "vals = set ls \<Longrightarrow> length ls = card (set ls)  \<Longrightarrow>  \<Sum>vals =  sum_list ls" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume a:"vals = set ls \<Longrightarrow> length ls = card (set ls) \<Longrightarrow> \<Sum>vals = sum_list ls"
  assume b:"vals = set (a # ls)"
  assume c:"length (a # ls) = card (set (a # ls))"
  show ?case   
qed
  
  
lemma "(a::nat) + (b + c) = (a + b) + c" 
proof (induct a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  then show ?case 
qed
  