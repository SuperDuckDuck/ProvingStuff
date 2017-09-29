theory Arithmetic
imports Complex_Main 
begin 


(*
lemma dreiecksUngleichung : fixes x y::int shows "abs(x + y) \<le> abs x + abs y"  
proof -
  assume  "abs(x + y) \<le> abs x + abs y"  
  have "x^2 + 2*x*y + y^2 \<le> x^2 + 2*abs(x * y) + y^2" by auto
*)
lemma "" 
term "op choose"
lemma "\<not> (\<forall>\<alpha> k .  \<alpha> choose k   = (-1)^k  * ((k - \<alpha> - 1) choose k))" 
proof - 
  assume a:"\<exists>\<alpha> k. \<alpha> choose k   = (-1)^k  * ((k - \<alpha> - 1) choose k)"
  {
    assume "\<And> alpha. \<exists>k . alpha choose k = (-1)^k * ((k - alpha - 1) choose k)"
    {
      assume "\<And>alpha ka . alpha choose ka = (-1)^ka * ((ka - alpha - 1) choose ka)"
      hence "\<And>ka. 1 choose ka = (-1)^ka * ((ka - 1 - 1) choose ka)" by 
    }
      thm exE
      with b have False by (rule exE)
  
  
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
  