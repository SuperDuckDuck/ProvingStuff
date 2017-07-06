theory Bool1 
  imports Main 
begin 
  
lemma "(P::bool) \<noteq> True \<Longrightarrow>P = False" 
proof (induct P)
  case True
  then show ?case by simp
next
  case False
  then show ?case by simp
qed

  
  
lemma "P = True \<or> P = False" 
proof (induct P)
  case True
  then show ?case by simp
next
  case False
  then show ?case by simp
qed
  
  

  