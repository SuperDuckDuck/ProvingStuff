theory Tree1 
  imports Main 
begin 
  
  
  
datatype 'a Tree  = Leaf 'a | Branch 'a "'a Tree" "'a Tree"
  
  
primrec cont :: "'a Tree \<Rightarrow> 'a list" where 
  "cont (Leaf val) = [val]"|
  "cont (Branch val lft rgt) =  val # cont lft @ cont rgt"
  
  
  
primrec sumT :: "int Tree \<Rightarrow> int" where 
  "sumT (Leaf val) = val"|
  "sumT (Branch val lft rgt) = val + sumT lft + sumT rgt"
  

definition sumL :: "int list \<Rightarrow> int" where 
  "sumL ls = foldl (op +) 0 ls"
(*
lemma helper1 : "val + vals = foldl (\<lambda> x y . x + y) 0  (val # ls) \<Longrightarrow> vals = foldl (\<lambda>x y . x + y) 0 ls" 
proof -
  *)
lemma helper1_helper1_helper1_helper1 : fixes n::int shows "foldr op + (a#ls) n = foldr op + (ls @ [a]) n" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  assume a:"foldr op + (a # ls) n = foldr op + (ls @ [a]) n"
  then show ?case by simp
qed
  
  
lemma helper1_helper1_helper1 : fixes n::int shows "foldr op + (rev ls) n = foldr op + ls n"   
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"foldr op + (rev ls) n = foldr op + ls n"
  have "foldr op + (a # ls) n = a + foldr op + ls n" by simp
  also have "\<dots> = a + foldr op + (rev ls) n " using hyp by simp
  also have "\<dots> =  foldr op + (a # rev ls) n" by simp
  also have "\<dots> = foldr op + (rev ls @ [a]) n" using helper1_helper1_helper1_helper1 by simp
  finally show ?case by simp
qed
  

lemma helper1_helper1_helper2 : fixes n::int shows "foldr (\<lambda>x y . x + y) ls n = foldr (\<lambda> x y. y + x) ls n" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"foldr op + ls n = foldr (\<lambda>x y. y + x) ls n"
  then show ?case by simp
qed  

lemma helper1_helper1 : fixes n::int shows "foldl (op +) n ls = foldr (op +) ls n"  
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"foldl op + n ls = foldr op + ls n"
  have "foldl op + n (a#ls) = foldr (\<lambda> x y . y + x) (rev (a#ls)) n" by (simp add :foldl_conv_foldr)
  also have "\<dots> = foldr (op +) (rev (a#ls)) n" by (simp only : helper1_helper1_helper2)
  also have "\<dots> = foldr (op +) (a#ls) n" by (simp only : helper1_helper1_helper1)
  finally show ?case by simp
qed  
  
  
lemma helper1_helper2 : fixes n::int shows "a + foldl op + n ls = foldl op + n (a # ls)" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  assume hyp:"a + foldl op + n ls = foldl op + n (a # ls)"
  have "a + foldl op + n (aa#ls) = a + foldr op + (aa#ls) n" by (simp only : helper1_helper1)
  also have "\<dots> = foldr op + (a # aa # ls) n" by simp
  also have "\<dots> = foldl op + n (a # aa # ls)" by (simp only : helper1_helper1 )
  finally show ?case using helper1_helper1 by simp
qed
  
(*  
lemma helper1 : "foldl op + n ls = n + sumL ls" 
proof (induct ls)
  case Nil
  then show ?case by (simp add : sumL_def)
next
  case (Cons a ls)
  assume hyp:"foldl op + n ls = n + sumL ls"
  have "foldl op + n (a # ls) = foldr op + (a # ls) n" by (simp only : helper1_helper1)
  also have "\<dots> = a + foldr op + ls n" by simp
  also have "\<dots> = a + foldl op + n ls" by (simp only : helper1_helper1)
  also have "\<dots> = a + n + sumL ls" using hyp by simp
  also have "\<dots> = n + sumL (a # ls)" using helper1_helper2 by (simp add : sumL_def)
  finally show ?case by simp        
qed
  *)

  
  
lemma helper1_helper3 : fixes n::int shows "foldr op + (ls @ xs) n = foldr op + ls 0 + foldr op + xs n" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"foldr op + (ls @ xs) n = foldr op + ls 0 + foldr op + xs n"
  then show ?case by simp
qed 
  
  
lemma helper1 : fixes n::int shows "foldl op + n (ls @ xs) = foldl op + 0 ls + foldl op + n xs" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"foldl op + n (ls @ xs) = foldl op + 0 ls + foldl op + n xs"
  then show "foldl op + n ((a # ls) @ xs) = foldl op + 0 (a # ls) + foldl op + n xs" using helper1_helper3 helper1_helper1 by presburger 
qed
  

lemma  fixes tr::"int Tree" shows "sumT tr  = sumL (cont tr)" 
proof (induct tr)
  case (Leaf x)
  then show ?case by (simp add : sumL_def)
next
  case (Branch x1a tr1 tr2)
  assume a:"sumT tr1 = sumL (cont tr1)"
  assume b:"sumT tr2 = sumL (cont tr2)"
  have "sumT (Branch x1a tr1 tr2) = x1a + sumT tr1 + sumT tr2" by simp
  also have "\<dots> = x1a + sumL (cont tr1) + sumL (cont tr2)" using a and b by simp
  also have "\<dots> = x1a + foldl op + 0 (cont tr1) + foldl op + 0 (cont tr2)" by (simp add : sumL_def)
  also have "\<dots> = x1a + foldl op + 0 (cont tr1 @ cont tr2)" by (simp only : helper1)
  also have "\<dots> = foldl op + 0 (x1a # cont tr1 @ cont tr2)" by (simp only : helper1_helper2)
  finally show ?case by (simp add : sumL_def) 
qed
  