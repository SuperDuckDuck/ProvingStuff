theory List1 
imports Main 
begin 


primrec head :: "'a list \<Rightarrow> 'a option" where 
"head [] = None"|
"head (x#xs) = Some x"

fun lst :: "'a list \<Rightarrow> 'a option " where 
"lst [] = None"|
"lst [x] = Some x"|
"lst (x#xs) = lst xs"

lemma "head [] = None" by simp 


lemma tmp : "lst (ls @ [a]) = Some a" 
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix aa ls
  case (Cons aa ls)
  assume a:"lst (ls @ [a]) = Some a" 
  show ?case 
  proof (cases ls)
    case Nil
    with a show ?thesis by simp
  next
    case (Cons a list)
    with a  show ?thesis by simp
  qed
qed
  

lemma "head xs = lst (rev xs)" 
proof (induct xs)
  case Nil
  show ?case by simp
 next 
  case (Cons a xs)
  assume "head xs = lst (rev xs)"
  thus ?case by (simp add : tmp)
qed
  

lemma "length xs > 0 \<Longrightarrow> length xs > length (tl xs)" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case by simp
qed

section {*proof that rev is injective (long version) [rev;injective;long]*}
  

lemma helper1 :  "Suc n < Suc (Suc n)" 
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

  
lemma helper2 : fixes n::nat shows "m < n \<Longrightarrow> m < Suc n" 
proof (induct m arbitrary : n)
  case 0
  then show ?case
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume hyp1:"0 < Suc n" 
    have a:"Suc n < Suc (Suc n)" by (rule helper1)
    with hyp1 show ?case by (rule less_trans)
  qed
next
  case (Suc m)
  assume hyp1:"\<And>n . m < n \<Longrightarrow> m < Suc n"
  assume "Suc m < n"
  then show ?case 
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume hyp2:"Suc m < n \<Longrightarrow> Suc m < Suc n"
       and hyp3:"Suc m < Suc n"
    have "m < n \<Longrightarrow> m < Suc n" by (rule hyp1)
    with hyp2 and hyp3 show ?case by simp
  qed
qed
 
lemma helper3 : fixes n::nat shows "0 < n \<Longrightarrow> 0 < Suc n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume "0 < Suc n"
  then show ?case by (rule helper2) 
qed
  
lemma helper4 : fixes a::nat shows " a \<noteq> b \<Longrightarrow> a < b \<or> b < a "
proof -
  assume hyp:"a \<noteq> b"
  {
    assume hyp2:"a \<ge> b \<and>   b \<ge> a"
    hence a:"a \<ge> b" by simp
    from hyp2 have "b \<ge> a" by simp
    from a and this have  "a = b" by (rule HOL.no_atp(10))
    with hyp have False by contradiction
  }
  thus "a < b \<or> b < a " by fastforce
qed
  
lemma helper5 : fixes m::nat shows " m < n \<Longrightarrow> m \<noteq> n" by simp

lemma helper6 : fixes n::nat shows "0 \<noteq> n \<Longrightarrow> 0 < n" 
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume "0 \<noteq> n \<Longrightarrow> 0 < n"
  assume hyp:"0 \<noteq> Suc n"
  thus "0 < Suc n" 
  proof -
    from hyp have a:"0 < Suc n \<or> Suc n < 0" by (rule helper4)
    {
      assume "0 < Suc n"
    }
    note tmp=this
    {
      assume "Suc n < 0"
      hence False by simp
      hence "0 < Suc n" by simp
    }
    with a and tmp show ?case by simp
  qed
qed
      
lemma helper7 : fixes n::nat shows "(0 \<noteq> n) \<Longrightarrow> (0 \<noteq> Suc n)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume hyp:"0 \<noteq> Suc n"
  then have a:"0 < Suc n" by (rule helper6)
  then have "0 < Suc (Suc n)" by (rule helper3)
  then show ?case by (rule helper5)
qed
 
lemma fixes n::nat shows "0 \<noteq> Suc n" 
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (rule helper7)
qed 
  
lemma "\<forall>xs ys . rev xs = rev ys \<longrightarrow> xs = ys"
proof (rule allI, rule allI)
  fix xs ys::"'a list"
  show "rev xs = rev ys \<longrightarrow> xs = ys"
  proof (rule impI, induct xs; induct ys)
    case Nil
    show ?case by (rule refl)
  next
    case (Cons a ys)
    assume hyp:"rev ([]::'a list) = rev (a # ys ::'a list)"
    have False 
    proof -
      {
        have a:"length (rev []::'a list) = length (rev (a # ys))" by (subst hyp, rule refl)
        hence "0 = 1 + length (rev ys)" by auto
            hence False by (rule )
            
      }
    then show ?case 
  qed
    
    
    
lemma "\<forall>xs ys . rev xs = rev ys \<longrightarrow> xs = ys"
proof (rule allI, rule allI)
  fix xs ys::"'a list"
  show "rev xs = rev ys \<longrightarrow> xs = ys"
  proof (induct xs ys rule : list_induct2')
    case 1
    then show ?case by simp
  next
    case (2 x xs)
    then show ?case sorry
  next
    case (3 y ys)
    then show ?case sorry
  next
    case (4 x xs y ys)
    then show ?case sorry
  qed
    
    
  
end 
  
  