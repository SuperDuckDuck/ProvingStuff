theory List2
  imports Main 
begin 

lemma helper1 : "aa = a \<Longrightarrow> \<forall>i . (a # xs) ! i = (aa # ys) ! i \<Longrightarrow> \<forall>i . xs ! i  = ys ! i" 
proof - 
  assume h1:"aa = a" 
    and h2:"\<forall>i . (a # xs) ! i = (aa # ys) ! i"
  show "\<forall>i . xs ! i  = ys ! i"
  proof (rule ccontr)
    {
      assume tmp:"\<exists>i . xs ! i \<noteq> ys ! i"
      {
        fix n
        assume h3:"xs ! n \<noteq> ys ! n"
          
        from h2 have "(a # xs) ! (Suc n) =  (aa # ys) ! (Suc n)" by (rule allE)
        hence "xs ! n = ys ! n" by simp
        with h3 have False by simp
      }
      with tmp have False by (rule exE)
    }
    thus "\<not> (\<forall>i. xs ! i = ys ! i) \<Longrightarrow> False " by simp
  qed
qed
   
    
lemma helper2 : "length xs = length ys \<Longrightarrow> (\<forall>i . xs ! i = ys ! i)  \<Longrightarrow> xs = ys " 
proof -
  assume h1:"length xs = length ys"
    and h2:"\<forall>i . xs ! i = ys ! i"
  then show "xs = ys"
  proof (induction xs arbitrary : ys)
    case Nil
    assume "length [] = length ys"
    then show ?case by (cases ys; simp)
  next
    case (Cons a xs)
    assume hyp1:"\<And>ys . length xs = length ys \<Longrightarrow> \<forall>i. xs ! i = ys ! i \<Longrightarrow> xs = ys"
      and hyp2:"\<forall>i. (a # xs) ! i = ys ! i"
      and hyp3:"length (a # xs) = length ys"
    from hyp2 and hyp3 show ?case 
    proof (induction ys)
      case Nil
      then show ?case by simp
    next
      case (Cons aa ys)
      assume ha1:"\<forall>i. (a # xs) ! i = ys ! i \<Longrightarrow> length (a # xs) = length ys \<Longrightarrow> a # xs = ys"
        and ha2:" \<forall>i. (a # xs) ! i = (aa # ys) ! i"
        and ha3:"length (a # xs) = length (aa # ys)"
      then show ?case 
      proof (cases "aa = a")
        case True
        assume c1:"aa =a"
        from c1 and ha2 have "\<forall>i . xs ! i = ys ! i" by (rule helper1)
        with c1 and hyp1[of ys] ha3 show ?thesis by simp
      next
        case False
        assume c2:"aa \<noteq> a"
        have False using ha2 c2 by (metis nth_Cons_0)
        then show ?thesis by simp
      qed
    qed
  qed
qed
 
lemma helper3 : "ls = take (length ls div 2) ls @ drop (length ls div 2) ls"   
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"ls = take (length ls div 2) ls @ drop (length ls div 2) ls"
  show ?case 
  proof (cases ls)
    case Nil
    then show ?thesis by simp
  next
    case (Cons aa list)
    then show ?thesis by simp 
  qed
qed  
  
fun tailRev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "tailRev [] res = res"|
  "tailRev (x#xs) res = tailRev xs (x#res)"
        
lemma lem1: "tailRev xs ys = rev xs @ ys" 
proof (induct xs arbitrary : ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed
  
theorem "tailRev xs [] = rev xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "tailRev (a # xs) [] = rev xs  @ [a]" using lem1[of xs "[a]"] by simp    
  thus  ?case by simp
qed
  
primrec reverse_core :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverse_core [] res = res"|
  "reverse_core (x#xs) res = reverse_core xs (x#res)"
    
definition "reverse ls = reverse_core ls []"
  declare reverse_def [simp]
lemma "reverse xs @ ys = reverse_core xs ys " 
proof (induction xs arbitrary : ys )
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"\<And>ys .reverse xs @ ys = reverse_core xs ys"
  have "reverse (a#xs) @ ys = reverse_core xs [a] @ ys " by simp
  also have "\<dots> = reverse xs @ [a] @ ys" using hyp[of "[a]"] by simp
  also have "\<dots> = reverse xs @ (a # ys)" by simp
  also have "\<dots> = reverse_core xs (a#ys)" using hyp by simp
  also have "\<dots> = reverse_core (a#xs) ys" by simp
  finally show ?case by simp
qed

lemma helper : "\<forall>ys . reverse xs @ ys = reverse_core xs ys " 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"\<forall>ys. reverse xs @ ys = reverse_core xs ys"
  {
    fix ys
    have tmp1: "reverse xs @ [a] = reverse_core xs [a]" using hyp by simp
    have "( reverse (a # xs) @ ys) = reverse_core xs [a] @ ys " by simp
    also have "\<dots> = reverse xs @ [a] @ ys" using tmp1 by simp
    also have "\<dots> = reverse xs @ (a # ys)" by simp
    also have "\<dots> = reverse_core xs (a#ys)" using hyp by simp
    also have "\<dots> = reverse_core (a#xs) ys" by simp
    finally have "reverse (a # xs) @ ys = reverse_core (a#xs) ys" by assumption
  }
  then show ?case by simp
qed
  
  