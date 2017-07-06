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

  lemma ""