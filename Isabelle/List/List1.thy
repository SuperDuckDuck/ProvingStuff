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


lemma "lst (ls @ [a]) = Some a" 
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix aa ls
  case (Cons aa ls)
  assume "lst (ls @ [a]) = Some a" 
  thus ?case by 

lemma "head xs = lst (rev xs)" 
proof (induct xs)
  case Nil
  show ?case by simp
 next 
  fix a xs x ls
  case (Cons a xs)
  assume "head xs = lst (rev xs)"

  show ?case 
  


