theory ModifyStringToCharTuples
  imports Main 
begin 


definition isAlpha :: "char \<Rightarrow> bool" where 
"isAlpha chr = (let val = nat_of_char chr  in  (65  \<le>  val \<and> val \<le> 90 ) \<or> (97 \<le> val \<and> val \<le> 122))"

declare isAlpha_def [simp]

lemma isAlphaTest1 : "isAlpha CHR ''a''" by simp

lemma isAlphaTest2 : "isAlpha CHR ''A''" by simp

lemma isAlphaTest3 : "isAlpha CHR ''z''" by simp

lemma isAlphaTest4 : "isAlpha CHR ''Z''" by simp

(*simple snaity proof*)
theorem "(\<exists>x . isAlpha x = False) \<and> (\<exists>x. isAlpha x = True)" 
proof -
  have "isAlpha CHR ''}''= False" by simp
  hence tmp:"\<exists>x . isAlpha x = False" by (rule exI)

  have "isAlpha CHR ''a''= True" by simp
  hence "\<exists>x . isAlpha x = True" by (rule exI)

  with  tmp show ?thesis by (rule conjI)
qed

definition "allLetterNats = set ([ nat_of_char CHR ''a'' ..< nat_of_char CHR ''z'' + 1] @ [nat_of_char CHR ''A'' ..< nat_of_char CHR ''Z'' + 1])" 

definition "allNotLetterNats = set (map (nat_of_char) (Enum.enum :: char list)) - allLetterNats"

declare allLetterNats_def [simp]

declare allNotLetterNats_def [simp]

lemma helper1:"x \<in> set [n ..< m] \<Longrightarrow> n \<le>  x  \<and>  x < m " by simp

lemma helper2:"x \<in> set ([n ..<m] @ [a ..<b]) \<Longrightarrow> (n \<le> x \<and> x < m) \<or> (a \<le> x \<and> x < b)" by simp

theorem "nat_of_char x \<in> allLetterNats \<Longrightarrow> isAlpha x" by auto

lemma "nat_of_char (x :: char) < 256" by simp 

lemma helper3:"x \<in> allNotLetterNats \<Longrightarrow> x < 65 \<or> (90 < x \<and> x < 97) \<or> 122 < x"  (*takes some time to compute*) by (auto ; arith)

lemma helper3'':"x \<in> allNotLetterNats \<Longrightarrow> x < 256" by auto

lemma helper3':" noc \<in>  allNotLetterNats \<Longrightarrow> (noc < 65 \<or> (90 < noc \<and> noc < 97) \<or> 122 < noc) \<and> noc < 256" using helper3 helper3'' by simp

lemma helper4:"noc = nat_of_char x \<Longrightarrow> \<not>isAlpha x = (noc < 65 \<or> (90 < noc \<and> noc < 97) \<or> 122 < noc) " by (auto simp add : Let_def )

theorem "nat_of_char x \<in> allNotLetterNats \<Longrightarrow> isAlpha x = False" 
proof -
  let ?noc="nat_of_char x"
  assume hyp:"nat_of_char x \<in> allNotLetterNats"
  hence "(?noc < 65 \<or> (90 < ?noc \<and> ?noc < 97) \<or> 122 < ?noc) " by (rule helper3)
  thus ?thesis using helper4 by simp
qed

primrec transform :: "string \<Rightarrow> string" where 
"transform [] = []"|
"transform (x#xs) = ''bla''"