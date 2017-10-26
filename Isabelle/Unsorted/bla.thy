theory bla
  imports Main
begin 


definition bla :: "char \<Rightarrow> bool" where
"bla val = (nat_of_char val \<le> 90)"

declare bla_def [simp]

lemma "\<exists>x::char . bla x = True" 
proof - 
  {
    assume "\<not>(\<exists>x . bla x = True)"
    hence "\<forall>x . bla x \<noteq> True" by simp
    hence "bla CHR ''A'' \<noteq> True" by (rule allE)
    hence "False " by simp
  }
  thus ?thesis by auto
qed

lemma "\<exists>x::char . bla x " 
proof - 
  have "bla CHR ''Z''" by simp
  thus "\<exists>x. bla x " by (rule exI)
qed