theory ExcludedMiddle
imports Main 
begin 

lemma "\<not>P \<or> P" 
proof -
{ 
  assume a:"\<not>(\<not>P \<or> P)"
  {
    assume P 
    hence "\<not>P \<or> P" ..
    with a have False ..
  }
  hence "\<not>P" ..
  hence "\<not>P \<or> P" ..
  with a have False ..
}
hence  "\<not>\<not>(\<not>P \<or> P)"  ..
thus ?thesis by (rule notnotD)
qed
