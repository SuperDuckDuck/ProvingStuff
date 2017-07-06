theory Cardinality1
  imports Main 
begin 
  
lemma "\<exists>x . x \<in> A \<Longrightarrow> card A > 0" 
proof - 

  
lemma "card A = 0 \<Longrightarrow> A = {}"
proof - 
  assume "card A = 0"
  {
    assume "A \<noteq> {}"
    hence "\<exists>x . x \<in> A"  sorry
    
      
  
    