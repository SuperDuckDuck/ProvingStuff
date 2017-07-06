theory Ordering1 
  imports Main
begin 


  

lemma "a \<le> b \<Longrightarrow> a = b \<or> a < b" 
proof -
  assume a:"a \<le> b"
  show ?thesis 
  proof (cases "a =b")
    case True
    then show ?thesis by simp 
  next
    case False
    assume "a \<noteq> b"
      with a have "a < b" by 
    then show ?thesis sorry
  qed
    
    