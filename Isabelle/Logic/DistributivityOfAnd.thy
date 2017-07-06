theory DistributivityOfAnd 
  imports Main 
begin 
  
lemma "A \<and> (B \<or> C) \<longleftrightarrow> (A \<and> B) \<or> (A \<and> C)" 
proof - 
  {
    assume a:"A \<and> (B \<or> C)" 
    hence b:A ..
    from a have c:"B \<or> C" ..
    {
      assume B 
      with b have "A \<and> B" ..
      hence " (A \<and> B) \<or> (A \<and> C)" ..
    }
    note tmp=this
    {
      assume C 
      with b have "A \<and> C" ..
      hence "(A \<and> B) \<or> (A \<and> C)" ..
    }
    from c and tmp and this have "(A \<and> B) \<or> (A \<and> C)" ..
  }
  moreover
  {
    assume a:"(A \<and> B) \<or> (A \<and> C)"
    {
      assume b:"A \<and> B"
      hence c:A ..
      from b have B ..
      hence "B \<or> C" ..
      with c have "A \<and> (B \<or> C)" ..
    }
    note tmp=this
    {
      assume b:"A \<and> C"
      hence c:A ..
      from b have C ..
      hence "B \<or> C" ..
      with c have "A \<and> (B \<or> C)" ..
    }
    from a and tmp and this have "A \<and> (B \<or> C)" ..
  }
  ultimately show ?thesis ..
qed
  
    
        