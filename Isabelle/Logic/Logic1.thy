theory Logic1
  imports Main 
begin 




lemma bla : fixes a  assumes "\<forall>x. A x" shows "A a \<or> A b"
proof -
  from assms show ?thesis by simp
qed
  

  
lemma "(\<forall>x. A x) \<longrightarrow> (\<exists>x. A x)"
proof -
  {
    fix a
    assume "\<forall>x. A x"
    hence "A a" by (rule allE)
    hence "\<exists>x. A x" by (rule exI)
  }
  thus ?thesis by simp
qed
  
  
lemma "(A \<and> B) \<longleftrightarrow> (\<not> (A \<longrightarrow> \<not>B))"
proof -
  {
    assume a:"A \<and> B"
    hence b:A ..
    from a have c:B .. 
    {
      assume "A \<longrightarrow> \<not>B"
      from this and b have "\<not>B" ..
      with c have False by simp 
    }
    hence "\<not>(A \<longrightarrow> \<not>B)" ..
  }
  moreover
  {
    assume a:"\<not> (A \<longrightarrow> \<not>B)"
    {
      assume b:"\<not>(A \<and> B)"
      {
        assume c:A 
        {
          assume B 
          with c have "A \<and> B" ..
          with b have False by simp
        }
        hence "\<not>B" ..
      }
      hence "A \<longrightarrow> \<not>B" ..
      with a have False by simp
    }
    hence "A \<and> B" by auto
  }
  ultimately show ?thesis by (rule iffI)
qed



      

    