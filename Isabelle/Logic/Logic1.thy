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


lemma "\<lbrakk> \<And>x . P x \<Longrightarrow> P z  ; P y \<rbrakk> \<Longrightarrow> P z"
proof -
  assume a:"\<And>x . P x \<Longrightarrow> P z" and  b:"P y"
  from a have "\<And>x . P x \<longrightarrow> P z" by (subst (asm) atomize_imp)
  hence "\<forall>x . P x \<longrightarrow> P z" by (subst (asm) atomize_all)
  hence "P y \<longrightarrow> P z" by (rule allE)
  from this and b  show "P z" by (rule mp)
qed  
  

lemma "\<lbrakk> \<And>x . P x \<Longrightarrow> P z  ; P y \<rbrakk> \<Longrightarrow> P z"
proof - 
  assume a:"\<And>x . P x \<Longrightarrow> P z" and  b:"P y"
  from a [OF b]  show "P z" by this
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

lemma "A \<or> B \<longleftrightarrow> A \<and> \<not>B \<or> A \<and> B \<or> \<not>A \<and> B"
proof -
  {
    assume a:"A \<or> B"
    {
      assume b:"\<not>((A \<and> \<not>B) \<or> (A \<and> B) \<or> (\<not>A \<and> B))"
      {
        assume c:A 
        {
          assume B 
          with c have "A \<and> B" ..
          hence "(A \<and> B) \<or> (\<not>A \<and> B)" ..
          hence "(A \<and> \<not>B) \<or> (A \<and> B) \<or> (\<not>A \<and> B)" by (rule disjI2)
          with b have False by contradiction
        }
        hence "\<not>B" ..
        with c have "A \<and> \<not>B" ..
        hence "(A \<and> \<not>B) \<or> (A \<and> B) \<or> (\<not>A \<and> B)" by blast
        with b have False by contradiction
      }
      note tmp=this
      {
        assume B 
        with b have False by blast
      }
      from a tmp this have False by (rule disjE)
    }
    hence "(A \<and> \<not>B) \<or> (A \<and> B) \<or> (\<not>A \<and> B)" by blast
  }
  moreover
  {
    assume "(A \<and> \<not>B) \<or> (A \<and> B) \<or> (\<not>A \<and> B)"
      
      
        
 
                
          
      

    