theory SetTheory1
imports Main 
begin 



lemma "A = B \<Longrightarrow> A \<subseteq> B \<and> B \<subseteq> A" 
proof (rule conjI)
  assume "A = B"
  thus "A \<subseteq> B" by (rule equalityD1)
 next
  assume "A = B"
  thus "B \<subseteq> A" by (rule equalityD2)
qed

    
lemma helper : " A \<subset> B \<and> B \<subset> A  \<Longrightarrow> A = B" 
proof (rule subset_antisym) 
  assume a:"A \<subset> B \<and> B \<subset> A"
  hence b:"A \<subset> B" ..
  thus "A \<subseteq> B"  by simp
next
  assume "A \<subset> B \<and> B \<subset> A"
  hence "B \<subset> A" ..
  thus "B \<subseteq> A" by simp
qed
       
lemma "A \<subset> B \<Longrightarrow> A \<subseteq> B" by simp

    (*this one is non sensical*)
lemma helper2 : "(\<forall>x. (x \<in> A \<longleftrightarrow> x \<in> B)) \<Longrightarrow> (A = B)" 
proof -
  assume a:"\<forall>x. (x \<in> A) = (x \<in> B)"
  {
    assume "A \<noteq> B"
    from this obtain y where b:"y \<in> A  \<and> y \<notin> B" using a by auto
    hence c:"y \<in> A" ..
    from b have d:"y \<notin> B" ..
    from a have "(y \<in> A) = (y \<in> B)" by (rule allE)
    with d and c have False by simp
  }
  hence "\<not> (A \<noteq> B)" by (rule notI)
  thus ?thesis by simp
qed

lemma "\<forall>x. (x \<in> A) \<longleftrightarrow> (x \<in> B) \<Longrightarrow> (A = B)" 
proof -
  assume "\<forall>x. (x \<in> A) \<longleftrightarrow> (x \<in> B)"
  hence "\<And>y. (y \<in> A) \<longleftrightarrow> (y \<in> B)" by (rule allE)
  hence "{y. y \<in> A} = {y . y \<in> B}" by simp
  thus "A = B" by simp
qed
  
lemma "A \<inter> B = {x . x \<in> A \<and>  x \<in> B}" by (rule Int_def)
    
lemma "A \<noteq> B  \<Longrightarrow> \<exists>y. y \<in> A  \<and> y \<notin> B \<or> y \<notin> A \<and> y \<in> B  "
proof - 
  assume a:"A \<noteq> B"
  {
    assume b:"\<not>(\<exists>y. y \<in> A  \<and> y \<notin> B \<or> y \<notin> A \<and> y \<in> B)"
    {
      fix y
      from b have  "(y \<in> A \<longrightarrow> y \<in> B)  \<and> ((y \<in> A) \<or> (y \<notin> B))" by simp
      hence "(y \<in> A \<longrightarrow> y \<in> B)  \<and> (y \<in> B \<longrightarrow> y \<in> A)" by auto
      hence "y \<in> A \<longleftrightarrow> y \<in> B" by auto
    }
    hence "\<forall>y. y \<in> A \<longleftrightarrow> y \<in> B" by (rule allI)
    hence "{y. y \<in> A} = {y. y \<in> B}" by simp
    hence "A = B" by simp
    with a have False by contradiction
  }
  thus "\<exists>y. y \<in> A  \<and> y \<notin> B \<or> y \<notin> A \<and> y \<in> B" by auto
qed
            
lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" by blast
          
  
lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" 
proof -
  {
    fix x
    have "(x \<in> (A \<inter> (B \<union> C))) =  (x \<in> A \<and> x \<in> (B \<union> C))" by simp
    also have "\<dots> = (x \<in> A \<and> (x \<in> B \<or> x \<in> C))" by simp
    also have "\<dots> = ((x \<in> A \<and> x \<in> B) \<or> (x \<in> A \<and> x \<in> C))" 
    proof -
      have "(x \<in> A \<and> (x \<in> B \<or> x \<in> C)) \<Longrightarrow> (x \<in> A \<and> x \<in> B \<or> x \<in> A \<and> x \<in> C)" by simp
      moreover
      {
        assume "x \<in> A \<and> x \<in> B \<or> x \<in> A \<and> x \<in> C"
        hence "x \<in> A \<and> (x \<in> B \<or> x \<in> C)" by blast
      }
      ultimately show ?thesis by (rule iffI)
    qed
    also have "\<dots> = (x \<in> (A \<inter> B) \<or> x \<in> (A \<inter> C))" by simp
    also have "\<dots> = (x \<in> ((A \<inter> B) \<union> (A \<inter> C)))" by simp
    finally have "(x \<in> (A \<inter> (B \<union> C))) = (x \<in> ((A \<inter> B) \<union> (A \<inter> C)))" by assumption      
  }
  hence "\<forall>x. (x \<in> (A \<inter> (B \<union> C))) = (x \<in> (A \<inter> B) \<union> (A \<inter> C))" by (rule allI)
  thus ?thesis by (simp add : helper2)    
qed
 
lemma "A \<subset> B \<Longrightarrow> B \<subset> C \<Longrightarrow> A \<subset> C" by (rule order.strict_trans)
  
lemma "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subseteq> C" 
proof -
  assume a:"A \<subseteq> B"
  assume b:"B \<subseteq> C"
  show ?thesis 
  proof (cases "A = B")
    case True
    assume "A = B"
    with b show ?thesis by simp
  next
    case False
    assume "A \<noteq> B"
    with a have c:"A \<subset> B" by simp
    then show ?thesis 
    proof (cases "B = C")
      case True
      with c have "A \<subset> C" by simp
      then show ?thesis by simp
    next
      case False
      with b have "B \<subset> C" by simp
      with c show ?thesis by simp
    qed
  qed
qed

  
lemma "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> C \<subseteq> A \<Longrightarrow> A = B \<and>  B = C \<and> C = A" 
proof - 
  assume a:"A \<subseteq> B"
  assume b:"B \<subseteq> C" 
  assume c:"C \<subseteq> A" 
  from a and b have "A \<subseteq> C" by simp
  with c have d:"A = C" by simp
  with a and b have e:"A = B" by simp
  with d have "B = C" by simp
  with d and e show ?thesis by simp
qed

lemma "{x. False}= {}" 
proof - 
  have "{x . False} = (if False then UNIV else {})" unfolding Collect_const by (rule subst; rule refl)
  also have "\<dots> = {}" by simp
  finally show ?thesis by assumption
qed

lemma "A \<inter> B = A - (A - B)" by blast
    
lemma "A \<inter> B = A - (A - B)"
proof -
  {
    assume "A \<inter> B"
      

lemma "A \<in> \<A> \<Longrightarrow> B \<in> \<A> \<Longrightarrow> "  
  
lemma "\<exists>x. x \<in> {n::nat . n \<noteq> 5}" 
  using [[simp_trace_new mode=full]]
proof -
  obtain y::nat where "y \<noteq> (5::nat)"  
  proof - 
    assume a:"\<And>y. y \<noteq> (5::nat) \<Longrightarrow> thesis"
      thus thesis using one_eq_numeral_iff by blast

   

  
lemma "A \<noteq> {} = (\<exists>x . x \<in> A)" 
proof -
  {
    assume "A \<noteq> {}"
      
      

    
lemma "\<exists>x. x \<in> A \<Longrightarrow> card A > 0" 
proof - 
  assume "\<exists>x . x \<in> A"
  {
    assume "card A \<le> 0"
    hence "card A = 0" by simp
        hence "A = {}" 
      
  
lemma "A = {} \<Longrightarrow> \<forall>x. x \<notin> A"
proof (rule allI)
  fix x
  assume "A = {}"


      

lemma "A = {} = (\<forall>x. x \<notin> A)" 
proof -
  {
    assume a:"A = {}"
    hence b:"card A = 0" by simp
    {
      assume c:"\<exists>x. x \<in> A"
      {
        fix x 
        assume "x \<in> A" 
        with a have False by simp
      }
      with c have False by (rule exE)
    }
    hence "\<forall>x. x \<notin> A" by auto
  }
  moreover
  {
    assume "\<forall>x. x \<notin> A"
    {
      
        
    
      
  
lemma helper3: "B \<noteq> {} = (\<exists>x. x \<in> B)" 
proof -
  {
    assume a:"B \<noteq> {}"
    {
      assume "\<not>(\<exists>x. x \<in> B)"
      hence "B = {}" by simp 
      with a have False by contradiction
    }
    hence "\<not>\<not>(\<exists>x. x \<in> B)" by (rule notI)
    hence "\<exists>x. x \<in> B" by (rule notnotD)
  }
  moreover
  {
    assume a:"\<exists>x. x \<in> B" 
    {
      assume "B = {}"
      hence "\<forall>x. x \<notin> B" by (subst all_not_in_conv) 
      hence "\<not>(\<exists>x. x \<in> B)" by simp
      with a have False by contradiction
    }
    hence "B \<noteq> {}" by auto
  }
    ultimately show ?thesis by (rule iffI)
qed
  
        

lemma "A \<inter> B = {} \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<notin> B \<or> x \<notin> A \<and> x \<in> B \<or> A = {} \<and> B = {}" 
  using [[simp_trace_new mode=full]]
proof - 
  assume "A \<inter> B = {}"
  show ?thesis 
  proof (cases "A = {}")
    case True
    assume a:"A = {}"
    then show ?thesis
    proof (cases "B = {}")
      case True
      with a  show ?thesis by simp
    next
      case False
      assume b:"B \<noteq> {}"
      from b have  "(\<exists>x. x \<in> A \<and> x \<notin> B \<or> x \<notin> A \<and> x \<in> B \<or> A = {} \<and> B = {}) = (\<exists>x. x \<in> A \<and> x \<notin> B \<or> x \<notin> A \<and> x \<in> B \<or> False)" by simp
      also from a have "\<dots> = (\<exists>x. False \<or> x \<notin> A \<and> x \<in> B)" by simp
      also have "\<dots> = (\<exists>x. x \<notin> A \<and> x \<in> B)" by simp
      also from a have "\<dots> = (\<exists>x. True \<and> x \<in> B)" by simp
      also have "\<dots> = (\<exists>x. x \<in> B)" by simp
      also have "\<dots> = (B \<noteq> {})" unfolding helper3  by (rule subst; rule refl)
      finally show ?thesis using b by simp
    qed
  next
    case False
    assume a:"A \<noteq> {}"
    then show ?thesis 
    proof (cases "B = {}")
      case True
      with a show ?thesis by auto 
    next
      case False
        
      then show ?thesis sorry
    qed
      
  qed
 

  
  
  
lemma "A \<inter> B = {} \<Longrightarrow> card(A \<union> B) = card A + card B" 
proof -
  assume a:"A \<inter> B = {}"
  {
    assume "card(A \<union> B) \<noteq> card A + card B"

      
      

      

lemma "card (a:: 'a set) + card (b::'a set)  \<ge> card (a \<union> b)" 
proof (cases "a \<inter> b = {}")
  case True
  then show ?thesis 
next
  case False
  then show ?thesis sorry
qed
  
lemma "A \<union> B = A \<inter> -B \<union> A \<inter> B \<union> -A \<inter> B" 
proof - 
  {
    fix x
    assume "x \<in> (A \<union> B)"
      
      
  