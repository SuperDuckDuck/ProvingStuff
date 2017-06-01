theory NumberTheory1
imports Complex 
begin 

thm floor_correct
lemma floor_smaller :  fixes n::real shows " \<lfloor>n\<rfloor> \<le> n"  using floor_correct
apply (rule conjE)
apply (assumption)
done 

lemma floor_smaller2 : fixes n::real shows " \<lfloor>n\<rfloor> \<le> n"  
proof -
  from floor_correct have "of_int \<lfloor>n\<rfloor> \<le> n \<and> n < of_int (\<lfloor>n\<rfloor> + 1) " by assumption
  hence "of_int \<lfloor>n\<rfloor> \<le> n" by (rule conjE)
  thus " real_of_int \<lfloor>n\<rfloor> \<le> n" by (simp del : of_int_floor_le)
qed


lemma "even (n::int) \<longleftrightarrow> (\<exists> k . n = 2*k)" by (rule dvd_def)


lemma "\<forall> n \<in> \<real> . odd n \<or> even n" 
proof (rule  Set.ballI)
  fix n::'a
  assume a:"n \<in> \<real>"
  show "odd n \<or> even n" by (rule excluded_middle)
qed
    
 

lemma "odd (n::int) \<longleftrightarrow> (\<exists>k. n = 2*k+1)"
using [[simp_trace_new mode=full]]
proof (rule iffI)
  assume a:"odd n"
  {
    fix k::int
    assume b:"n = 2*k + 1"
    {
      assume c:"even (2*k+1)"
      from c and b have False by simp
    }
    hence "odd (2 * k + 1)" by simp
  }


lemma "sqrt (real 2) \<notin> \<rat>" 
proof 
  

    
    
    
    
  
  