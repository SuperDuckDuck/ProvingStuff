theory UniversalSet1
  imports Set
begin 
  
abbreviation NewUniv ::"'a set" where 
  "NewUniv \<equiv> \<top>"
    

  
lemma helper1 : "{x . \<top>} = NewUniv"  by (subst top_bool_def ; subst top_set_def ; subst top_fun_def; subst top_bool_def; rule refl)
    
lemma helper2 : "{x . False} = {}" 
proof -
  have "{x . False} = {x . \<bottom>}" by (subst bot_bool_def; rule refl)
  also have "\<dots> = Collect (\<lambda>x .\<bottom>)" by (rule refl) (*unnecessary syntactic step for understanding purposes*)
  also have "\<dots> = Collect \<bottom>" by (subst bot_fun_def ; rule refl)
  also have  "\<dots> = {}" by (subst bot_set_def; rule refl)
  finally show ?thesis by assumption
qed
    
lemma myCollectConst : "{x . P} = (if P then NewUniv else {})" 
proof (cases P)
  case True
  assume a:P
    
  have "(if P then NewUniv else {}) = (if True then NewUniv else {})" by (subst a; rule refl)
  also have "\<dots> = NewUniv" by (rule if_True)
  finally have c:"(if P then NewUniv else {}) = NewUniv" by assumption

  have "{x . P}  = {x . True}" by (subst a; rule refl)
  also have "\<dots> = {x. \<top>}" by (subst top_bool_def; rule refl)
  also have "\<dots> =  NewUniv" by (subst helper1; rule refl)
  finally have d:"{x. P} = NewUniv" by assumption
      
  have e:"({x . P} = (if P then NewUniv else {})) = (NewUniv = NewUniv) " by (subst d; subst c;simp)
  show ?thesis by (subst e; rule refl)
next
  case False
  assume a:"\<not>P"
    
  hence b:"P = False" by simp
   
  have "{x . P} = {x . False}" by (simp add : b)
  also have "\<dots> = {}" by (simp only : helper2)
  finally have c:"{x . P} = {}" by assumption
      
  have "(if P then NewUniv else {}) = (if False then NewUniv else {})" by (subst b; rule refl)
  also have "\<dots> =  {}" by (subst if_False ; rule refl) 
  finally have d:"(if P then NewUniv else {}) = {}" by assumption

  show ?thesis by (subst d; subst c; rule refl) 
qed

  
  