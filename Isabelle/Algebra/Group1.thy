theory Group1
  imports Main
begin 


class times2 = 
  fixes times2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 70)
  
class semiGroup2 = times2 +
  assumes semiGroup_assoc [simp] : "(a \<odot> b) \<odot> c = a \<odot> (b \<odot> c)"
    
    
class abel  = semiGroup2 +
  assumes abel_comm : "a \<odot> b = b \<odot> a"
    
    
lemma  "x \<odot> y \<odot> z = (x \<odot> y) \<odot> z" by (rule refl)
    
lemma (in  abel) lft_comm : "b \<odot> (c \<odot> a) = a \<odot> (b \<odot> c)" 
proof - 
  have "b \<odot> (c \<odot> a) =  b \<odot> (a \<odot> c)" by (subst abel_comm ; rule refl)
  also have "\<dots> = b \<odot> a \<odot> c" by simp
  also have "\<dots> = a \<odot> b \<odot> c" by (simp add : abel_comm)
  also  have "\<dots> = a \<odot> (b \<odot> c)"  by simp
  finally show ?thesis by assumption
qed
  
definition (in semiGroup2) is_idempodent :: "'a \<Rightarrow> bool" where
  "is_idempodent val  = (if val \<odot> val = val then True else False)"
  
  
definition (in semiGroup2) is_neutral :: "'a \<Rightarrow> bool" where
  "is_neutral val = (if \<forall>x. val \<odot> x = x then True else False)"
  
lemma neutMult : "is_neutral n  \<Longrightarrow> n \<odot> m = m" 
proof -
  assume a:"is_neutral n"
  {
    assume b:"n \<odot> m \<noteq> m"
    hence c:"\<exists>x. n \<odot> x \<noteq> x" by (rule exI)
    hence "\<not>(\<forall>x . n \<odot> x = x)" by simp
    with a have False by (simp add : is_neutral_def)  
  }
  thus ?thesis by auto
qed
  
      
instantiation nat :: times2
begin
primrec times2_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "times2_nat 0  _ =  0"|
  "times2_nat (Suc n) m = m + times2_nat n m"
  
instance ..
end
 
lemma distributivity [simp] : fixes  a::nat and b::nat and c::nat shows  "a \<odot> b + a \<odot> c  = a \<odot> (b + c) " 
proof (induct a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  assume hyp:"a \<odot> b + a \<odot> c = a \<odot> (b + c)"
  show ?case by (simp add : hyp)
qed
  
lemma zeroComm [simp] : fixes a::nat shows  "a \<odot> 0 = 0 \<odot> a"
proof (induct a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  assume hyp:"a \<odot> 0 = 0 \<odot> a"
  then show ?case by simp
qed
  
lemma valMultOne [simp] : fixes a::nat shows  "a = a \<odot> 1" 
proof (induct a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  then show ?case by simp
qed
  
  
  
lemma commutativity [simp] : fixes a::nat and b::nat shows "a \<odot> b = b \<odot> a"
proof (induct a)
  case 0
  then show ?case using zeroComm by simp 
next
  case (Suc a)
  assume hyp:"a \<odot> b = b \<odot> a"
  have "Suc a \<odot> b = b + a \<odot> b" by simp
  also have "\<dots> = b + b \<odot> a" using hyp by simp
  also have "\<dots> =  b \<odot> 1 + b \<odot> a" by (subst valMultOne; rule refl)
  also have "\<dots> = b \<odot> (1 + a)" by simp
  finally show ?case by simp
qed
  
  
instantiation nat :: semiGroup2 
begin
instance
 
proof 
  fix a::nat and b::nat and c::nat
  show "a \<odot> b \<odot> c = a \<odot> (b \<odot> c) " 
  proof (induct a)
    case 0
    then show ?case by simp
  next
    case (Suc a)
    assume hyp:"a \<odot> b \<odot> c = a \<odot> (b \<odot> c)"
    have "Suc a \<odot> (b \<odot> c) = (b \<odot> c) + a \<odot> (b \<odot> c)" by simp
    also have "\<dots> = b \<odot> c + (a \<odot> b) \<odot> c" using hyp by simp
    also have "\<dots> = c \<odot> b + c \<odot> (a \<odot> b)" by simp
    also have "\<dots> = c \<odot> (b + (a \<odot> b))" by (subst distributivity; rule refl)
    also have "\<dots> = c \<odot> (b \<odot> 1 +  b \<odot> a)" by (subst(3) valMultOne ; subst(3) commutativity; rule refl)
    also have "\<dots> = c \<odot> (b \<odot> (1 + a))" by (simp only : distributivity)
    also have "\<dots> = c \<odot> (b \<odot>( Suc a))" by simp
    also have "\<dots> = c \<odot> (Suc a \<odot> b)" by simp
    finally show ?case by simp
  qed 
qed
end

  
value "(2::nat) \<odot> 2 :: nat" 
  
value "(2::nat) \<odot> 0"
  
lemma "(2 :: nat) \<odot> 2 = 4" by (simp add : times2_nat_def)
    

  
    
lemma fixes n::nat and m::nat shows "is_neutral n \<Longrightarrow> is_neutral m \<Longrightarrow> n = m"  
proof -
  assume a:"is_neutral n"
  assume b:"is_neutral m"
  {

    assume c:"n \<noteq> m"
    from a have d:"n \<odot> m = m"  by (simp only : neutMult)
    from b have "n \<odot> m = n"  by (simp only : neutMult commutativity)
    with d have "n = m" by simp
    with c have False by contradiction
  }
  thus ?thesis by auto
qed
  
        
  
typedef(overloaded) zeroNat = "{n . n = (0 ::nat) }" 
  by simp    
    
instantiation zeroNat :: zero
begin
instance ..
end
    
instantiation zeroNat :: times2 
begin
definition times2_zeroNat :: "zeroNat \<Rightarrow> zeroNat \<Rightarrow> zeroNat" where 
  "times2_zeroNat a b = 0"
  
instance ..
end
    
    
instantiation zeroNat :: semiGroup2
begin
instance 
proof 
  fix a::zeroNat and  b::zeroNat and c::zeroNat
  show " a \<odot> b \<odot> c = a \<odot> (b \<odot> c)" using times2_zeroNat_def  by simp
qed
end
 
value "(0 \<odot> 0) \<odot> (0 \<odot> 0) :: zeroNat"
     
lemma "(0::zeroNat) \<odot> 0 = 0" by (simp add : times2_zeroNat_def) 
  
lemma "((0::zeroNat) \<odot> 0) \<odot> (0 \<odot> 0) = 0"  by (simp add : times2_zeroNat_def)
  
instantiation int :: times2
begin
definition times2_int :: "int \<Rightarrow> int \<Rightarrow> int" where 
  "times2_int a b= a * b"
  
instance ..
end
  
  
instantiation int :: semiGroup2
begin
instance 
proof 
  fix a::int and b::int and c::int 
  show "a \<odot> b \<odot> c = a \<odot> (b \<odot> c)" using times2_int_def by simp
qed
end
  
value "(4::int) * (1::int)"

  
datatype myNat = zero ("0") | Suc myNat
  
