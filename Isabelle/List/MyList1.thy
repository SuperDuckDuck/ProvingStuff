theory MyList1 
  imports Sledgehammer Code_Numeral Lifting_Set
begin 
  
  datatype 'a MyList  =  Nil ("[]") | Cons (hd : 'a) (tl : 'a list) (infixr "::" 65) 
  
  lemma ""