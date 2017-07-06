theory LinearAlgebra1
imports Equivalence_Lebesgue_Henstock_Integration
begin 


lemma plus_emeasure':
  assumes "A \<in> sets M" "B \<in> sets M" "A \<inter> B \<in> null_sets M"
  shows "emeasure M A + emeasure M B = emeasure M (A \<union> B)"