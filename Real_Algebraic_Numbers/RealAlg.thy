theory RealAlg imports
  RealAlg_Abs
  RealAlg_Arith
begin

(*lift Alg to alg*)
lift_definition RAlg:: "int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> alg" is
  "\<lambda>p lb ub. if valid_alg p lb ub then Alg p lb ub else 0" 
proof -
  fix p::"int poly" and lb ub::float
  define pp where "pp\<equiv>if valid_alg p lb ub then p else [:0,1:]"
  have "pp\<noteq>0" unfolding pp_def 
    by (metis degree_0 pCons_eq_0_iff valid_alg_deg zero_neq_one)
  thus "?thesis p lb ub" 
    apply (rule_tac x=pp in exI)
    by (auto simp add:alg_bound_and_root(3) pp_def)
qed

(*lift Ratreal to alg*)
lift_definition RRat:: "rat \<Rightarrow> alg" is
  "\<lambda>r. Ratreal r"
proof -
  fix r::rat
  obtain r1 r2 ::int where r:"r= of_int r1/ of_int r2" and "r2\<noteq>0" 
    by (metis Fract_of_int_quotient less_irrefl quotient_of_unique)
  define p where "p\<equiv>[:-r1,r2:]"
  show "?thesis r"
    apply (rule_tac x=p in exI)
    by (auto simp add:p_def r `r2\<noteq>0` of_rat_divide)
qed

end