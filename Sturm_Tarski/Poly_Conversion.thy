theory Poly_Conversion imports 
  "Polynomial_Interpolation.Ring_Hom_Poly"
begin

section \<open>Converting @{typ "rat poly"} to @{typ "int poly"} by clearing the denominators\<close>

definition int_of_rat::"rat \<Rightarrow> int" where
  "int_of_rat = inv of_int"

lemma of_rat_inj[simp]: "inj of_rat"
by (simp add: linorder_injI)

lemma (in ring_char_0) of_int_inj[simp]: "inj of_int"
  by (simp add: inj_on_def)

lemma int_of_rat_id: "int_of_rat o of_int = id" 
  unfolding int_of_rat_def
  by auto

lemma int_of_rat_0[simp]:"int_of_rat 0 = 0" 
  by (metis id_apply int_of_rat_id o_def of_int_0)

lemma int_of_rat_inv:"r\<in>\<int> \<Longrightarrow> of_int (int_of_rat r) = r"
unfolding int_of_rat_def
by (simp add: Ints_def f_inv_into_f)

lemma int_of_rat_0_iff:"x\<in>\<int> \<Longrightarrow> int_of_rat x = 0 \<longleftrightarrow> x = 0" 
using int_of_rat_inv by force

lemma [code]:"int_of_rat r = (let (a,b) = quotient_of r in 
          if b=1 then a else Code.abort (STR ''Failed to convert rat to int'') 
          (\<lambda>_. int_of_rat r))"
  apply (auto simp add:split_beta int_of_rat_def)
  by (metis Fract_of_int_quotient inv_f_eq of_int_inj of_int_rat quotient_of_div surjective_pairing)  

definition de_lcm::"rat poly \<Rightarrow> int" where
  "de_lcm p = Lcm(set(map (\<lambda>x. snd (quotient_of x)) (coeffs p)))"

lemma de_lcm_pCons:"de_lcm (pCons a p) = lcm (snd (quotient_of a)) (de_lcm p)"
  unfolding de_lcm_def
  by (cases "a=0\<and>p=0",auto)

lemma de_lcm_0[simp]:"de_lcm 0 = 1" unfolding de_lcm_def by auto

lemma de_lcm_pos[simp]:"de_lcm p > 0"
  apply (induct p)
  apply (auto simp add:de_lcm_pCons)
  by (metis lcm_pos_int less_numeral_extra(3) quotient_of_denom_pos')+  

lemma de_lcm_ints: 
  fixes x::rat
  shows "x\<in>set (coeffs p) \<Longrightarrow> rat_of_int (de_lcm p) * x \<in> \<int>"
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  define a1 a2 where "a1\<equiv>fst (quotient_of a)" and "a2\<equiv>snd (quotient_of a)"
  have a:"a=(rat_of_int a1)/(rat_of_int a2)" and "a2>0" 
    using quotient_of_denom_pos'[of a] unfolding a1_def a2_def
    by (auto simp add: quotient_of_div)
  define mp1 where "mp1\<equiv>a2 div gcd (de_lcm p) a2"
  define mp2 where "mp2\<equiv>de_lcm p div gcd a2 (de_lcm p) "
  have lcm_times1:"lcm a2 (de_lcm p) = de_lcm p * mp1"
    using lcm_altdef_int[of "de_lcm p" a2,folded mp1_def] `a2>0` 
    unfolding mp1_def 
    apply (subst div_mult_swap)
    by (auto simp add: abs_of_pos gcd.commute lcm_altdef_int mult.commute)
  have lcm_times2:"lcm a2 (de_lcm p) = a2 * mp2"
    using lcm_altdef_int[of a2 "de_lcm p",folded mp1_def] `a2>0` 
    unfolding mp2_def by (subst div_mult_swap, auto simp add:abs_of_pos)
  show ?case
  proof (cases "x \<in> set (coeffs p)")    
    case True
    show ?thesis using pCons(2)[OF True]
      by (smt Ints_mult Ints_of_int a2_def de_lcm_pCons lcm_times1 
            mult.assoc mult.commute of_int_mult)
  next
    case False
    then have "x=a" 
      using pCons cCons_not_0_eq coeffs_pCons_eq_cCons insert_iff list.set(2) not_0_cCons_eq 
      by fastforce
    show ?thesis unfolding `x=a` de_lcm_pCons
      apply (fold a2_def,unfold a)
      by (simp add: de_lcm_pCons lcm_times2 of_rat_divide)
  qed
qed

definition clear_de::"rat poly \<Rightarrow> int poly" where
  "clear_de p = (SOME q. (map_poly of_int q) = smult (of_int (de_lcm p)) p)"

lemma clear_de:"of_int_poly(clear_de p) = smult (of_int (de_lcm p)) p"
proof -
  have "\<exists>q. (of_int_poly q) = smult (of_int (de_lcm p)) p" 
  proof (induct p)
    case 0
    show ?case by (metis map_poly_0 smult_0_right)
  next
    case (pCons a p)
    then obtain q1::"int poly" where q1:"of_int_poly q1 = smult (rat_of_int (de_lcm p)) p"
      by auto
    define a1 a2 where "a1\<equiv>fst (quotient_of a)" and "a2\<equiv>snd (quotient_of a)"
    have a:"a=(rat_of_int a1)/ (rat_of_int a2)" and "a2>0" 
        using quotient_of_denom_pos' quotient_of_div 
        unfolding a1_def a2_def by auto 
    define mp1 where "mp1\<equiv>a2 div gcd (de_lcm p) a2"
    define mp2 where "mp2\<equiv>de_lcm p div gcd a2 (de_lcm p) "
    have lcm_times1:"lcm a2 (de_lcm p) = de_lcm p * mp1"
      using lcm_altdef_int[of "de_lcm p" a2,folded mp1_def] `a2>0` 
      unfolding mp1_def 
      by (subst div_mult_swap, auto simp add: abs_of_pos gcd.commute lcm_altdef_int mult.commute)
    have lcm_times2:"lcm a2 (de_lcm p) = a2 * mp2"
      using lcm_altdef_int[of a2 "de_lcm p",folded mp1_def] `a2>0` 
      unfolding mp2_def by (subst div_mult_swap, auto simp add:abs_of_pos)
    define q2 where "q2\<equiv>pCons (mp2 * a1) (smult mp1 q1)"
    have "of_int_poly q2 = smult (rat_of_int (de_lcm (pCons a p))) (pCons a p)" using `a2>0`  
      apply (simp add:de_lcm_pCons )
      apply (fold a2_def)
      apply (unfold a)
      apply (subst lcm_times2,subst lcm_times1)
      by (simp add: Polynomial.map_poly_pCons mult.commute of_int_hom.map_poly_hom_smult q1 q2_def)
    then show ?case by auto
  qed
  then show ?thesis unfolding clear_de_def  by (meson someI_ex)
qed

lemma clear_de_0[simp]:"clear_de 0 = 0" 
  using clear_de[of 0] by auto

lemma [code abstract]: "coeffs (clear_de p) = 
    (let lcm = de_lcm p in map (\<lambda>x. int_of_rat (of_int lcm * x)) (coeffs p))"
proof -
  define mul where "mul\<equiv>rat_of_int (de_lcm p)"
  have "map_poly int_of_rat (of_int_poly q) = q" for q
    apply (subst map_poly_map_poly) 
    by (auto simp add:int_of_rat_id)
  then have clear_eq:"clear_de p = map_poly int_of_rat (smult (of_int (de_lcm p)) p)"
    using arg_cong[where f="map_poly int_of_rat",OF clear_de] 
    by auto
  show ?thesis
  proof (cases "p=0")
    case True
    then show ?thesis by auto
  next
    case False
    define g where "g\<equiv>(\<lambda>x. int_of_rat (rat_of_int (de_lcm p) * x))"
    have "de_lcm p \<noteq> 0" using de_lcm_pos by (metis less_irrefl)
    moreover have "last (coeffs p) \<noteq>0" 
      by (simp add: False last_coeffs_eq_coeff_degree)
    have False when asm:"last (map g (coeffs p)) =0" 
    proof -
      have "coeffs p \<noteq>[]" using False by auto
      hence "g (last (coeffs p)) = 0" using asm last_map[of "coeffs p" g] by auto
      hence "last (coeffs p) = 0"
        unfolding g_def using `coeffs p \<noteq>[]` `de_lcm p \<noteq> 0`
        apply (subst (asm) int_of_rat_0_iff)
        by (auto intro!: de_lcm_ints )
      thus False using `last (coeffs p) \<noteq>0` by simp
    qed
    ultimately show ?thesis
      apply (auto simp add: coeffs_smult clear_eq comp_def smult_conv_map_poly map_poly_map_poly coeffs_map_poly)  
      apply (fold g_def)
      by (metis False Ring_Hom_Poly.coeffs_map_poly coeffs_eq_Nil last_coeffs_eq_coeff_degree 
          last_map)
    qed
qed


end