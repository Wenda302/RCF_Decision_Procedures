(*
    Author:     Wenda Li <wl302@cam.ac.uk>
*)

theory More_PolyMisc imports
  Poly_Maps
  Float_Misc
begin

  
lemma poly_mod:"poly q x=0 \<Longrightarrow> poly (p mod q) x = poly p x" 
  apply (subst (2) div_mult_mod_eq[symmetric,of p q])
  by (metis (no_types, lifting) add_cancel_left_left mult_zero_right poly_add poly_mult)

lemma pseudo_divmod_0[simp]: "pseudo_divmod f 0 = (0,f)"
  unfolding pseudo_divmod_def by auto

lemma map_poly_eq_iff:
  assumes "f 0=0" "inj f"
  shows "map_poly f x =map_poly f y \<longleftrightarrow> x=y" 
  using assms
  by (auto simp: poly_eq_iff coeff_map_poly dest:injD)
      
lemma pseudo_mod_0[simp]:
  shows "pseudo_mod p 0= p" "pseudo_mod 0 q = 0"
  unfolding pseudo_mod_def pseudo_divmod_def by (auto simp add: length_coeffs_degree)
  
lemma pseudo_mod_mod:
  assumes "g\<noteq>0"
  shows "smult (lead_coeff g ^ (Suc (degree f) - degree g)) (f mod g) = pseudo_mod f g"
proof -
  define a where "a=lead_coeff g ^ (Suc (degree f) - degree g)"
  have "a\<noteq>0" unfolding a_def by (simp add: assms)  
  define r where "r = pseudo_mod f g" 
  define r' where "r' = pseudo_mod (smult (1/a) f) g"
  obtain q where pdm: "pseudo_divmod f g = (q,r)" using r_def[unfolded pseudo_mod_def]
    apply (cases "pseudo_divmod f g")
    by auto
  obtain q' where pdm': "pseudo_divmod (smult (1/a) f) g = (q',r')" using r'_def[unfolded pseudo_mod_def] 
    apply (cases "pseudo_divmod (smult (1/a) f) g")
    by auto
  have "smult a f = q * g + r" and deg_r:"r = 0 \<or> degree r < degree g"
    using pseudo_divmod[OF assms pdm] unfolding a_def by auto
  moreover have "f = q' * g + r'" and deg_r':"r' = 0 \<or> degree r' < degree g"
    using \<open>a\<noteq>0\<close>  pseudo_divmod[OF assms pdm'] unfolding a_def degree_smult_eq 
    by auto  
  ultimately have gr:"(smult a q' - q) * g =  r - smult a r'" 
    by (auto simp add:smult_add_right algebra_simps)
  have "smult a r' = r" when "r=0" "r'=0"
    using that by auto
  moreover have "smult a r' = r" when "r\<noteq>0 \<or> r'\<noteq>0"
  proof -
    have "smult a q' - q =0"
    proof (rule ccontr)
      assume asm:"smult a q' - q \<noteq> 0 "
      have "degree (r - smult a r') < degree g"
        using deg_r deg_r' degree_diff_less that by force
      also have "... \<le> degree (( smult a q' - q)*g)"
        using degree_mult_right_le[OF asm,of g] by (simp add: mult.commute) 
      also have "... = degree (r - smult a r')"
        using gr by auto
      finally have "degree (r - smult a r') < degree (r - smult a r')" .
      then show False by simp
    qed
    then show ?thesis using gr by auto
  qed
  ultimately have "smult a r' = r" by argo
  then show ?thesis unfolding r_def r'_def a_def mod_poly_def 
    using assms by (auto simp add:field_simps)
qed    
    
lemma poly_pseudo_mod:
  assumes "poly q x=0" "q\<noteq>0"
  shows "poly (pseudo_mod p q) x = (lead_coeff q ^ (Suc (degree p) - degree q)) * poly p x"
proof -
  define a where "a=coeff q (degree q) ^ (Suc (degree p) - degree q)"
  obtain f r where fr:"pseudo_divmod p q = (f, r)" by fastforce
  then have "smult a p = q * f + r" "r = 0 \<or> degree r < degree q"
    using pseudo_divmod[OF \<open>q\<noteq>0\<close>] unfolding a_def by auto
  then have "poly (q*f+r) x = poly (smult a p) x" by auto    
  then show ?thesis
    using assms(1) fr unfolding pseudo_mod_def a_def
    by auto
qed  
  
lemma degree_less_timesD:
  fixes q::"'a::idom poly"
  assumes "q*g=r" and deg:"r=0 \<or> degree g>degree r" and "g\<noteq>0"
  shows "q=0 \<and> r=0"
proof -
  have ?thesis when "r=0"
    using assms(1) assms(3) no_zero_divisors that by blast    
  moreover have False when "r\<noteq>0"
  proof -
    have "degree r < degree g"
      using deg that by auto
    also have "... \<le> degree (q*g)"
      by (metis assms(1) degree_mult_right_le mult.commute mult_not_zero that)
    also have "... = degree r"
      using assms(1) by simp
    finally have "degree r<degree r" .
    then show False by auto
  qed
  ultimately show ?thesis by auto
qed

section \<open>Some extra useful lemmas about map_poly\<close>

lemma map_poly_plus:
  assumes "f 0 =0" "\<And>x y. f (x+y) = f x + f y"
  shows "map_poly f (p+q) = map_poly f p + map_poly f q"
  apply (intro poly_eqI)  
  by (auto simp add:coeff_map_poly assms)   
  
lemma map_poly_minus:
  assumes "f 0 =0" "\<And>x y. f (x-y) = f x - f y"
  shows "map_poly f (p-q) = map_poly f p - map_poly f q"
  apply (intro poly_eqI)  
  by (auto simp add:coeff_map_poly assms)     
    
lemma map_poly_plus_combine:
  assumes "f 0 = 0" "g 0 = 0"
  shows "map_poly f p + map_poly g p = map_poly (\<lambda>x. f x+g x) p"
  apply (induct p)
  by (auto simp add:map_poly_pCons assms)

lemma map_poly_minus_combine:
  assumes "f 0 = 0" "g 0 = 0"
  shows "map_poly f p - map_poly g p = map_poly (\<lambda>x. f x-g x) p"
  apply (induct p)
  by (auto simp add:map_poly_pCons assms)  
  
section{*rev poly*}

lift_definition rev_poly::"'a::zero poly \<Rightarrow> 'a poly" is
  "\<lambda>p n. if n>degree p then 0 else coeff p (degree p - n)"
using MOST_nat by auto

lemma rev_poly_0[simp]: "rev_poly 0 = 0" 
  apply transfer' 
  by auto

lemma rev_poly_0_iff[simp]: "rev_poly p = 0 \<longleftrightarrow> p=0"
  apply transfer'
  by (metis coeff_0 diff_zero leading_coeff_0_iff less_nat_zero_code)

lemma rev_poly_pCons:"rev_poly (pCons a p) = (if p=0 then [:a:] else rev_poly p + monom a (Suc (degree p)))" 
  apply transfer'
  apply transfer'
  by (auto split:nat.split simp add: Suc_diff_le)

lemma rev_poly_poly:
  fixes x::"'a::field" 
  assumes "x\<noteq>0"
  shows "x^(degree p) * poly (rev_poly p) (inverse x) = poly p x" 
apply (induct p )
apply (auto simp add:rev_poly_pCons field_simps poly_monom)
by (auto simp add:`x\<noteq>0`)

lemma rev_poly_poly_iff:
  fixes x::"'a::field" 
  assumes "x\<noteq>0"
  shows "poly (rev_poly p) (inverse x) =0  \<longleftrightarrow> poly p x = 0" 
apply (subst rev_poly_poly[OF `x\<noteq>0`,symmetric])
by (auto simp add:`x\<noteq>0`)

lemma [code abstract]: "coeffs (rev_poly p) = strip_while (HOL.eq 0) (rev (coeffs p))" 
proof (rule coeffs_eqI,subst nth_default_strip_while_dflt)
  fix n
  have "degree p < n \<Longrightarrow> nth_default 0 (rev (coeffs p)) n = 0"
    unfolding degree_eq_length_coeffs by (simp add: nth_default_beyond)
  moreover have "\<not> degree p < n \<Longrightarrow> coeff p (degree p - n) = nth_default 0 (rev (coeffs p)) n"
    unfolding degree_eq_length_coeffs 
    apply (auto simp add:nth_default_coeffs_eq[symmetric] nth_default_def rev_nth)
    by (metis One_nat_def degree_eq_length_coeffs length_coeffs_degree not_less_eq)
  ultimately show "coeff (rev_poly p) n = nth_default 0 (rev (coeffs p)) n"
    by transfer auto
qed simp

lemma of_rat_poly_rev_poly:
  "of_rat_poly (rev_poly p) = rev_poly (of_rat_poly p)"
apply (induct p)
by (auto simp add:rev_poly_pCons of_rat_poly_monom)

lemma of_int_poly_rev_poly:
  "of_int_poly (rev_poly p) = rev_poly (of_int_poly p)"
apply (induct p)
by (auto simp add:rev_poly_pCons of_int_poly_monom)

section \<open> @{typ "rat poly"} to @{typ "int poly"} by clearing the denominators\<close>

definition is_rat::"real \<Rightarrow> bool" where
  "is_rat x = (x\<in>\<rat>)"

lemma [code]:"is_rat (Ratreal x) = True" unfolding is_rat_def by auto

definition rat_of_real::"real \<Rightarrow> rat" where
  "rat_of_real = inv of_rat"

lemma [code]:
    "rat_of_real (Ratreal r) = r" 
    "rat_of_real (real_of_float f) = rat_of_float f"
  subgoal by (metis Ratreal_def f_inv_into_f of_rat_eq_iff rangeI rat_of_real_def)
  subgoal by (metis f_inv_into_f of_rat_eq_iff rangeI rat_of_real_def real_of_rat_of_float)
  done

lemma rat_of_real_id: "rat_of_real o of_rat = id" unfolding rat_of_real_def
  by (meson inj_onI inv_o_cancel of_rat_eq_iff)

lemma rat_of_real_0[simp]: "rat_of_real 0 = 0" 
  by (metis f_inv_into_f of_rat_0 of_rat_eq_iff rangeI rat_of_real_def)

lemma rat_of_real_inv:"r\<in>\<rat> \<Longrightarrow> of_rat (rat_of_real r) = r"
unfolding rat_of_real_def
by (simp add: Rats_def f_inv_into_f)

lemma rat_of_real_0_iff:"x\<in>\<rat> \<Longrightarrow> rat_of_real x = 0 \<longleftrightarrow> x = 0" 
using rat_of_real_inv by force

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
          (%_. int_of_rat r))"
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
  "clear_de p = (SOME q. (of_int_poly q) = smult (of_int (de_lcm p)) p)"

lemma clear_de:"of_int_poly(clear_de p) = smult (of_int (de_lcm p)) p"
proof -
  have "\<exists>q. (of_int_poly q) = smult (of_int (de_lcm p)) p" 
  proof (induct p)
    case 0
    show ?case by auto
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
      by (auto simp add:q2_def q1 mult.commute)
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
    unfolding of_int_poly_def
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
      by (metis (full_types) no_trailing_unfold strip_while_idem_iff)
    qed
qed


end


