(*
Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

theory Poly_Maps imports Main 
  "HOL-Computational_Algebra.Polynomial_Factorial"
  (*"~~/src/HOL/Library/Polynomial_Factorial" *)
begin                                                 

(*
NOTE:
René Thiemann and Akihisa Yamada's Ring_Hom/Ring_Hom_Poly should be a good way to abstract 
similar definitions like of_int_poly, of_rat_poly and of_float_poly, but keeping those
constants (i.e. of_int_poly vs. map_poly of_int) might be sometimes useful. 
*)
  
section {*of_int_poly*}

definition of_int_poly:: "int poly \<Rightarrow> ('a::ring_char_0) poly" where
 "of_int_poly = map_poly of_int" 
  
lemma coeff_of_int_poly:"coeff (of_int_poly p)  = of_int o (coeff p)" 
  unfolding of_int_poly_def comp_def
  using coeff_map_poly of_int_0 by blast

lemma of_int_poly_0[simp]:"of_int_poly 0 = 0" 
  unfolding of_int_poly_def by simp

lemma of_int_poly_1[simp]:"of_int_poly 1 = 1" 
  unfolding of_int_poly_def by simp

lemma of_int_poly_eq_iff[simp]:"of_int_poly p = of_int_poly q \<longleftrightarrow> p = q" 
  unfolding  poly_eq_iff
  by (auto simp add:coeff_of_int_poly)     

lemma of_int_poly_eq_0_iff [simp]: "(of_int_poly a = 0) = (a = 0)"
  using of_int_poly_eq_iff [of _ 0] by simp

lemma zero_eq_of_int_poly_iff [simp]: "(0 = of_int_poly a) = (0 = a)"
  by simp

lemma of_int_poly_eq_1_iff [simp]: "(of_int_poly a = 1) = (a = 1)"
  by (metis of_int_poly_1 of_int_poly_eq_iff)

lemma one_eq_of_int_poly_iff [simp]: "(1 = of_int_poly a) = (1 = a)"
  by simp

lemma of_int_poly_pCons[simp]:"of_int_poly (pCons a p) = pCons (of_int a) (of_int_poly p)" 
  unfolding of_int_poly_def
  by (simp add: map_poly_pCons)
  
lemma of_int_poly_plus[simp]: "of_int_poly (p + q) = of_int_poly p +  of_int_poly q" 
  using Rat.of_rat_add
  by (auto simp add: poly_eq_iff coeff_of_int_poly)

lemma of_int_poly_smult[simp]:"of_int_poly (smult s p) = smult (of_int s) (of_int_poly p)" 
  using Int.of_int_mult 
  by (auto simp add: poly_eq_iff coeff_of_int_poly)

lemma of_int_poly_mult[simp]:"of_int_poly (p*q) = of_int_poly p * of_int_poly q"
  apply (induct p,intro poly_eqI)
  by auto

lemma of_int_poly_pcompose[simp]: "of_int_poly (pcompose p q) = pcompose (of_int_poly p) (of_int_poly q)"
  apply (induct p)
  by (auto simp add:pcompose_pCons)

lemma of_int_poly_degree[simp]:"degree (of_int_poly p) = degree p"
  by (induct p,auto)

lemma of_int_poly_poly:
  "of_int (poly p x) = poly (of_int_poly p) (of_int x)" 
apply (induct p)
by auto

lemma of_int_poly_monom:
  "of_int_poly (monom x n) = monom (of_int x) n"
apply (induct n)
by (auto simp add:monom_0 monom_Suc)

lemma [code abstract]: "coeffs (of_int_poly p)=  (map of_int (coeffs p))" 
  apply (induct p)
  apply auto 
by (metis not_0_cCons_eq zero_eq_of_int_poly_iff)

declare of_int_poly_def[symmetric,simp]

section {* of_rat_poly *}

definition of_rat_poly:: "rat poly \<Rightarrow> ('a::field_char_0) poly" where
 "of_rat_poly = map_poly of_rat"

lemma coeff_of_rat_poly:"coeff (of_rat_poly p)  = of_rat o (coeff p)" 
  unfolding of_rat_poly_def comp_def
  using coeff_map_poly of_rat_0 by blast

lemma of_rat_poly_0[simp]:"of_rat_poly 0 = 0" unfolding of_rat_poly_def by simp

lemma of_rat_poly_1[simp]:"of_rat_poly 1 = 1"  
  unfolding of_rat_poly_def by auto

lemma of_rat_poly_eq_iff[simp]:"of_rat_poly p = of_rat_poly q \<longleftrightarrow> p = q" 
  unfolding  poly_eq_iff
  by (auto simp add:coeff_of_rat_poly)

lemma of_rat_poly_eq_0_iff [simp]: "(of_rat_poly a = 0) = (a = 0)"
  using of_rat_poly_eq_iff [of _ 0] by simp

lemma zero_eq_of_rat_poly_iff [simp]: "(0 = of_rat_poly a) = (0 = a)"
  by simp

lemma of_rat_poly_eq_1_iff [simp]: "(of_rat_poly a = 1) = (a = 1)"
  using of_rat_poly_eq_iff [of _ 1] by simp

lemma one_eq_of_rat_poly_iff [simp]: "(1 = of_rat_poly a) = (1 = a)"
  by simp

lemma of_rat_poly_pCons[simp]:"of_rat_poly (pCons a p) = pCons (of_rat a) (of_rat_poly p)" 
  unfolding of_rat_poly_def
  by (simp add: map_poly_pCons)

lemma of_rat_poly_plus[simp]: "of_rat_poly (p + q) = of_rat_poly p +  of_rat_poly q" 
  using  Rat.of_rat_add
  by (auto simp add: poly_eq_iff coeff_of_rat_poly)

lemma of_rat_poly_smult[simp]:"of_rat_poly (smult s p) = smult (of_rat s) (of_rat_poly p)" 
  using Rat.of_rat_mult 
  by (auto simp add: poly_eq_iff coeff_of_rat_poly)

lemma of_rat_poly_mult[simp]:"of_rat_poly (p*q) = of_rat_poly p * of_rat_poly q"
  by (induct p,intro poly_eqI,auto)

lemma of_rat_poly_power[simp]:"of_rat_poly (p^n) = (of_rat_poly p) ^ n"
  by (induct n,auto)

lemma of_rat_poly_degree[simp]:"degree (of_rat_poly p) = degree p"
  by (induct p,auto)

lemma of_rat_poly_minus[simp]: "of_rat_poly (- p) = - (of_rat_poly p)" 
  using  of_rat_minus
  by (auto simp add: poly_eq_iff coeff_of_rat_poly)

lemma of_rat_poly_inj:"inj of_rat_poly"
by (meson injI of_rat_poly_eq_iff)

lemma of_rat_poly_eucl_rel_poly: 
    "eucl_rel_poly (of_rat_poly x) (of_rat_poly y) (of_rat_poly q,of_rat_poly r) 
      \<longleftrightarrow> eucl_rel_poly x y (q, r)"
  unfolding eucl_rel_poly_iff
  by (auto intro:iffD1[OF of_rat_poly_eq_iff])

lemma of_rat_poly_div_mod[simp]: 
    "of_rat_poly (p div q) = (of_rat_poly p) div (of_rat_poly q)"
    "of_rat_poly (p mod q) = (of_rat_poly p) mod (of_rat_poly q)"
  subgoal 
    apply (intro div_poly_eq[symmetric] mod_poly_eq[symmetric])
    apply (subst of_rat_poly_eucl_rel_poly)
    by (rule eucl_rel_poly[of p q])
  subgoal 
    apply (intro div_poly_eq[symmetric] mod_poly_eq[symmetric])
    apply (subst of_rat_poly_eucl_rel_poly)
    by (rule eucl_rel_poly[of p q])
  done

lemma of_rat_poly_poly:
  "real_of_rat (poly p x) = poly (of_rat_poly p) (real_of_rat x)"
by (induct p,auto simp add:of_rat_add of_rat_mult)

lemma of_rat_poly_monom:
  "of_rat_poly (monom x n) = monom (of_rat x) n"
apply (induct n)
by (auto simp add:monom_0 monom_Suc)

lemma of_rat_lead_coeff[simp]: "of_rat (lead_coeff p) = lead_coeff (of_rat_poly p)" 
  by (simp add: coeff_of_rat_poly)

lemma [code abstract]: "coeffs (of_rat_poly p)=  (map of_rat (coeffs p))" 
  apply (induct p)
  apply auto 
by (metis not_0_cCons_eq zero_eq_of_rat_poly_iff)

lemma of_rat_poly_of_int_poly_eq [simp]: "of_rat_poly (of_int_poly z) = of_int_poly z"
  unfolding poly_eq_iff coeff_of_rat_poly coeff_of_int_poly
  by auto      

declare of_rat_poly_def[symmetric,simp]

section {* of_real_poly *}

definition of_real_poly:: "real poly \<Rightarrow> ('a::{real_algebra_1,comm_semiring_1,field}) poly" where
 "of_real_poly = map_poly of_real"

lemma coeff_of_real_poly:"coeff (of_real_poly p)  = of_real o (coeff p)" 
  unfolding of_real_poly_def comp_def
  using coeff_map_poly of_real_0 by blast

lemma of_real_poly_0[simp]:"of_real_poly 0 = 0" unfolding of_real_poly_def by simp

lemma of_real_poly_1[simp]:"of_real_poly 1 = 1"  
  unfolding of_real_poly_def by simp

lemma of_real_poly_eq_iff[simp]:"of_real_poly p = of_real_poly q \<longleftrightarrow> p = q" 
  unfolding  poly_eq_iff
  by (auto simp add:coeff_of_real_poly)

lemma of_real_poly_eq_0_iff [simp]: "(of_real_poly a = 0) = (a = 0)"
  using of_real_poly_eq_iff [of _ 0] by simp

lemma zero_eq_of_real_poly_iff [simp]: "(0 = of_real_poly a) = (0 = a)"
  by simp

lemma of_real_poly_eq_1_iff [simp]: "(of_real_poly a = 1) = (a = 1)"
  using of_real_poly_eq_iff [of _ 1] of_real_poly_1 
  by auto
  
lemma one_eq_of_real_poly_iff [simp]: "(1 = of_real_poly a) = (1 = a)"
  by simp

lemma of_real_poly_pCons[simp]:"of_real_poly (pCons a p) = pCons (of_real a) (of_real_poly p)" 
  unfolding of_real_poly_def by (simp add: map_poly_pCons)

lemma of_real_poly_plus[simp]: "of_real_poly (p + q) = of_real_poly p +  of_real_poly q" 
  using  of_real_add
  by (auto simp add: poly_eq_iff coeff_of_real_poly)

lemma of_real_poly_smult[simp]:"of_real_poly (smult s p) = smult (of_real s) (of_real_poly p)" 
  using of_real_mult 
  by (auto simp add: poly_eq_iff coeff_of_real_poly)

lemma of_real_poly_mult[simp]:"of_real_poly (p*q) = of_real_poly p * of_real_poly q"
  by (induct p,intro poly_eqI,auto)

lemma of_real_poly_power[simp]:"of_real_poly (p^n) = (of_real_poly p) ^ n"
  by (induct n,auto)

lemma of_real_poly_degree[simp]:"degree (of_real_poly p) = degree p"
  by (induct p,auto)

lemma of_real_poly_minus[simp]: "of_real_poly (- p) = - (of_real_poly p)" 
  using  of_real_minus
  by (auto simp add: poly_eq_iff coeff_of_real_poly)

lemma of_real_poly_inj:"inj of_real_poly"
by (meson injI of_real_poly_eq_iff)

lemma of_real_poly_eucl_rel_poly: 
    "eucl_rel_poly (of_real_poly x) (of_real_poly y) (of_real_poly q,of_real_poly r) 
      \<longleftrightarrow> eucl_rel_poly x y (q, r) "
unfolding eucl_rel_poly_iff 
by (auto intro:iffD1[OF of_real_poly_eq_iff])

lemma of_real_poly_div_mod[simp]: 
    "of_real_poly (p div q) = (of_real_poly p) div (of_real_poly q)"
    "of_real_poly (p mod q) = (of_real_poly p) mod (of_real_poly q)"
  by (intro div_poly_eq[symmetric] mod_poly_eq[symmetric],subst of_real_poly_eucl_rel_poly
    ,rule eucl_rel_poly[of p q])+

lemma of_real_poly_poly:
  "of_real (poly p x) = poly (of_real_poly p) (of_real x)" 
by (induct p,auto)

lemma of_real_poly_monom:
  "of_real_poly (monom x n) = monom (of_real x) n"
apply (induct n)
by (auto simp add:monom_0 monom_Suc)

lemma of_real_lead_coeff[simp]: "of_real (lead_coeff p) = lead_coeff (of_real_poly p)" 
  by (simp add: coeff_of_real_poly)

lemma [code abstract]: "coeffs (of_real_poly p)=  (map of_real (coeffs p))" 
  apply (induct p)
  apply auto 
by (metis not_0_cCons_eq zero_eq_of_real_poly_iff)

lemma of_real_poly_of_int_poly_eq [simp]: "of_real_poly (of_int_poly z) = of_int_poly z"
  unfolding poly_eq_iff coeff_of_real_poly coeff_of_int_poly
  by auto      
    
declare of_real_poly_def[symmetric,simp]
 

end
