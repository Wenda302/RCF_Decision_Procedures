theory Preprocess_Polys imports 
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
  "../Sturm_Tarski/Poly_Conversion"
begin

section \<open> @{typ "real poly"} to @{typ "int poly"} by clearing the denominators\<close>

definition is_rat::"real \<Rightarrow> bool" where
  "is_rat x = (x\<in>\<rat>)"

definition all_coeffs_rat::"real poly \<Rightarrow> bool" where 
  "all_coeffs_rat p = list_all is_rat (coeffs p)"

definition rat_of_real::"real \<Rightarrow> rat" where
  "rat_of_real = inv of_rat"

lemma [code]:"is_rat (Ratreal x) = True" unfolding is_rat_def by auto

lemma [code]:
    "rat_of_real (Ratreal r) = r" 
    (*"rat_of_real (real_of_float f) = rat_of_float f"*)
  subgoal by (metis Ratreal_def f_inv_into_f of_rat_eq_iff rangeI rat_of_real_def)
  (*subgoal by (metis f_inv_into_f of_rat_eq_iff rangeI rat_of_real_def 
                real_of_rat_of_float) *)
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

definition clear_de_real :: "real poly \<Rightarrow> int poly" where
  "clear_de_real p \<equiv> clear_de (map_poly rat_of_real p)"

abbreviation de_lcm_real :: "real poly \<Rightarrow> int" where 
  "de_lcm_real p \<equiv> de_lcm (map_poly rat_of_real p)"

lemma clear_de_real:
  assumes "all_coeffs_rat p"
  shows "of_int_poly (clear_de_real p) = smult (de_lcm_real p) p"
proof -
  have "of_int_poly (clear_de (map_poly rat_of_real p)) =
      smult (rat_of_int (de_lcm_real p)) (map_poly rat_of_real p)"
    using clear_de[of "map_poly rat_of_real p"] .
  also have "map_poly real_of_rat ... = 
        smult (real_of_int (de_lcm_real p)) (map_poly (real_of_rat \<circ> rat_of_real) p)"
    unfolding of_rat_hom.map_poly_hom_smult
    by (simp add:map_poly_map_poly)
  also have "... = smult (de_lcm_real p) (map_poly id p)"
  proof -
    have "map_poly (real_of_rat \<circ> rat_of_real) p = map_poly id p"
      apply (rule map_poly_cong)
      using assms rat_of_real_inv unfolding all_coeffs_rat_def is_rat_def 
      by (simp add: list.pred_set)
    then show ?thesis by simp
  qed
  also have "... = smult (de_lcm_real p) p"
    by simp
  finally have "map_poly real_of_rat (of_int_poly (clear_de 
      (map_poly rat_of_real p))) = smult (real_of_int (de_lcm_real p)) p" .
  then show ?thesis 
    by (simp add:map_poly_map_poly comp_def clear_de_real_def)
qed

end