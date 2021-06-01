theory Univariate_Sign_Determination imports Real_Alg_Imp
begin

section \<open>Univariate sign determination procedure\<close>

definition sign_int_coeffs_at :: "int poly \<Rightarrow> alg_imp \<Rightarrow> int" where 
  "sign_int_coeffs_at q x = sign (eval_poly of_int q (real_of_alg_imp x))"

lemma sign_int_coeffs_at_Ratalg[code]: 
  "sign_int_coeffs_at q (Ratalg x lb ub) = sign (eval_poly rat_of_int q x)" (is "?L=?R")
proof -
  have "?R = sign (real_of_rat (eval_poly rat_of_int q x))"
    by simp
  also have "... = sign (poly (of_int_poly q) (real_of_rat x))"
    unfolding eval_poly_def
    by (simp flip:of_rat_hom.poly_map_poly add:map_poly_map_poly comp_def)
  also have "... = ?L"
    unfolding sign_int_coeffs_at_def eval_poly_def by simp
  finally show ?thesis by simp
qed

lemma sign_int_coeffs_at_Polyalg[code]: 
  "sign_int_coeffs_at q (Polyalg p lb ub) = ( 
    if valid_alg p lb ub then 
      fi_changes_itv_spmods lb ub p (pderiv p * q)
    else Code.abort (STR ''Invalid sgn_at'') 
        (\<lambda>_. sign_int_coeffs_at q (Polyalg p lb ub))
    )"
proof (cases "valid_alg p lb ub")
  case True
  let ?ip = "of_int_poly p" and ?iq="of_int_poly q"

  have "sign_int_coeffs_at q (Polyalg p lb ub) = taq {Alg p lb ub} (of_int_poly q)"
    unfolding sign_int_coeffs_at_def by (simp add:eval_poly_def taq_def)
  also have "... = taq {x::real. poly ?ip x = 0 \<and> lb < x \<and> x < ub} ?iq"
  proof -
    have "{Alg p lb ub} = {x. poly ?ip x = 0 \<and> lb < x \<and> x < ub}"
      using alg_bound_and_root[OF True]  alg_eq[OF True]
      by safe meson
    then show ?thesis by simp
  qed
  also have "... = changes_itv_smods (real_of_float lb) (real_of_float ub) (of_int_poly p)
     (pderiv (of_int_poly p) * of_int_poly q)"
    apply (rule sturm_tarski_interval)
    using True unfolding valid_alg_def 
    by (auto simp add: float_int.map_poly_R_hom_commute)
  also have "... = changes_itv_smods (real_of_float lb) (real_of_float ub) (of_int_poly p)
     (of_int_poly ((pderiv p) *  q))"
    by (simp add: of_int_hom.map_poly_pderiv of_int_poly_hom.hom_mult)
  also have "... = fi_changes_itv_spmods lb ub p (pderiv p * q)"
    using float_int.changes_spmods_smods(1) by simp
  finally have "sign_int_coeffs_at q (Polyalg p lb ub) 
      = fi_changes_itv_spmods lb ub p (pderiv p * q)" .
  then show ?thesis using True by auto
qed auto

lemma sign_int_coeffs_at_Floatalg[code]: 
  "sign_int_coeffs_at q (Floatalg f) = sign (eval_poly float_of_int q f) "  (is "?L=?R")
proof -
  have "?R = sign (real_of_float (eval_poly float_of_int q f))"
    by simp
  also have "... = sign (poly (of_int_poly q) (real_of_float f))"
    unfolding eval_poly_def
    using float_int.map_poly_R_hom_commute by presburger
  also have "... = ?L"
    unfolding sign_int_coeffs_at_def eval_poly_def by simp
  finally show ?thesis by simp
qed  


end