theory Univariate_Sign_Determination imports Real_Alg_Imp
begin

section \<open>Univariate sign determination procedure\<close>

definition sign_int_coeffs_at :: "int poly \<Rightarrow> alg_imp \<Rightarrow> int" where 
  "sign_int_coeffs_at q x = sign (eval_poly of_int q (real_of_alg_imp x))"

definition sign_at_Polyalg_core:: "int poly \<Rightarrow> int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> int" where
  "sign_at_Polyalg_core q p lb ub 
      = (if p=q then 
            0 
        else if descartes_roots_test lb ub (of_int_poly q) =  0 then
            sign (eval_poly float_of_int q (mid_fl lb ub))
        else 
            fi_changes_itv_spmods lb ub p (pderiv p * q)
        )"

lemma same_sign_no_root:
  fixes a b::real
  defines "s\<equiv>{a<..<b}"
  assumes "proots_within p s = {}" "x\<in>s" "y\<in>s"
  shows "sign (poly p x) = sign (poly p y)"
proof (cases "x=y")
  case False
  show ?thesis 
  proof (rule ccontr)
    assume "sign (poly p x) \<noteq> sign (poly p y)"
    moreover have "poly p x \<noteq>0" "poly p y \<noteq>0" 
      using assms(2-4) by blast+
    ultimately have "poly p x * poly p y < 0"
      by (metis linorder_neqE_linordered_idom mult_less_0_iff sign_def)
    have False if "x>y"
    proof -
      obtain z where "z>y" "z < x" "poly p z = 0"
        using poly_IVT[OF \<open>x>y\<close>, of p] \<open>poly p x * poly p y < 0\<close> 
        by (metis mult.commute)
      then have "z\<in>proots_within p s" 
        by (metis assms(3) assms(4) greaterThanLessThan_iff less_trans proots_withinI s_def)
      then show False using \<open>proots_within p s = {}\<close> by auto
    qed
    moreover have False if "y>x"
    proof -
      obtain z where "z>x" "z < y" "poly p z = 0"
        using poly_IVT[OF \<open>y>x\<close>, of p] \<open>poly p x * poly p y < 0\<close> by auto
      then have "z\<in>proots_within p s" 
        by (metis assms(3) assms(4) greaterThanLessThan_iff less_trans proots_withinI s_def)
      then show False using \<open>proots_within p s = {}\<close> by auto
    qed
    ultimately show False
      using \<open>x\<noteq>y\<close> by argo
  qed
qed auto

lemma sign_at_Polyalg_core:
  assumes valid:"valid_alg p lb ub"
  shows "sign_int_coeffs_at q (Polyalg p lb ub)
            = sign_at_Polyalg_core q p lb ub"
proof -
  define x where "x = real_of_alg_imp (Polyalg p lb ub)"
  define qq pp ll uu where "qq=map_poly real_of_int q" 
    and "pp=map_poly real_of_int p" and "ll = real_of_float lb" 
    and "uu = real_of_float ub"
  have x:"poly pp x = 0" "ll<x" "x<uu"
    using alg_bound_and_root[OF assms] unfolding pp_def x_def ll_def uu_def
    by auto
  then have "ll<uu" by auto
  

  have "sign_int_coeffs_at q (Polyalg p lb ub) = sign (poly qq x)"
    unfolding sign_int_coeffs_at_def pp_def qq_def x_def eval_poly_def by simp
  also have "... = sign_at_Polyalg_core q p lb ub"
  proof -
    have ?thesis when "p=q"
    proof -
      have "sign (poly qq x) = 0"
        using that \<open>poly pp x = 0\<close>  unfolding pp_def qq_def by auto
      also have "... = sign_at_Polyalg_core q p lb ub"  
        unfolding sign_at_Polyalg_core_def 
        using that by auto
      finally show ?thesis .
    qed
    moreover have ?thesis when "p\<noteq>q" "descartes_roots_test ll uu qq = 0"
    proof (cases "qq=0")
      case True
      then show ?thesis 
        using that
        unfolding sign_at_Polyalg_core_def ll_def uu_def qq_def by auto
    next
      case False
      define y where "y = real_of_float (mid_fl lb ub)"
      have "ll<y" "y<uu"
        using \<open>ll<uu\<close> unfolding y_def ll_def uu_def 
        by (meson float_int.r2.hom_less mid_fl_strict_between)+
      then have "y \<in> {ll<..<uu}" by auto
      moreover have "x \<in> {ll<..<uu}" 
        by (simp add: \<open>ll < x\<close> \<open>x < uu\<close>)
      moreover have "proots_within qq {ll<..<uu} = {}"
        using \<open>descartes_roots_test ll uu qq = 0\<close> False \<open>ll < uu\<close>
        by (meson descartes_roots_test_zero ex_in_conv 
            greaterThanLessThan_iff proots_within_iff)
      ultimately have "sign (poly qq x) = sign (poly qq y)"
        using same_sign_no_root[of qq ll uu x y] by auto
      then show ?thesis unfolding sign_at_Polyalg_core_def y_def eval_poly_def qq_def
        using that[unfolded ll_def uu_def qq_def]
        by (simp add: float_int.map_poly_R_hom_commute)
    qed
    moreover have ?thesis when "p\<noteq>q" "descartes_roots_test ll uu qq \<noteq> 0"
    proof -
      have "sign (poly qq x) = taq {Alg p lb ub} (of_int_poly q)"
        unfolding qq_def x_def taq_def by simp
      also have "... = taq {x::real. poly pp x = 0 \<and> lb < x \<and> x < ub} qq"
      proof -
        have "{Alg p lb ub} = {x. poly pp x = 0 \<and> lb < x \<and> x < ub}"
          using x  alg_eq[OF valid] unfolding ll_def uu_def x_def pp_def
          by (smt (verit, del_insts) Collect_cong singleton_conv)
        then show ?thesis unfolding pp_def qq_def by simp
      qed
      also have "... = changes_itv_smods (real_of_float lb) (real_of_float ub) (of_int_poly p)
         (pderiv (of_int_poly p) * of_int_poly q)"  unfolding pp_def qq_def
        apply (rule sturm_tarski_interval)
        using valid unfolding valid_alg_def 
        by (auto simp add: float_int.map_poly_R_hom_commute ll_def uu_def)
      also have "... = changes_itv_smods (real_of_float lb) (real_of_float ub) (of_int_poly p)
         (of_int_poly ((pderiv p) *  q))"
        by (simp add: of_int_hom.map_poly_pderiv of_int_poly_hom.hom_mult)
      also have "... = fi_changes_itv_spmods lb ub p (pderiv p * q)"
        using float_int.changes_spmods_smods(1) by simp
      finally have "sign (poly qq x) 
          = fi_changes_itv_spmods lb ub p (pderiv p * q)" .
      then show ?thesis 
        using that unfolding sign_at_Polyalg_core_def ll_def uu_def qq_def
        by auto
    qed
    ultimately show ?thesis by auto
  qed
  finally show ?thesis .
qed

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
      sign_at_Polyalg_core q p lb ub
    else Code.abort (STR ''Invalid sgn_at'') 
        (\<lambda>_. sign_int_coeffs_at q (Polyalg p lb ub))
    )"
  using sign_at_Polyalg_core by force

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