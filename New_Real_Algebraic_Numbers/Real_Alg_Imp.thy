theory Real_Alg_Imp imports 
  Complex_Main
  "../Sturm_Tarski/Pseudo_Remainder_Sequence"
  "Polynomial_Interpolation.Ring_Hom_Poly"
  "../Budan_Fourier/Descartes_Roots_Test"
  Float_Misc
begin

section \<open>Cauchy sequences for the reals\<close>

abbreviation "Real \<equiv> Real.Real"
abbreviation "cauchy \<equiv> Real.cauchy"
abbreviation "vanishes \<equiv> Real.vanishes"

fun to_cauchy:: "rat poly \<times> rat \<times> rat \<Rightarrow> nat \<Rightarrow> rat" where
  "to_cauchy (_, lb, ub) 0 = (lb+ub)/2"|
  "to_cauchy (p, lb, ub) (Suc n) = (
    let c=(lb+ub)/2
    in if  poly p lb * poly p c \<le>0 then to_cauchy (p, lb, c) n
                                    else to_cauchy (p, c, ub) n)"

lemma to_cauchy_bound_aux:
  fixes p::"rat poly"
  assumes "lb<ub"
  defines "X\<equiv>to_cauchy (p,lb,ub)"
  shows "lb< X n \<and> X n<ub" using assms(1) unfolding X_def 
proof (induct n arbitrary:lb ub)
  case 0
  thus ?case by auto
next
  case (Suc n) 
  define c where "c\<equiv>(lb+ub)/2"
  have "c>lb" and "c<ub" using `lb<ub` unfolding c_def by auto thm Suc.hyps[OF `c>lb`]
  hence "lb<to_cauchy (p, lb, c) n" and "to_cauchy (p, lb, c) n<ub" 
      and "lb < to_cauchy (p, c, ub) n" and "to_cauchy (p, c, ub) n<ub"
    using Suc.hyps[OF `c>lb`] Suc.hyps[OF `c<ub`] by auto
  thus ?case 
    by (cases "poly p lb * poly p c \<le>0",auto simp add:c_def)
qed

lemma to_cauchy_converge:
  fixes p::"rat poly"
  assumes "lb<ub"  
  defines "X\<equiv>to_cauchy (p,lb,ub)"
  shows "\<bar> X (i+1) - X i\<bar> < (ub - lb) / 2^(i+1)" unfolding X_def using `lb<ub`
proof (induct i arbitrary:lb ub)
  case 0
  thus ?case by (auto simp add:Let_def field_simps)
next
  case (Suc n)
  define r where "r\<equiv>(lb+ub)/2"
  hence "r>lb" and "r<ub" using `lb<ub` by auto
  show ?case (is "?L<?R")
  proof (cases "poly p lb * poly p r \<le>0")
    case True
    hence "?L=\<bar>to_cauchy (p, lb, r) (n + 1) - to_cauchy (p, lb, r) n\<bar>" 
      by (simp add:Let_def r_def)
    also have "...< (r - lb) / 2 ^ (n + 1)"
      using Suc.hyps[OF `lb<r`] .
    also have "... =  ?R"
      unfolding r_def by (auto simp add:field_simps)
    finally show ?thesis .
  next
    case False
    hence "?L=\<bar>to_cauchy (p, r, ub) (n + 1) - to_cauchy (p, r, ub) n\<bar>" 
      by (simp add:Let_def r_def)
    also have "...< (ub - r) / 2 ^ (n + 1)"
      using Suc.hyps[OF `r<ub`] .
    also have "... =  ?R"
      unfolding r_def by (auto simp add:field_simps)
    finally show ?thesis .
  qed
qed

lemma power_Archimedean:
  fixes x::"rat"
  assumes "x>0" "a>1"
  shows "\<forall>y. \<exists>n. y < a^n * x" 
proof (rule,case_tac "y>0")
  fix y::rat  assume "\<not> 0 < y" 
  thus " \<exists>n. y < a ^ n * x" using assms 
    apply (rule_tac x=0 in exI)
    by auto
next
  fix y::rat assume "y>0" 
  obtain n::nat where "n> log (of_rat a) (of_rat (y/x))" 
    using reals_Archimedean2 by blast
  hence  "(of_rat a) powr n > (of_rat a) powr (log (of_rat a) (of_rat (y/x)))" 
    by (intro powr_less_mono,auto simp add:`a>1`)
  hence "a ^ n > y/x"  using `y>0` `x>0` `a>1`
    apply (subst (asm) powr_realpow,simp)
    apply (subst (asm) powr_log_cancel,auto)
    apply (subst (asm) of_rat_power[symmetric])
    by (simp add:of_rat_less)
  thus "\<exists>n. y < a ^ n * x" by (auto simp add:field_simps `x>0`)
qed

lemma to_cauchy_cauchy:
  fixes p::"rat poly"
  assumes "lb<ub"
  defines "X\<equiv>to_cauchy (p,lb,ub)"
  shows "cauchy X"
proof (rule Real.cauchyI)
  fix r::rat assume "r>0"
  define d where "d\<equiv>ub-lb"
  hence "d>0" using `lb<ub` by simp
  obtain k::nat where k:"2*d/2^k<r" 
    using power_Archimedean[OF `r>0`,of 2,simplified] by (auto simp add:field_simps)
  { fix m n::nat assume "m>n"
    hence "\<bar>X m - X n\<bar> < (d/2^n - d/2^m)" 
    proof (induct "m - n" arbitrary:m n)  
      case 0
      thus ?case by simp
    next
      case (Suc diff) print_cases
      have "\<bar>X m - X n\<bar> \<le> \<bar>X m - X (m - 1)\<bar> + \<bar>X (m - 1) - X n\<bar>" by auto
      also have "... \<le> \<bar>X m - X (m - 1)\<bar> + (d / 2 ^ n - d / 2 ^ (m - 1))"
        using Suc.hyps(1)[of "m - 1" n] Suc(2,3) by (cases "n=m - 1",simp,force)
      also have "... <  d / 2 ^ m + (d / 2 ^ n - d / 2 ^ (m - 1))"      
        using to_cauchy_converge[OF `lb<ub`,of p "m - 1", folded X_def d_def] `m>n` by auto
      also have "... = (d / 2 ^ n - d / 2 ^ m)"
        by (auto simp add:field_simps, metis Suc.prems Suc_pred not_gr0 not_less0 power_Suc)          
      finally show ?case .
    qed }
  note diff=this
  have "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X m - X n\<bar> < r" 
  proof (rule+)
    fix m n assume "k \<le> m" "k \<le> n"
    have "\<bar>X m - X n\<bar> \<le> \<bar>d / 2 ^ n - d / 2 ^ m\<bar>"
      by (cases rule:linorder_cases[of m n], (drule diff|auto)+)
    also have "... \<le> \<bar>d / 2 ^ n\<bar> + \<bar>d / 2 ^ m\<bar>" by linarith
    also have "... = (d / 2 ^ n + d / 2 ^ m)" 
      using \<open>d>0\<close> by fastforce
    also have "... \<le> 2 *d / 2^k"
    proof -
      have "d / 2 ^ n \<le> d / 2 ^ k" and "d / 2 ^ m \<le> d / 2 ^ k"
        using `k\<le>n` `k\<le>m` order.strict_implies_order[OF `d>0`]
         by (intro divide_left_mono,auto)+
      thus ?thesis by auto
    qed
    also have "...<r" using k .
    finally show "\<bar>X m - X n\<bar> < r" .
  qed
  thus "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X m - X n\<bar> < r" by auto
qed

lemma to_cauchy_bound:
  fixes p::"rat poly" and lb ub ::rat
  defines "X\<equiv>to_cauchy (p,lb,ub)"
  assumes "lb<ub" 
  shows "of_rat lb\<le> Real X" "Real X\<le>of_rat ub" 
using le_RealI Real_leI  to_cauchy_cauchy[OF `lb<ub`,of p, folded X_def]
  to_cauchy_bound_aux[OF `lb<ub`,of p,folded X_def]
by (metis less_eq_rat_def of_rat_less_eq)+

lemma "Real.vanishes X \<Longrightarrow> Real.cauchy X \<Longrightarrow> Real.Real X = 0" 
by (metis (poly_guards_query) cauchy_diff diff_Real diff_self eq_Real vanishes_diff)

lemma cauchy_imp_poly_cauchy:
  assumes "Real.cauchy X"
  shows "Real.cauchy (\<lambda>i. poly p (X i))"
by (induct p,auto intro!: Real.cauchy_add Real.cauchy_mult simp add: assms)

lemma real_poly_eq_poly_real:
  fixes p::"rat poly"
  assumes "Real.cauchy X"
  shows "Real.Real (\<lambda>i. poly (map_poly of_rat p) (X i)) 
              = poly (map_poly of_rat p) (Real.Real X)"
proof (induct p)
  case 0
  thus ?case by (simp add:zero_real_def)
next
  case (pCons a p)
  let ?mp = "map_poly of_rat"
  have "Real (\<lambda>i. poly (?mp (pCons a p)) (X i)) = Real (\<lambda>i. a + X i * poly p (X i))"
    by simp
  also have "... = Real (\<lambda>i. a) + Real (\<lambda>i. X i * poly p (X i))"
    apply (subst Real.add_Real[symmetric])
    by (auto simp add: assms cauchy_imp_poly_cauchy)
  also have "... = Real (\<lambda>i. a) + Real X * Real (\<lambda>i. poly p (X i)) "
    apply (subst Real.mult_Real[symmetric])
    using assms by (auto simp add: cauchy_imp_poly_cauchy)
  also have "... = Real (\<lambda>i. a) + Real X * poly (?mp p) (Real X)"
    using pCons by simp
  also have "... = poly (map_poly real_of_rat (pCons a p)) (Real X)"
    unfolding of_rat_hom.map_poly_pCons_hom
    by (simp add: of_rat_Real)
  finally show ?case .
qed

lemma vanishes_imp_cauchy:
  assumes "Real.vanishes X"  
  shows "Real.cauchy X" unfolding Real.cauchy_def 
proof (rule,rule)
  fix r::rat assume "0 < r"
  then obtain k where k:"\<forall>n\<ge>k. \<bar>X n\<bar> < r / 2" 
    using assms[unfolded Real.vanishes_def,THEN spec,of "r/2"] by auto
  { fix m n assume "m\<ge>k" "n\<ge>k"
    have "\<bar>X m - X n\<bar> \<le> \<bar>X m\<bar> + \<bar>X n\<bar>" by simp
    also have "... <r/2 + r/2" using k `m\<ge>k` `n\<ge>k` 
      by (metis add_mono_thms_linordered_field(5))
    also have "... = r" by simp
    finally have "\<bar>X m - X n\<bar> < r" . }
  thus "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X m - X n\<bar> < r" by auto
qed

lemma power2_valishes:
  assumes "r>0"
  shows "vanishes (\<lambda>i. r/2^i)"
proof (rule vanishesI)
  fix \<epsilon>::rat assume "\<epsilon>>0"
  obtain k::nat where k:"r/2^k<\<epsilon>" 
    using power_Archimedean[THEN spec,of \<epsilon> 2 "r",OF `\<epsilon>>0`] by (auto simp add:field_simps)
  { fix n assume "n\<ge>k"
    hence "r/2^n \<le> r/2^k" using `r>0` by (auto simp add:field_simps)
    hence "r/2^n < \<epsilon>" using k by auto }
  thus " \<exists>k. \<forall>n\<ge>k. \<bar>r / 2 ^ n\<bar> < \<epsilon>" using `r>0` by auto
qed
 
lemmas power2_cauchy = power2_valishes[THEN vanishes_imp_cauchy]

lemma to_cauchy_root:
  fixes p::"rat poly"
  assumes "lb<ub" "poly p lb * poly p ub \<le> 0"
  defines "X\<equiv>to_cauchy (p,lb,ub)" 
  shows "poly (map_poly of_rat p) (Real X) = 0" using assms(2)
proof -
  define r where "r\<equiv>(ub-lb)/2"
  hence "r>0" and cauchy_X:"Real.cauchy X" 
    unfolding X_def  using to_cauchy_cauchy `lb<ub` by auto
  { fix i
    have "poly p (X i+r/2^i) * poly p (X i - r/2^i) \<le>0" 
        unfolding r_def X_def using assms(2)
      proof (induct i arbitrary:lb ub) 
        case 0
        thus ?case unfolding X_def r_def by (simp add:field_simps)
      next
        case (Suc n)
        have "poly p lb * poly p ((lb+ub)/2) \<le> 0 \<Longrightarrow> ?case"
          by (frule Suc.hyps,auto simp add:Let_def field_simps)
        moreover have "\<not> poly p lb * poly p ((lb+ub)/2) \<le> 0 \<Longrightarrow> poly p ((lb+ub)/2) * poly p ub \<le> 0" 
          using Suc.prems unfolding not_le
          apply (unfold mult_le_0_iff zero_less_mult_iff)
          by auto
        hence "\<not> poly p lb * poly p ((lb+ub)/2) \<le> 0 \<Longrightarrow> ?case"
            by (frule Suc.hyps,auto simp add:Let_def field_simps)
        ultimately show ?case by blast
      qed }
  hence "Real (\<lambda>i. poly p (X i+r/2^i) * poly p (X i - r/2^i)) \<le>0"
    using power2_cauchy[OF `r>0`] cauchy_X
    by (auto intro!: Real_leI cauchy_mult cauchy_imp_poly_cauchy cauchy_add to_cauchy_cauchy )
  hence "poly (map_poly of_rat p) (Real (\<lambda>i. X i+r/2^i)) 
          * poly (map_poly of_rat p) (Real (\<lambda>i. X i - r/2^i)) \<le>0"
    using power2_cauchy[OF `r>0`] cauchy_X
    apply (subst (asm) Real.mult_Real[symmetric]) 
    subgoal by (simp add: cauchy_imp_poly_cauchy)
    subgoal by (simp add: cauchy_imp_poly_cauchy)
    subgoal using real_poly_eq_poly_real by auto
    done
  moreover have "Real (\<lambda>i. X i+r/2^i) = Real X" and "Real (\<lambda>i. X i-r/2^i) = Real X"
    using cauchy_X power2_valishes power2_cauchy `r>0`
    by (subst Real.eq_Real,auto intro:vanishes_minus)+
  ultimately have "poly (map_poly of_rat p) (Real X) 
                        * poly (map_poly of_rat p) (Real X) \<le>0" 
    by auto
  thus ?thesis by (metis linorder_neqE_linordered_idom mult_le_0_iff not_less)
qed

lemma to_cauchy_bound':
  fixes p::"rat poly" and lb ub ::rat
  defines "X\<equiv>to_cauchy (p,lb,ub)"
  assumes "lb<ub" and sgn_diff:"poly p lb * poly p ub<0"
  shows "of_rat lb< Real X" "Real X < of_rat ub"
proof -
  define x where"x=Real X"
  have "poly (map_poly of_rat p) x=0" using to_cauchy_root[OF `lb<ub`, of p] sgn_diff 
    apply (fold X_def x_def)
    by auto
  hence "x\<noteq>of_rat lb" "x\<noteq>of_rat ub" using sgn_diff by auto
  moreover have "of_rat lb\<le>x" and "x\<le>of_rat ub" 
    using to_cauchy_bound[OF `lb<ub`] unfolding x_def X_def by auto
  ultimately show "of_rat lb< Real X" "Real X < of_rat ub" unfolding x_def by auto
qed

section \<open>Validity checks for representations of real algebraic numbers\<close>

(*
definition one_root_btw::"int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "one_root_btw p lb ub = (card {x. poly (map_poly real_of_int p) x=0 \<and> lb<x \<and> x<ub} = 1)"
*)

definition one_root_test::"int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "one_root_test p lb ub = (descartes_roots_test lb ub (map_poly real_of_int p) = 1)"

term descartes_roots_test

(*
definition valid_alg::"int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "valid_alg p lb ub = (lb<ub \<and> poly (of_int_poly p) lb * poly (of_int_poly p) ub <0 
    \<and> one_root_btw (map_poly of_int p) lb ub)"
*)

definition valid_alg::"int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "valid_alg p lb ub = (lb<ub \<and> poly (of_int_poly p) lb 
      * poly (of_int_poly p) ub <0 
    \<and> one_root_test p lb ub)"

lemma valid_alg_code[code]: 
  "valid_alg p lb ub = (lb<ub \<and> sgn (eval_poly of_int p lb) 
      * sgn (eval_poly of_int p ub) <0 \<and> one_root_test p lb ub)"
proof -
  have "poly (of_int_poly p) lb * poly (of_int_poly p) ub <0  
        \<longleftrightarrow> sgn (eval_poly of_int p lb) * sgn (eval_poly of_int p ub) <0"
    unfolding eval_poly_def by (metis sgn_less sgn_mult)
  then show ?thesis unfolding valid_alg_def by auto
qed

global_interpretation float_int:hom_pseudo_smods float_of_int real_of_int real_of_float
  defines 
    fi_changes_hpoly_at  = float_int.changes_hpoly_at and
    fi_changes_itv_spmods = float_int.changes_itv_spmods and
    fi_changes_gt_spmods = float_int.changes_gt_spmods and
    fi_changes_le_spmods = float_int.changes_le_spmods and
    fi_changes_R_spmods = float_int.changes_R_spmods
  apply unfold_locales
  apply (simp_all add: of_rat_less of_rat_less_eq)
  using real_of_float_eq by force

global_interpretation rat_float:hom_pseudo_smods rat_of_float real_of_float real_of_rat
  apply unfold_locales
  by (simp_all add: of_rat_less of_rat_less_eq rat_of_float_add rat_of_float_mult)
  
section \<open>Representation of a real algebraic number\<close>

definition Alg:: "int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> real" where
  [code del]:"Alg p lb ub = (if valid_alg p lb ub
                    then Real (to_cauchy (map_poly of_int p,rat_of_float lb,rat_of_float ub))
                    else undefined)"

lemma alg_bound_and_root:
  fixes p::"int poly" and lb ub::float
  assumes "valid_alg p lb ub"
  shows "lb<Alg p lb ub" and "Alg p lb ub<ub" and "poly (of_int_poly p) (Alg p lb ub) = 0"
proof -
  let ?p = "of_int_poly p" 
  have less:"rat_of_float lb<rat_of_float ub" 
      and "poly ?p lb * poly ?p ub<0" 
      and "one_root_test p lb ub" 
    using assms unfolding valid_alg_def eval_poly_def
    apply auto
    by (metis rat_float.R_hom rat_float.r2.hom_less)
  define x where "x\<equiv>Alg p lb ub"
  hence x:"x= Real (to_cauchy (of_int_poly p, rat_of_float lb, rat_of_float ub))" 
    using assms Alg_def valid_alg_def by auto
  have "poly (of_int_poly p) (rat_of_float lb) * poly (of_int_poly p) (rat_of_float ub) \<le> 0"
  proof -
    have "rat_of_float (poly (of_int_poly p) lb * poly (of_int_poly p) ub) < 0"
      using \<open>poly ?p lb * poly ?p ub<0\<close> by (simp add: rat_float.r2.hom_less)
    then have "poly (of_int_poly p) (rat_of_float lb) 
                    * poly (of_int_poly p) (rat_of_float ub) < 0"
      unfolding rat_of_float_mult
      by  (simp flip:rat_float.poly_map_poly add:map_poly_map_poly comp_def)
    then show ?thesis by auto
  qed
  from to_cauchy_root[OF _ this,folded x] less
  have "poly (map_poly real_of_rat (of_int_poly p)) x = 0"
    by simp
  then show "poly (of_int_poly p) x=0"
    by (simp add:map_poly_map_poly comp_def)
  then show "lb<x" and "x<ub"
    using to_cauchy_bound[OF less,of ?p,folded x] \<open>poly ?p lb * poly ?p ub<0\<close>
    by (metis float_int.map_poly_R_hom_commute float_int.r2.hom_0_iff le_less
        less_irrefl mult_eq_0_iff real_of_rat_of_float)+
qed

lemma card_1_imp_eq:"card S=1 \<Longrightarrow> x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> x=y" 
  by (metis One_nat_def card_eq_SucD singletonD)

lemma card_eq_count_leq_1:
  assumes "p\<noteq>0" "proots_count p s \<le> 1"
  shows "card (proots_within p s) = proots_count p s"
proof -
  have "card (proots_within p s) \<le> 1"
    using card_proots_within_leq[OF \<open>p\<noteq>0\<close>,of s] \<open>proots_count p s \<le> 1\<close>
    by auto
  then have "card (proots_within p s) = 0 \<or> card (proots_within p s) = 1"
    by auto
  moreover have ?thesis if "card (proots_within p s) = 0"
  proof -
    have "proots_within p s = {}"
      using that by (meson assms(1) card_0_eq finite_proots)
    then show ?thesis unfolding proots_count_def by auto
  qed
  moreover have ?thesis if "card (proots_within p s) = 1"
  proof -
    obtain a where "proots_within p s = {a}"
      using \<open>card (proots_within p s) = 1\<close> card_1_singletonE by blast
    then have "order a p = proots_count p s"
      unfolding proots_count_def by auto
    then have "order a p \<le> 1" using \<open>proots_count p s \<le> 1\<close> by auto
    moreover have "order a p\<noteq>0"
      using \<open>proots_within p s = {a}\<close> order_root \<open>p\<noteq>0\<close> unfolding proots_within_def
      by auto
    ultimately have "order a p=1" by auto
    then have "proots_count p s = 1"
      using \<open>order a p = proots_count p s\<close> by auto
    with that show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma alg_eq:
  assumes valid:"valid_alg p lb ub" and "poly (of_int_poly p) x = 0" and "x>lb" and "x<ub"
  shows "x=Alg p lb ub"
proof -
  define S where "S={x::real. poly (of_int_poly p) x = 0 \<and> lb < x \<and> x < ub}"
  have "card S  = 1" 
  proof -
    define ll uu pp where "ll=real_of_float lb" and "uu = real_of_float ub" 
                      and "pp=map_poly real_of_int p" 
    have "descartes_roots_test ll uu pp = 1" and "ll < uu" and "pp\<noteq>0"
      using valid unfolding valid_alg_def one_root_test_def ll_def uu_def pp_def 
      by auto
    then have "proots_count pp {x. ll < x \<and> x < uu} = 1"
      using descartes_roots_test_one by auto
    then have "card (proots_within pp {x. ll < x \<and> x <  uu})
                  = proots_count pp {x. ll < x \<and> x < uu}"
      using card_eq_count_leq_1[OF \<open>pp\<noteq>0\<close>] by auto
    also have "... = 1"
      using descartes_roots_test_one[OF \<open>pp\<noteq>0\<close> \<open>ll < uu\<close>] 
            \<open>descartes_roots_test ll uu pp = 1\<close>
      by auto
    finally have "card (proots_within pp {x. ll < x \<and> x < uu}) = 1" . 
    moreover have "proots_within pp {x. ll < x \<and> x < uu} = S"
      unfolding S_def pp_def ll_def uu_def proots_within_def 
      by auto
    ultimately show ?thesis by auto
  qed
  moreover have "x\<in>S" 
    using assms unfolding S_def by auto
  moreover have "Alg p lb ub\<in> S" 
    using alg_bound_and_root[OF valid] unfolding S_def by auto
  ultimately show ?thesis apply (elim card_1_imp_eq) by auto
qed

lemma valid_alg_deg:
  assumes valid:"valid_alg p lb ub"
  shows "degree p\<noteq>0"
proof (cases "p=0")
  case True
  thus ?thesis using valid by (auto simp add:valid_alg_def)
next
  case False
  have False when "degree p=0" 
  proof -
    obtain c where "p=[:c:]" "c\<noteq>0" using False 
      by (metis \<open>degree p = 0\<close> degree_eq_zeroE pCons_0_0)
    thus False using valid 
      using alg_bound_and_root(3) by fastforce
  qed
  thus ?thesis by auto
qed

datatype alg_imp =
     Floatalg float
   | Ratalg rat float float
   | Polyalg "int poly" float float  

fun real_of_alg_imp :: "alg_imp \<Rightarrow> real" where
  "real_of_alg_imp (Ratalg r _ _) = (Ratreal r)"|
  "real_of_alg_imp (Floatalg f) = real_of_float f"|
  "real_of_alg_imp (Polyalg p lb ub) = Alg p lb ub"

definition valid_Ratalg:: "rat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "valid_Ratalg r lb ub = (lb < of_rat r \<and> of_rat r < ub)"

fun valid_alg_imp :: "alg_imp \<Rightarrow> bool" where 
  "valid_alg_imp (Ratalg r lb ub) = valid_Ratalg r lb ub"
| "valid_alg_imp (Floatalg _ ) = True "
| "valid_alg_imp (Polyalg p lb ub) = valid_alg p lb ub" 

section \<open>A number between and upper/lower bounds of real algebraic numbers\<close>

definition mid_fl::"float \<Rightarrow> float \<Rightarrow> float" where
  "mid_fl a b = (a+b)*Float 1 (- 1)"

lemma mid_fl_strict_between[intro]:
  assumes "a<b" 
  shows "a < mid_fl a b" "mid_fl a b < b"
  using assms unfolding mid_fl_def by (auto simp:powr_neg_one)

fun btw_alg :: "alg_imp \<Rightarrow> alg_imp \<Rightarrow> alg_imp" where
   "btw_alg (Ratalg _ _ ub1) (Ratalg r2 lb2 _) = Floatalg (mid_fl ub1 lb2)"
 | "btw_alg (Ratalg _ _ ub1) (Floatalg f) = Floatalg (mid_fl ub1 f)"
 | "btw_alg (Ratalg _ _ ub1) (Polyalg p lb2 _) = Floatalg (mid_fl ub1 lb2)"
 | "btw_alg (Floatalg f) (Ratalg r2 lb2 _) = Floatalg (mid_fl f lb2)"
 | "btw_alg (Floatalg f1) (Floatalg f2) = Floatalg (mid_fl f1 f2)"
 | "btw_alg (Floatalg f) (Polyalg p lb2 _) = Floatalg (mid_fl f lb2)"
 | "btw_alg (Polyalg _ _ ub1) (Ratalg r2 lb2 _) = Floatalg (mid_fl ub1 lb2)"
 | "btw_alg (Polyalg _ _ ub1) (Floatalg f) = Floatalg (mid_fl ub1 f)"
 | "btw_alg (Polyalg _ _ ub1) (Polyalg p lb2 _) = Floatalg (mid_fl ub1 lb2)"

fun strict_less_alg_imp :: "alg_imp \<Rightarrow> alg_imp \<Rightarrow> bool" where
   "strict_less_alg_imp (Ratalg _ _ ub1) (Ratalg _ lb2 _) = (ub1 < lb2)"
 | "strict_less_alg_imp (Ratalg _ _ ub1) (Floatalg f) = (ub1 < f)"
 | "strict_less_alg_imp (Ratalg _ _ ub1) (Polyalg p lb2 _) = (ub1 < lb2)"
 | "strict_less_alg_imp (Floatalg f) (Ratalg r2 lb2 _) = (f < lb2)"
 | "strict_less_alg_imp (Floatalg f1) (Floatalg f2) = (f1 < f2)"
 | "strict_less_alg_imp (Floatalg f) (Polyalg p lb2 _) = (f < lb2)"
 | "strict_less_alg_imp (Polyalg _ _ ub1) (Ratalg r2 lb2 _) = (ub1 < lb2)"
 | "strict_less_alg_imp (Polyalg _ _ ub1) (Floatalg f) = (ub1 < f)"
 | "strict_less_alg_imp (Polyalg _ _ ub1) (Polyalg p lb2 _) = (ub1 < lb2)"

lemma alg_imp_less:
  assumes "valid_alg_imp a" "valid_alg_imp b" "strict_less_alg_imp a b"
  shows "real_of_alg_imp a < real_of_alg_imp b"
  using assms 
  apply (cases a;cases b)
  apply (auto simp:valid_Ratalg_def dest:alg_bound_and_root)
  using alg_bound_and_root(1) alg_bound_and_root(2) by fastforce

lemma btw_alg_between:
  assumes "valid_alg_imp a" "valid_alg_imp b" "strict_less_alg_imp a b"
  shows "real_of_alg_imp a < real_of_alg_imp (btw_alg a b)" 
        "real_of_alg_imp (btw_alg a b) < real_of_alg_imp b"
proof -
  show "real_of_alg_imp a < real_of_alg_imp (btw_alg a b)" 
  proof (cases a)
    case (Floatalg f)
    then show ?thesis 
      using assms
      by (cases b) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
  next
    case (Ratalg r1 lb1 ub1)
    then have "real_of_alg_imp a = real_of_rat r1" by auto
    also have "... < ub1"
      using Ratalg assms(1) valid_Ratalg_def valid_alg_imp.simps(1) by blast
    also have "... < real_of_alg_imp (btw_alg a b)"
      using Ratalg assms
      by (cases b) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
    finally show ?thesis .
  next
    case (Polyalg p1 lb1 ub1)
    then have  "real_of_alg_imp a < ub1" 
      using alg_bound_and_root(2) assms(1) by force
    also have "... < real_of_alg_imp (btw_alg a b)"
      using Polyalg assms
      by (cases b) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
    finally show ?thesis .
  qed
    
  show "real_of_alg_imp (btw_alg a b) < real_of_alg_imp b"
  proof (cases b)
    case (Floatalg f)
    then show ?thesis 
      using assms
      by (cases a) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
  next
    case (Ratalg r1 lb1 ub1)
    then have "real_of_alg_imp (btw_alg a b) < lb1"
      using assms
      by (cases a)  (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
    also have "... < real_of_alg_imp b"
      using Ratalg assms(2) valid_Ratalg_def by auto
    finally show ?thesis .
  next
    case (Polyalg p1 lb1 ub1)
    then have "real_of_alg_imp (btw_alg a b) < lb1"
      using assms
      by (cases a) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
    also have "... < real_of_alg_imp b"
      using Polyalg alg_bound_and_root(1) assms(2) by auto
    finally show ?thesis .
  qed
qed

lemma btw_alg_imp_between:
  assumes "strict_less_alg_imp a b"
  shows "strict_less_alg_imp a (btw_alg a b)" 
        "strict_less_alg_imp (btw_alg a b) b"
  subgoal using assms
    by (cases a;cases b) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
  subgoal using assms
    by (cases a;cases b) (auto simp flip:float_int.r2.hom_less simp del:less_float.rep_eq)
  done

lemma valid_btw_alg:
  assumes "valid_alg_imp a" "valid_alg_imp b"
  shows "valid_alg_imp (btw_alg a b)"
  using assms by (cases a;cases b) auto

fun upper_alg :: "alg_imp \<Rightarrow> alg_imp" where 
  "upper_alg (Ratalg _ _ ub1) = Floatalg (ub1+1)"
| "upper_alg (Floatalg f) = Floatalg (f+1)"
| "upper_alg (Polyalg _ _ ub1) = Floatalg (ub1+1)"

fun lower_alg :: "alg_imp \<Rightarrow> alg_imp" where 
  "lower_alg (Ratalg _ lb1 _) = Floatalg (lb1 - 1)"
| "lower_alg (Floatalg f) = Floatalg (f-1)"
| "lower_alg (Polyalg _ lb1 _) = Floatalg (lb1 - 1)"

lemma valid_upper_alg:"valid_alg_imp x \<Longrightarrow> valid_alg_imp (upper_alg x)"
  by (cases x) auto

lemma valid_lower_alg:"valid_alg_imp x \<Longrightarrow> valid_alg_imp (lower_alg x)"
  by (cases x) auto

lemma upper_alg_less_imp:"valid_alg_imp x 
        \<Longrightarrow> strict_less_alg_imp x (upper_alg x)"
  by (cases x) auto

lemma lower_alg_less_imp:"valid_alg_imp x 
        \<Longrightarrow> strict_less_alg_imp (lower_alg x) x"
  by (cases x) auto

lemma upper_alg_less:"valid_alg_imp x 
        \<Longrightarrow> real_of_alg_imp x < real_of_alg_imp (upper_alg x)"
  apply (cases x) 
  by (auto simp:valid_Ratalg_def add.commute alg_bound_and_root(2) pos_add_strict)

lemma lower_alg_less:"valid_alg_imp x 
        \<Longrightarrow> real_of_alg_imp (lower_alg x) < real_of_alg_imp x"
  apply (cases x) 
  apply (auto simp:valid_Ratalg_def)
  using alg_bound_and_root(1) by force



end