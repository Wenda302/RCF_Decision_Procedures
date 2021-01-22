(* 
    Real Algebraic Numbers
    Author:     Wenda Li, University of Cambridge
*)


theory RealAlg_Imp 
  imports  
    "../Sturm_Tarski/Sturm_Tarski"
    More_PolyMisc
    Bivariate_Poly
begin
  
text \<open>In this theory, we define a pseudo-constructor for real algebraic numbers and provide
  an efficient procedure to evaluate the sign of univariate and bivaraite polynomials at real algebraic points.\<close>

section{*of_float_poly*}

definition of_float_poly:: "float poly \<Rightarrow> real poly" where
 "of_float_poly = map_poly real_of_float"

lemma coeff_of_float_poly:"coeff (of_float_poly p)  = real_of_float o (coeff p)" 
  unfolding of_float_poly_def comp_def
  using coeff_map_poly zero_float.rep_eq by blast

lemma of_float_poly_0[simp]:"of_float_poly 0 = 0" 
  unfolding of_float_poly_def by simp

lemma of_float_poly_1[simp]:"of_float_poly 1 = 1" 
  unfolding of_float_poly_def by simp
  
lemma of_float_poly_eq_iff[simp]:"of_float_poly p = of_float_poly q \<longleftrightarrow> p = q" 
  unfolding  poly_eq_iff
  by (auto simp add:coeff_of_float_poly real_of_float_eq)     

lemma of_float_poly_eq_0_iff [simp]: "(of_float_poly a = 0) = (a = 0)"
  using of_float_poly_eq_iff [of _ 0] by simp

lemma zero_eq_of_float_poly_iff [simp]: "(0 = of_float_poly a) = (0 = a)"
  by simp

lemma of_float_poly_eq_1_iff [simp]: "(of_float_poly a = 1) = (a = 1)"
  by (metis of_float_poly_1 of_float_poly_eq_iff)

lemma one_eq_of_float_poly_iff [simp]: "(1 = of_float_poly a) = (1 = a)"
  by simp

lemma of_float_poly_pCons[simp]:"of_float_poly (pCons a p) = pCons (real_of_float a) (of_float_poly p)" 
  unfolding of_float_poly_def
  apply (cases "a\<noteq>0 \<or> p\<noteq>0")
  by (auto simp add:map_poly_pCons)
    
lemma of_float_poly_plus[simp]: "of_float_poly (p + q) = of_float_poly p +  of_float_poly q" 
  using Rat.of_rat_add
  by (auto simp add: poly_eq_iff coeff_of_float_poly)

lemma of_float_poly_smult[simp]:"of_float_poly (smult s p) = smult (real_of_float s) (of_float_poly p)" 
  using Int.of_int_mult 
  by (auto simp add: poly_eq_iff coeff_of_float_poly)

lemma of_float_poly_mult[simp]:"of_float_poly (p*q) = of_float_poly p * of_float_poly q"
  apply (induct p,intro poly_eqI)
  by auto

lemma of_float_poly_pcompose[simp]: "of_float_poly (pcompose p q) = pcompose (of_float_poly p) (of_float_poly q)"
  apply (induct p)
  by (auto simp add:pcompose_pCons)

lemma of_float_poly_degree[simp]:"degree (of_float_poly p) = degree p"
  by (induct p,auto)

lemma of_float_poly_poly:
  "real_of_float (poly p x) = poly (of_float_poly p) (real_of_float x)" 
apply (induct p)
by auto

lemma of_float_poly_monom:
  "of_float_poly (monom x n) = monom (real_of_float x) n"
apply (induct n)
by (auto simp add:monom_0 monom_Suc)

lemma of_float_lead_coeff[simp]: "real_of_float (lead_coeff p) = lead_coeff (of_float_poly p)" 
  by (simp add: coeff_of_float_poly) 

lemma of_float_poly_pseudo_divmod_iff:
  "pseudo_divmod f g = (q,r) 
      \<longleftrightarrow> pseudo_divmod (of_float_poly f) (of_float_poly g) = (of_float_poly q,of_float_poly r)" 
  (is "?L \<longleftrightarrow> ?R")
proof (cases "g=0")
  case True
  then show ?thesis by auto
next
  case False
  define a where "a=(lead_coeff g) ^ (Suc (degree f) - degree g)"
  define a' where "a'=(lead_coeff (of_float_poly g)) ^ (Suc (degree f) - degree g)"
  have ?R when ?L
  proof -
    obtain q' r' where qr':"pseudo_divmod (of_float_poly f) (of_float_poly g) = (q',r')" 
      by fastforce
    have "smult a f = g * q + r" and deg: "r = 0 \<or> degree r < degree g"
      using pseudo_divmod[OF False that] unfolding a_def by auto
    have "smult a' (of_float_poly f) = (of_float_poly g) * (of_float_poly q) 
        + (of_float_poly r)" 
    proof -
      have "of_float_poly (smult a f) = of_float_poly (g * q + r)"
        using \<open>smult a f = g * q + r\<close> by simp
      then show ?thesis unfolding a_def a'_def by auto
    qed
    moreover have "smult a' (of_float_poly f) = (of_float_poly g) * q' + r'" 
        and deg': "r' = 0 \<or> degree r' < degree g"
      using pseudo_divmod[OF _ qr'] False unfolding a'_def 
      by auto
    ultimately have "(q'-of_float_poly q) * (of_float_poly g) = (of_float_poly r - r')"
      by (auto simp add:algebra_simps)
    then have "q'-of_float_poly q = 0 \<and> of_float_poly r - r' = 0" 
      apply (elim degree_less_timesD) 
      subgoal 
        by (metis deg deg' degree_diff_less diff_self of_float_poly_0 of_float_poly_degree)  
      using False by auto
    then show ?thesis using qr' by auto
  qed
  moreover have ?L when ?R
  proof -
    obtain q' r' where qr':"pseudo_divmod f g = (q',r')" 
      by fastforce
    have "of_float_poly g \<noteq> 0" using False by auto
    from pseudo_divmod[OF this that]
    have "smult a' (of_float_poly f) = (of_float_poly g) * (of_float_poly q) + (of_float_poly r)" 
        and deg: "r = 0 \<or> degree r < degree g"
      unfolding a'_def by auto
    moreover have "smult a f = g * q' + r'" and deg': "r' = 0 \<or> degree r' < degree g"  
      using pseudo_divmod[OF False qr'] unfolding a_def by auto
    then have "of_float_poly (smult a f) = of_float_poly (g * q' + r')"
      by simp
    then have "smult a' (of_float_poly f) 
        = (of_float_poly g) * (of_float_poly q') + (of_float_poly r')"
      unfolding a_def a'_def by auto
    ultimately have "(of_float_poly q'-of_float_poly q) * (of_float_poly g) 
        = (of_float_poly r - of_float_poly r')"
      by (auto simp add:algebra_simps)
    then have "of_float_poly q'-of_float_poly q = 0 \<and> of_float_poly r - of_float_poly r' = 0" 
      apply (elim degree_less_timesD) 
      subgoal by (metis deg deg' degree_0 degree_diff_less diff_zero not_gr_zero 
            not_less_zero of_float_poly_0 of_float_poly_degree)
      using False by auto
    then show ?thesis using qr' by auto
  qed
  ultimately show ?thesis by auto
qed
  
lemma of_float_poly_pseudo_mod:
  "of_float_poly (pseudo_mod p q) = pseudo_mod (of_float_poly p) (of_float_poly q)"
  unfolding pseudo_mod_def using of_float_poly_pseudo_divmod_iff
  by (metis prod.collapse snd_conv)

lemma of_float_poly_pderiv:
  "of_float_poly (pderiv p) = pderiv (of_float_poly p)"
  apply (induct p)
  by (auto simp add:pderiv_pCons)

lemma of_float_int_poly[simp]: "of_float_poly (of_int_poly p) = of_int_poly p"
  apply (induct p)
  by auto

lemma [code abstract]: "coeffs (of_float_poly p) =  (map real_of_float (coeffs p))" 
  apply (induct p)
  apply (auto simp add: real_of_float_eq)
  by (simp add: cCons_def)

declare of_float_poly_def[symmetric,simp]

section{*pseudo remainder sequence*}

function spmods :: "'a::idom poly \<Rightarrow> 'a poly \<Rightarrow> ('a poly) list" where
  "spmods p q= (if p=0 then [] else 
      let 
        m=(if even(degree p+1-degree q) then -1 else -lead_coeff q) 
      in     
        Cons p (spmods q (smult m (pseudo_mod p q))))"
by auto
termination
 apply (relation "measure (\<lambda>(p,q).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
 apply simp_all
 apply (metis pseudo_mod)
done

lemma spmods_0[simp]:
  "spmods 0 q = []"
  "spmods p 0 = (if p=0 then [] else [p])"
by auto

lemma spmods_nil_eq:"spmods p q = [] \<longleftrightarrow> (p=0)"
  by (metis list.distinct(1) spmods.elims)

lemma changes_poly_at_alternative: 
  "changes_poly_at ps a= changes (map (\<lambda>p. sgn(poly p a)) ps)" 
unfolding changes_poly_at_def
apply (subst  Sturm_Tarski.changes_map_sgn_eq)
by (auto simp add:comp_def)

lemma smods_smult_length: 
  assumes "a\<noteq>0" "b\<noteq>0"
  shows "length (smods p q) = length (smods (smult a p) (smult b q))" using assms
proof (induct "smods p q"  arbitrary:p q a b )
  case Nil
  thus ?case by (simp split:if_splits)
next
  case (Cons x xs)
  hence "p\<noteq>0" by auto
  define r where "r\<equiv>- (p mod q)"
  have "smods q r = xs" using Cons.hyps(2) `p\<noteq>0` unfolding r_def by auto
  hence "length (smods q r) = length (smods (smult b q) (smult a r))"
    using Cons.hyps(1)[of q r b a] Cons by auto
  moreover have "smult a p\<noteq>0" using `a\<noteq>0` `p\<noteq>0` by auto
  moreover have "-((smult a p) mod (smult b q)) = (smult a r)" 
    using Polynomial.mod_smult_left Polynomial.mod_smult_right[OF `b\<noteq>0`]
    unfolding r_def by simp
  ultimately show ?case
    unfolding r_def by auto
qed

lemma smods_smult_nth[rule_format]:
  fixes p q::"real poly"
  assumes "a\<noteq>0" "b\<noteq>0"
  defines "xs\<equiv>smods p q" and "ys\<equiv>smods (smult a p) (smult b q)"
  shows "\<forall>n<length xs. ys!n = (if even n then smult a (xs!n)  else smult b (xs!n))" using assms
proof (induct "smods p q"  arbitrary:p q a b xs ys)
  case Nil
  thus ?case by (simp split:if_splits)
next
  case (Cons x xs)
  hence "p\<noteq>0" by auto
  define r where "r\<equiv>- (p mod q)"
  have xs:"xs=smods q r" "p#xs=smods p q" using Cons.hyps(2) `p\<noteq>0` unfolding r_def by auto
  define ys where "ys\<equiv>smods (smult b q) (smult a r)"
  have "- ((smult a p) mod (smult b q)) = smult a r" 
    using mod_smult_right[OF `b\<noteq>0`, of "smult a p" q,unfolded mod_smult_left[where y=q]]
    unfolding r_def by auto
  hence ys:"smult a p # ys = smods (smult a p) (smult b q)" using `p\<noteq>0` `a\<noteq>0` 
    unfolding ys_def r_def by auto
  have hyps:"\<And>n. n<length xs \<Longrightarrow> ys ! n = (if even n then smult b (xs ! n) else smult a (xs ! n))"
    using Cons.hyps(1)[of q r b a,folded xs ys_def] `a\<noteq>0` `b\<noteq>0` by auto
  thus ?case
    apply (fold xs ys)
    apply auto
    by (case_tac n,auto)+
qed

lemma smods_smult_sgn_map_eq:
  fixes x::real
  assumes "m>0"
  defines "f\<equiv>\<lambda>p. sgn(poly p x)"
  shows "map f (smods p (smult m q)) = map f (smods p q)"
        "map sgn_pos_inf (smods p (smult m q)) = map sgn_pos_inf (smods p q)"
        "map sgn_neg_inf (smods p (smult m q)) = map sgn_neg_inf (smods p q)"
proof -
  define xs ys where "xs\<equiv>smods p q" and "ys\<equiv>smods p (smult m q)" 
  have "m\<noteq>0" using `m>0` by simp
  have len_eq:"length xs =length ys"
    using smods_smult_length[of 1 m] `m>0` unfolding xs_def ys_def by auto
  moreover have 
    "(map f xs) ! i = (map f ys) ! i"
    "(map sgn_pos_inf xs) ! i = (map sgn_pos_inf ys) ! i"
    "(map sgn_neg_inf xs) ! i = (map sgn_neg_inf ys) ! i"
     when "i<length xs" for i
  proof -
    note nth_eq=smods_smult_nth[OF one_neq_zero `m\<noteq>0`,of _ p q,unfolded smult_1_left, 
        folded xs_def ys_def,OF `i<length xs` ]
    then show "map f xs ! i = map f ys ! i"
          "(map sgn_pos_inf xs) ! i = (map sgn_pos_inf ys) ! i"
          "(map sgn_neg_inf xs) ! i = (map sgn_neg_inf ys) ! i"
      using that
      unfolding f_def using len_eq `m>0`
      by (auto simp add:sgn_mult sgn_pos_inf_def sgn_neg_inf_def lead_coeff_smult)  
  qed
  ultimately show "map f (smods p (smult m q)) = map f (smods p q)"
    "map sgn_pos_inf (smods p (smult m q)) = map sgn_pos_inf (smods p q)"
    "map sgn_neg_inf (smods p (smult m q)) = map sgn_neg_inf (smods p q)"
    apply (fold xs_def ys_def)
    by (auto intro: nth_equalityI)
qed

lemma changes_poly_at_smods_smult:
  assumes "m>0"  
  shows "changes_poly_at (smods p (smult m q)) x =changes_poly_at (smods p q) x "
using smods_smult_sgn_map_eq[OF `m>0`]
unfolding changes_poly_at_alternative by auto

lemma spmods_smods_sgn_map_eq:
  fixes p q::"real poly" and x::real
  defines "f\<equiv>\<lambda>p. sgn (poly p x)"
  shows "map f (smods p q) = map f (spmods p q)" 
        "map sgn_pos_inf (smods p q) = map sgn_pos_inf (spmods p q)"
        "map sgn_neg_inf (smods p q) = map sgn_neg_inf (spmods p q)"
proof (induct "spmods p q" arbitrary:p q)
  case Nil
  hence "p=0" using spmods_nil_eq by metis
  thus "map f (smods p q) = map f (spmods p q)" 
       "map sgn_pos_inf (smods p q) = map sgn_pos_inf (spmods p q)"
       "map sgn_neg_inf (smods p q) = map sgn_neg_inf (spmods p q)"
    by auto
next
  case (Cons p' xs)
  hence "p\<noteq>0" by auto
  define r where "r\<equiv>- (p mod q)"
  define exp where " exp\<equiv>degree p +1 - degree q"
  define m where "m\<equiv>(if even exp then 1 else lead_coeff q) 
      * (lead_coeff q ^ exp)"
  have xs1:"p#xs=spmods p q"  
    by (metis (no_types) Cons.hyps(4) list.distinct(1) list.inject  spmods.simps)
  have xs2:"xs=spmods q (smult m r)" when "q\<noteq>0" 
  proof -
    define m' where  "m'\<equiv>if even exp then - 1 else - lead_coeff q"
    have "smult m' (pseudo_mod p q) = smult m r" 
      unfolding m_def m'_def r_def 
      apply (subst pseudo_mod_mod[symmetric])
      using that exp_def by auto    
    thus ?thesis using `p\<noteq>0` xs1 unfolding r_def 
      by (simp add:spmods.simps[of p q,folded exp_def, folded m'_def] del:spmods.simps)
  qed
  define ys where "ys\<equiv>smods q r"
  have ys:"p#ys=smods p q" using `p\<noteq>0` unfolding ys_def r_def by auto
  have qm:"q\<noteq>0 \<Longrightarrow> m>0" 
    using `p\<noteq>0` unfolding m_def
    apply auto  
    subgoal by (simp add: zero_less_power_eq)
    subgoal using zero_less_power_eq by fastforce
    done
  show "map f (smods p q) = map f (spmods p q)"
  proof (cases "q\<noteq>0")
    case True
    then have "map f (spmods q (smult m r)) = map f (smods q r)"
      using smods_smult_sgn_map_eq(1)[of m x q r,folded f_def] qm 
        Cons.hyps(1)[OF xs2,folded f_def] 
      by simp  
    thus ?thesis
      apply (fold xs1 xs2[OF True] ys ys_def)
      by auto
  next
    case False
    thus ?thesis by auto
  qed
  show "map sgn_pos_inf (smods p q) = map sgn_pos_inf (spmods p q)"
  proof (cases "q\<noteq>0")
    case True
    then have "map sgn_pos_inf (spmods q (smult m r)) = map sgn_pos_inf (smods q r)"
      using Cons.hyps(2)[OF xs2,folded f_def] qm[OF True] 
        smods_smult_sgn_map_eq(2)[of m  q r,folded f_def] by auto
    thus ?thesis
      apply (fold xs1 xs2[OF True] ys ys_def)
      by (simp add:f_def)
  next
    case False
    thus ?thesis by auto
  qed 
  show "map sgn_neg_inf (smods p q) = map sgn_neg_inf (spmods p q)"
  proof (cases "q\<noteq>0")
    case True
    then have "map sgn_neg_inf (spmods q (smult m r)) = map sgn_neg_inf (smods q r)"
      using Cons.hyps(3)[OF xs2,folded f_def] qm[OF True] 
        smods_smult_sgn_map_eq(3)[of m  q r,folded f_def] by auto
    thus ?thesis
      apply (fold xs1 xs2[OF True] ys ys_def)  
      by (simp add:f_def)
  next
    case False
    thus ?thesis by auto
  qed 
qed

section{*Real algebraic number*}

declare [[coercion_enabled]]
declare [[coercion "of_rat::rat\<Rightarrow>real"]]
declare [[coercion "of_int::int\<Rightarrow>rat"]]
declare [[coercion_map map_poly]]

abbreviation "Real \<equiv> Real.Real"
abbreviation "cauchy \<equiv> Real.cauchy"
abbreviation "vanishes \<equiv> Real.vanishes"

fun to_cauchy:: "rat poly \<times> rat \<times> rat \<Rightarrow> nat \<Rightarrow> rat" where
  "to_cauchy (_, lb, ub) 0 = (lb+ub)/2"|
  "to_cauchy (p, lb, ub) (Suc n) = (
    let c=(lb+ub)/2
    in if  poly p lb * poly p c \<le>0  then to_cauchy (p, lb, c) n
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
  obtain n::nat where "n> log a (y/x)" 
    using reals_Archimedean2 by blast
  hence  "a powr n > a powr (log a (y/x))" 
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
  shows "lb\<le> Real X" "Real X\<le>ub" 
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
  shows "Real.Real (\<lambda>i. poly p (X i)) = poly p (Real.Real X)"
proof (induct p)
  case 0
  thus ?case by (simp add:zero_real_def)
next
  case (pCons a p)
  show ?case
    apply simp
    apply (subst Real.add_Real[symmetric])
    apply (auto intro!:Real.cauchy_mult cauchy_imp_poly_cauchy simp add:assms of_rat_Real)
    apply (subst Real.mult_Real[symmetric])   
    by (auto intro!:cauchy_imp_poly_cauchy simp add:assms pCons.hyps)
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
  shows "poly p (Real X) = 0" using assms(2)
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
  hence "poly p (Real (\<lambda>i. X i+r/2^i)) * poly p (Real (\<lambda>i. X i - r/2^i)) \<le>0"
    using power2_cauchy[OF `r>0`] cauchy_X
    apply (subst (asm) Real.mult_Real[symmetric]) prefer 3
    apply (subst (asm) (1 2) real_poly_eq_poly_real)
    by (auto intro: Real_leI cauchy_mult cauchy_imp_poly_cauchy cauchy_add to_cauchy_cauchy )
  moreover have "Real (\<lambda>i. X i+r/2^i) = Real X" and "Real (\<lambda>i. X i-r/2^i) = Real X"
    using cauchy_X power2_valishes power2_cauchy `r>0`
    by (subst Real.eq_Real,auto intro:vanishes_minus)+
  ultimately have "poly p (Real X) * poly p (Real X) \<le>0" by auto
  thus ?thesis by (metis linorder_neqE_linordered_idom mult_le_0_iff not_less)
qed

lemma to_cauchy_bound':
  fixes p::"rat poly" and lb ub ::rat
  defines "X\<equiv>to_cauchy (p,lb,ub)"
  assumes "lb<ub" and sgn_diff:"poly p lb * poly p ub<0"
  shows "lb< Real X" "Real X < ub"
proof -
  define x where"x=Real X"
  have "poly p x=0" using to_cauchy_root[OF `lb<ub`, of p] sgn_diff 
    apply (fold X_def x_def)
    by auto
  hence "x\<noteq>lb" "x\<noteq>ub" using sgn_diff 
    by (metis less_irrefl mult_eq_0_iff of_rat_eq_0_iff of_rat_poly_def of_rat_poly_poly)+
  moreover have "lb\<le>x" and "x\<le>ub" using to_cauchy_bound[OF `lb<ub`] unfolding x_def X_def by auto
  ultimately show "lb< Real X" "Real X < ub" unfolding x_def by auto
qed

definition roots_btw::"real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set" where
  "roots_btw p lb ub={x. poly p x=0 \<and> lb<x \<and> x<ub}"

lemma card_1:"card S=1 \<Longrightarrow> x\<in>S \<Longrightarrow> S={x}" by (metis One_nat_def card_eq_SucD empty_iff insertE)

definition changes_itv_spmods:: 
  "'a ::linordered_idom \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_itv_spmods a b p q= (let ps = spmods p q in 
        changes_poly_at ps a - changes_poly_at ps b)"

definition changes_R_spmods:: "'a::linordered_idom poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_R_spmods p q= (let ps= spmods p q in 
            changes_poly_neg_inf ps - changes_poly_pos_inf ps)"

lemma changes_map_real_of_float:
  "changes xs = changes (map real_of_float xs)"
proof (induct xs rule:changes.induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 x1 x2 xs)
  moreover have "x1*x2<0 \<longleftrightarrow> real_of_float x1 * real_of_float x2 < 0" 
    by (unfold mult_less_0_iff, simp)
  moreover have "x2=0 \<longleftrightarrow> real_of_float x2 =0" by (simp add: real_of_float_eq)
  ultimately show ?case by auto
qed

lemma changes_spmods_smods:
  fixes p q::"float poly" and a b::"float"
  shows "changes_itv_spmods a b p q = changes_itv_smods a b p q"
        "changes_R_spmods p q = changes_R_smods p q"
proof -
  define ps1 where "ps1\<equiv>smods p q"
  define ps2 where "ps2\<equiv>spmods (map_poly real_of_float p) (map_poly real_of_float q)"
  define ps3 where "ps3\<equiv>spmods p q"
  have ps2ps3:"ps2 = map of_float_poly ps3 " unfolding ps3_def ps2_def
  proof (induct "spmods p q" arbitrary:p q )
    case Nil
    thus ?case 
      by (metis list.map_disc_iff of_float_poly_0 of_float_poly_def spmods_nil_eq)
  next
    case (Cons p' xs)
    hence "p\<noteq>0" by auto
    define exp where "exp\<equiv>degree p + 1 - degree q"
    define m where "m\<equiv>(if even exp then - 1 else - lead_coeff q)"
    define r where "r\<equiv>smult m (pseudo_mod p q)"
    have xs1:"p#xs=spmods p q"  
      by (metis (no_types) Cons.hyps(2) list.distinct(1) list.inject  spmods.simps)
    have xs2:"xs=spmods q r" using xs1 `p\<noteq>0` r_def
      by (auto simp del:spmods.simps simp add:spmods.simps[of p q,folded exp_def,folded m_def])
    define ys where "ys\<equiv>spmods (of_float_poly q) (of_float_poly r)"
    have ys:"p#ys=spmods (of_float_poly p) (of_float_poly q)" 
      using `p\<noteq>0` unfolding ys_def r_def 
      apply (subst (2) spmods.simps)
      by (auto simp del:spmods.simps simp add:m_def exp_def of_float_poly_pseudo_mod)  
      show ?case using Cons.hyps(1)[OF xs2] 
        apply (fold xs1 xs2 of_float_poly_def)
        apply (fold ys ys_def)
        by auto
  qed
  show "changes_itv_spmods a b p q = changes_itv_smods a b p q"
  proof -
    have "map (\<lambda>p. sgn (poly p x)) ps1 = map (\<lambda>p. sgn (poly p x)) ps3" for x::float
      using spmods_smods_sgn_map_eq(1)[of _ "map_poly real_of_float p" "map_poly real_of_float q"
          ,folded ps1_def ps2_def] ps2ps3
      by (auto simp add:of_float_poly_poly)
    then have "changes_poly_at ps1 x = changes_poly_at ps3 x" for x::float
      unfolding changes_poly_at_alternative changes_poly_pos_inf_def
      using changes_map_real_of_float by auto
    then show ?thesis
      unfolding changes_itv_smods_def changes_itv_spmods_def
      apply (fold ps1_def ps3_def)
      by auto
  qed
  show "changes_R_spmods p q = changes_R_smods p q"
  proof -
    have "map sgn_pos_inf ps1 = map sgn_pos_inf ps3"
           "map sgn_neg_inf ps1 = map sgn_neg_inf ps3"
      using ps2ps3 spmods_smods_sgn_map_eq(2-3)[of p q,folded ps1_def ps2_def]
      by (auto simp add:sgn_pos_inf_def sgn_neg_inf_def) 
    then have "changes_poly_pos_inf ps1 = changes_poly_pos_inf ps3"
          "changes_poly_neg_inf ps1 = changes_poly_neg_inf ps3"
      unfolding changes_poly_pos_inf_def changes_poly_neg_inf_def
      using changes_map_real_of_float by auto
    then show ?thesis
      unfolding changes_R_smods_def changes_R_spmods_def
      apply (fold ps1_def ps3_def)
      by auto
  qed
qed

definition valid_alg::"int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "valid_alg p lb ub = (lb<ub \<and> poly (of_int_poly p) lb * poly (of_int_poly p) ub <0 
    \<and> card (roots_btw p lb ub) = 1)"


lemma [code]:"valid_alg p lb ub = (lb<ub \<and> (sgn(poly (of_int_poly p) lb) * sgn(poly (of_int_poly p) ub) <0) 
          \<and> changes_itv_spmods lb ub (of_int_poly p) (pderiv (of_int_poly p)) =1)"
proof -
  have "(card (roots_btw p lb ub) = 1) 
      \<longleftrightarrow> (changes_itv_spmods lb ub (of_int_poly p) (pderiv (of_int_poly p)) =1)"
      when "poly (of_int_poly p) lb * poly (of_int_poly p) ub <0" "lb<ub"
  proof -
    have "card (roots_btw (of_int_poly p) lb ub) 
          = changes_itv_smods lb ub (of_int_poly p) (pderiv (of_int_poly p))"
      apply (intro sturm_interval[of lb ub p,folded roots_btw_def,simplified])
      using that by (auto simp add:of_float_poly_poly real_of_float_eq)
    also have "... = changes_itv_spmods lb ub (of_int_poly p) (pderiv (of_int_poly p))"
      by (auto simp add:changes_spmods_smods of_float_poly_pderiv)
    finally show ?thesis by auto
  qed
  moreover have "poly (of_int_poly p) lb * poly (of_int_poly p) ub <0 =
    (sgn(poly (of_int_poly p) lb) * sgn(poly (of_int_poly p) ub) <0)"
    by (simp add: mult_less_0_iff)
  ultimately show ?thesis unfolding valid_alg_def
    by blast
qed

definition Alg:: "int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> real" where
  "Alg p lb ub = (if valid_alg p lb ub
                    then Real (to_cauchy (p,rat_of_float lb,rat_of_float ub))
                    else undefined)"

code_datatype Alg Ratreal real_of_float

lemma [code]: "real_of_float x \<le> real_of_float y \<longleftrightarrow> x \<le> y"
 "real_of_float x < real_of_float y \<longleftrightarrow> x < y"
  "real_of_float x + real_of_float y = real_of_float (x + y)"
  "real_of_float x * real_of_float y = real_of_float (x * y)"
  "- real_of_float x = real_of_float (- x)"
  "real_of_float x - real_of_float y = real_of_float (x - y)"
  by  auto

lemma rat_of_float_less[simp]: "rat_of_float x < rat_of_float y \<longleftrightarrow> x < y" 
  by (metis less_float.rep_eq of_rat_less real_of_rat_of_float)

lemma alg_bound_and_root:
  fixes p::"int poly" and lb ub::float
  assumes "valid_alg p lb ub"
  shows "lb<Alg p lb ub" and "Alg p lb ub<ub" and "poly (of_int_poly p) (Alg p lb ub) = 0"
proof -
  have less:"rat_of_float lb<rat_of_float ub" and "poly p lb * poly p ub<0" 
      and "card (roots_btw p lb ub) = 1" 
    using assms unfolding valid_alg_def 
    by (auto simp add:of_float_poly_poly)
  define x where "x\<equiv>Alg p lb ub"
  hence x:"x= Real (to_cauchy (of_int_poly p, rat_of_float lb, rat_of_float ub))" 
    using assms Alg_def valid_alg_def by auto
  have "poly (of_int_poly p) (real_of_float lb) * poly (of_int_poly p) (real_of_float ub) < 0" 
    using `poly p lb * poly p ub<0` by auto
  show "poly (of_int_poly p) x=0"
    using less `poly p lb * poly p ub<0`
    apply (intro to_cauchy_root[of "rat_of_float lb" "rat_of_float ub" "of_int_poly p",
        folded x,simplified ])
    apply auto
    by (metis (mono_tags, lifting) of_int_0 of_rat_less of_rat_mult of_rat_of_int_eq 
      of_rat_poly_of_int_poly_eq of_rat_poly_poly order.strict_implies_order real_of_rat_of_float)
  then show "lb<x" and "x<ub"
    using to_cauchy_bound[OF less,unfolded le_less,simplified,of "of_int_poly p",folded x] 
      `poly p lb * poly p ub<0`
    by auto
qed

lemma card_1_imp_eq:"card S=1 \<Longrightarrow> x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> x=y" by (metis One_nat_def card_eq_SucD singletonD)

lemma alg_eq:
  assumes valid:"valid_alg p lb ub" and "poly (of_int_poly p) x = 0" and "x>lb" and "x<ub"
  shows "x=Alg p lb ub"
proof -
  have "card (roots_btw (of_int_poly p) lb ub) = 1" using valid unfolding valid_alg_def by simp
  moreover have "x\<in>roots_btw (of_int_poly p) lb ub" using assms unfolding roots_btw_def by auto
  moreover have "Alg p lb ub\<in> roots_btw (of_int_poly p) lb ub" using alg_bound_and_root[OF valid] 
    unfolding roots_btw_def by auto
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
    thus False using valid by (auto simp add:valid_alg_def)  
  qed
  thus ?thesis by auto
qed

section \<open>Univariate sign determination procedure\<close>

class sgn_at=
  fixes sgn_at::"'a::linordered_idom poly \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes sgn_at_def:"sgn_at q x= sgn (poly q x)"

instantiation real :: sgn_at
begin

definition "(sgn_at::real poly\<Rightarrow>real\<Rightarrow>real) =(\<lambda>q x. sgn (poly q x))"

instance proof qed (simp add:sgn_at_real_def)

end


(*converting a rational real polynomial into an integer one 
  by clearing its denominators*)
definition int_poly::"real poly \<Rightarrow> int poly" where
  "int_poly p = clear_de (map_poly rat_of_real p)"

lemma int_poly:
  fixes p::"real poly"
  defines "p'\<equiv>map_poly rat_of_real p"
  shows "of_int_poly (int_poly p) = smult (of_int (de_lcm p')) p'"
  unfolding int_poly_def p'_def
  by (simp add: clear_de)

lemma sgn_at_code_ratreal[code]: "sgn_at q (Ratreal x) = sgn (poly q (Ratreal x))"
  unfolding sgn_at_def by auto

lemma sgn_at_code_alg[code]: "sgn_at q (Alg p lb ub) = ( 
    if valid_alg p lb ub \<and> (\<forall>x\<in>set (coeffs q). is_rat x) then 
      (let
          p'::float poly=of_int_poly p;
          q'::float poly=of_int_poly (int_poly q)
       in
      of_int (changes_itv_spmods lb ub p' (pderiv p' * q')))
    else Code.abort (STR ''Invalid sgn_at'') 
        (%_. sgn_at q (Alg p lb ub)))" (is "?L=?R")
proof (cases "valid_alg p lb ub \<and> (\<forall>x\<in>set (coeffs q). is_rat x)")
  case False
  thus ?thesis unfolding Alg_def sgn_at_def valid_alg_def by auto
next
  case True
  define p' q' where "p'\<equiv>(of_int_poly p)::float poly" and "q'\<equiv>(of_int_poly (int_poly q))::float poly"
  have "lb<ub" "poly p' lb * poly p' ub <0" "card (roots_btw p' lb ub) = 1" 
    using True unfolding valid_alg_def p'_def  by auto
  have "?R = of_int (changes_itv_spmods lb ub p' (pderiv p' * q'))"
    using True by (auto simp add:p'_def q'_def Let_def)
  also have "... = of_int (changes_itv_smods lb ub p' (pderiv p' * q'))"
    using changes_spmods_smods by auto
  also have "... = of_int (taq {x::real. poly p' x = 0 \<and> lb < x \<and> x < ub} (of_float_poly q'))"
    using `lb<ub` `poly p' lb * poly p' ub <0`
    apply (subst sturm_tarski_interval)    
    by (auto simp add:of_float_poly_pderiv of_float_poly_poly)
  also have "...  = of_int (taq {Alg p lb ub} (of_float_poly q'))"
  proof -
    define x where  "x\<equiv>Alg p lb ub" 
    have "lb<x" "x<ub" "poly (of_int_poly p) x=0" 
      using alg_bound_and_root True unfolding x_def by auto
    hence "x \<in> roots_btw (of_int_poly p) lb ub" unfolding roots_btw_def by auto
    hence "roots_btw (of_int_poly p) lb ub = {x}"
      using `card (roots_btw p' lb ub) = 1` unfolding p'_def
      by (elim card_1[rotated],simp)  
    thus ?thesis unfolding roots_btw_def x_def p'_def by auto
  qed
  also have "... =  sgn_at (of_float_poly q') (Alg p lb ub)" unfolding taq_def sgn_at_def
    unfolding sign_def by auto
  also have "... = sgn_at q (Alg p lb ub)"
  proof -
    define m where "m\<equiv>real_of_int (de_lcm (map_poly rat_of_real q))"
    have "of_float_poly q' = of_rat_poly (of_int_poly (int_poly q))"
      by (simp add:q'_def)
    also have "... =  smult m (of_rat_poly (map_poly rat_of_real q))" unfolding m_def
      by (auto simp add: int_poly[of q])
    also have "... = smult m q"
    proof -
      have "of_rat_poly (map_poly rat_of_real q) = q" using True
        apply (induct q)
        apply (simp_all add:of_rat_poly_def map_poly_map_poly del:of_rat_poly_def[symmetric])
        by (auto simp add:map_poly_pCons is_rat_def rat_of_real_inv)
      thus ?thesis by auto
    qed
    finally have "of_float_poly q' = smult m q" .
    moreover have "m>0" unfolding m_def by simp
    ultimately show ?thesis unfolding sgn_at_def by (simp add: sgn_mult)
  qed
  finally show ?thesis by simp
qed

(*for further optimization*)
definition sgn_at_core::"float poly \<Rightarrow> float poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> int" where
  "sgn_at_core q p lb ub = changes_itv_spmods lb ub p (pderiv p * q)"

lemma sgn_at_core:
  assumes valid:"valid_alg p lb ub"
  shows "sgn_at_core q (of_int_poly p) lb ub = sign (poly (of_float_poly q) (Alg p lb ub))"
proof -
  define p' where "p'\<equiv>(of_int_poly p)::float poly" 
  have "lb<ub" "poly p' lb * poly p' ub <0" and card:"card (roots_btw p' lb ub) = 1" 
    using valid unfolding valid_alg_def p'_def  by auto
  have "sgn_at_core q (of_int_poly p) lb ub =  (changes_itv_spmods lb ub p' (pderiv p' * q))"
    unfolding sgn_at_core_def
    using valid by (auto simp add:p'_def  Let_def)
  also have "... = of_int (changes_itv_smods lb ub p' (pderiv p' * q))"
    using changes_spmods_smods by auto
  also have "... = of_int (taq {x::real. poly p' x = 0 \<and> lb < x \<and> x < ub} (of_float_poly q))"
    using `lb<ub` `poly p' lb * poly p' ub <0`
    apply (subst sturm_tarski_interval)    
    by (auto simp add:of_float_poly_pderiv of_float_poly_poly)
  also have "...  = of_int (taq {Alg p lb ub} (of_float_poly q))"
  proof -
    define x where "x\<equiv>Alg p lb ub" 
    have "lb<x" "x<ub" "poly (of_int_poly p) x=0" 
      using alg_bound_and_root valid unfolding x_def by auto
    hence "x \<in> roots_btw (of_int_poly p) lb ub" unfolding roots_btw_def by auto
    hence "roots_btw (of_int_poly p) lb ub = {x}"
      using card unfolding p'_def
      by (auto intro!: card_1)  
    thus ?thesis unfolding roots_btw_def x_def p'_def by auto
  qed
  also have "... =  sign (poly (of_float_poly q) (Alg p lb ub))" unfolding taq_def sgn_at_def
    unfolding sign_def by auto
  finally show ?thesis by simp
qed

value [code] "sgn_at [:1::rat,2,3,4,5,6,7,8,9,10:] (2/3)"

section \<open>Bivariate sign determination procedure\<close>

lift_definition degen::"real bpoly \<Rightarrow> real \<Rightarrow>real bpoly" is
  "\<lambda>p y n. (if poly_y p y\<noteq>0 \<and> n \<le>degree (poly_y p y) then coeff p n else 0)"
by (metis (no_types, lifting) MOST_nat leD)

lemma degen_0[simp]:"degen 0 y=0" 
  apply transfer'
  by auto

lemma degen_pCons_0_eq[simp]:"degen [:a:] y = (if poly a y=0 then 0 else [:a:])"
  apply transfer'
  by (auto intro!:ext split:nat.split)

lemma degen_eq_0_iff:"degen p y=0 \<longleftrightarrow> poly_y p y=0"
  apply transfer'
  apply (auto intro!:ext split:nat.split)
by (metis coeff_poly_y leading_coeff_0_iff order_refl poly_0)

lemma degen_pCons:
  "poly_y p y\<noteq>0 \<Longrightarrow> degen (pCons a p) y  =  pCons a (degen p y)"
  "poly_y p y=0 \<Longrightarrow> degen (pCons a p) y = degen [:a:] y"
  apply transfer'
  apply transfer'
  apply (auto split:nat.split)[1]
  apply transfer'
  by auto

lemma degen_lc_not_vanish:"degen p y\<noteq>0 \<Longrightarrow> poly (lead_coeff (degen p y)) y \<noteq>0"
  apply (induct p,simp)
  apply (case_tac "poly_y p y=0")
  by (auto simp add:degen_pCons degen_eq_0_iff)
  
lemma degen_degree_leq:"degree (degen p y) \<le> degree p"
  apply (induct p,simp)
  apply (case_tac "poly_y p y=0")
  by (auto simp add:degen_pCons)

lemma poly_y_degen[simp]:"poly_y (degen p y) y = poly_y p y"
  apply (induct p,simp)
  apply (case_tac "poly_y p y=0")
  by (auto simp add:degen_pCons)

lemma poly_y_eq_0_coeffs_iff:"poly_y p y = 0 \<longleftrightarrow> (\<forall>q\<in>set (coeffs p). poly q y=0)" 
  apply (induct p)
  by auto

lemma strip_while_Cons_if:"strip_while P (x # xs) = (if (\<forall>x\<in>set xs. P x) then 
      (if P x then [] else [x]) else x#strip_while P xs)"
unfolding strip_while_def
by (auto simp add: dropWhile_append3)

lemma degen_code[code abstract]:
  fixes y :: "real"
  shows "coeffs (degen p y) = strip_while (\<lambda>q. sgn_at q y=0) (coeffs p)" 
apply (induct p,simp)
apply (case_tac "poly_y p y=0")
by (auto simp add:degen_pCons sgn_at_def sgn_0_0 cCons_def poly_y_eq_0_coeffs_iff strip_while_Cons_if)

function spmods_y :: "real bpoly \<Rightarrow> real bpoly \<Rightarrow> real  \<Rightarrow> (real bpoly) list" where
  "spmods_y p q y= (if p=0 then [] else 
      let 
        mul=(if even(degree p+1-degree q) then -1 else -lead_coeff q);
        r= degen (smult mul (pseudo_mod p q)) y
      in     
        Cons p (spmods_y q r y))"
  by auto
termination using degree_pseudo_mod_less
 apply (relation "measure (\<lambda>(p,q,_).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
 apply (auto intro!: order_trans_rules(21)[OF degen_degree_leq])
 by force+

lemma spmods_poly_y_dist:
  assumes not_degen: "poly (lead_coeff p) y\<noteq>0" "poly (lead_coeff q) y\<noteq>0"
  shows "spmods (poly_y p y) (poly_y q y) = map (\<lambda>p. poly_y p y) (spmods_y p q y)" 
    using assms
proof (induct "spmods (poly_y p y) (poly_y q y)" arbitrary:p q )
  case Nil
  hence "poly_y p y=0" using spmods_nil_eq by metis 
  hence False using Nil(2) lc_not_vanish_2 by auto
  thus ?case by simp    
next
  case (Cons _ xs)
  define m where "m\<equiv>(if even (degree p + 1 - degree q) then -1 else -lead_coeff q)"
  define r where "r\<equiv>degen (smult m (pseudo_mod p q)) y"
  define p' q' r' where "p'\<equiv>poly_y p y" and "q'\<equiv>poly_y q y" and "r'\<equiv>poly_y r y" 
  have "p\<noteq>0" and "p'\<noteq>0" and "q'\<noteq>0" using Cons.prems lc_not_vanish_2
    unfolding p'_def q'_def by auto
  have xs1:"p'#xs=spmods p' q'"  
    by (metis (no_types) Cons.hyps(2)[folded p'_def q'_def] list.distinct(1) list.inject spmods.simps)
  have xs2:"xs=spmods q' r'" 
  proof -
    define m' where "m'\<equiv>(if even (degree p' + 1 - degree q') then -1 else -lead_coeff q')"
    have "poly m y=m'" 
      using Cons.prems
      unfolding m_def m'_def p'_def q'_def
      by (simp add: lc_not_vanish_1 coeff_poly_y )
    hence "r'= smult m' (pseudo_mod p' q')" 
      using poly_y_dist_pmod[OF Cons.prems]
      unfolding r'_def r_def  p'_def q'_def
      by (auto simp add:poly_y_smult)
    thus ?thesis using  xs1 unfolding  m'_def r_def
      by (metis `p' \<noteq> 0` list.inject spmods.simps)
  qed
  define ys where "ys\<equiv>spmods_y q r y"
  have ys:"p#ys=spmods_y p q y" 
    unfolding ys_def r_def m_def
    by (metis `p \<noteq> 0` spmods_y.simps)
  have "spmods (poly_y q y) (poly_y r y) = map (\<lambda>p. poly_y p y) (spmods_y q r y)" 
  proof (cases "r=0")
    case True
    thus ?thesis using `q'\<noteq>0` unfolding q'_def by auto
  next
    case False
    hence "poly (lead_coeff r) y \<noteq> 0" using degen_lc_not_vanish
      unfolding r_def by auto
    thus ?thesis using Cons.hyps(1)[OF xs2[unfolded q'_def r'_def] Cons.prems(2)]
      by auto
  qed
  then show ?case 
    apply (fold p'_def q'_def r'_def xs1 xs2 ys ys_def)
    by (simp add:p'_def)
qed

definition bsgn_at::"real bpoly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "bsgn_at q x y=sgn (bpoly q x y)"

definition changes_bpoly_at::"real bpoly list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "changes_bpoly_at ps x y = changes (map (\<lambda>p. sgn (bpoly p x y)) ps)"

lemma [code]:
    "changes_bpoly_at ps (Ratreal x) (Ratreal y) = changes (map (\<lambda>p. sgn (bpoly p x y)) ps)"
  unfolding changes_bpoly_at_def by simp

lemma [code]:
    "changes_bpoly_at ps (real_of_float x) (Alg p lb ub) 
        = changes_bpoly_at ps (Ratreal (rat_of_float x)) (Alg p lb ub)"
  unfolding Ratreal_def real_of_rat_of_float by auto

lemma [code]:
    "changes_bpoly_at ps (real_of_float x) (real_of_float y) 
      = changes_bpoly_at ps (Ratreal (rat_of_float x)) (Ratreal (rat_of_float y))"
  unfolding Ratreal_def real_of_rat_of_float by auto

lemma [code]:
    "changes_bpoly_at ps (real_of_float x) (Ratreal y) 
      = changes_bpoly_at ps (Ratreal (rat_of_float x)) (Ratreal y)"
  unfolding Ratreal_def real_of_rat_of_float by auto

lemma of_int_poly_pderiv:
  "of_int_poly (pderiv p) = pderiv (of_int_poly p)"
  apply (induct p)
  by (auto simp add:pderiv_pCons)

lemma of_int_poly_of_int_poly[simp]:
  "of_int_poly (of_int_poly p) = of_int_poly p"
  by (induct p,auto)

(*FIXME: remove this*)
definition sgn_at_core_old::"real poly \<Rightarrow> int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> real" where
  "sgn_at_core_old q p lb ub = changes_itv_smods (rat_of_float lb) (rat_of_float ub) p (pderiv p * q)"

(*FIXME: remove this*)
lemma sgn_at_core_old:
  assumes valid:"valid_alg p lb ub"
  shows "sgn_at_core_old q p lb ub = sgn (poly q (Alg p lb ub))"
proof -
  define p' where "p'\<equiv>(of_int_poly p)::real poly" 
  define lb' ub' where "lb'= real_of_float lb" and "ub'=real_of_float ub"
  have "lb'<ub'" "poly p' lb' * poly p' ub' <0" and card:"card (roots_btw p' lb' ub') = 1" 
    using valid unfolding valid_alg_def p'_def lb'_def ub'_def  
    by (auto simp add:of_float_poly_poly)
  have "sgn_at_core_old q p lb ub = (changes_itv_smods lb' ub' p' (pderiv p' * q))"
    unfolding sgn_at_core_old_def p'_def lb'_def ub'_def
    by (auto simp add:of_int_poly_pderiv)
  also have "... = of_int (taq {x::real. poly p' x = 0 \<and> lb' < x \<and> x < ub'} q)"
    using \<open>lb'<ub'\<close> \<open>poly p' lb' * poly p' ub' <0\<close>
    apply (subst sturm_tarski_interval)    
    by (auto simp add:of_float_poly_pderiv of_float_poly_poly)
  also have "...  = of_int (taq {Alg p lb ub} q)"
  proof -
    define x where "x\<equiv>Alg p lb ub" 
    have "lb<x" "x<ub" "poly p' x=0" 
      using alg_bound_and_root valid unfolding x_def p'_def by auto
    hence "x \<in> roots_btw p' lb' ub'" unfolding roots_btw_def lb'_def ub'_def by auto
    hence "roots_btw p' lb' ub' = {x}"
      using card unfolding p'_def
      by (auto intro!: card_1)  
    thus ?thesis unfolding roots_btw_def x_def p'_def by auto
  qed
  also have "... =  sgn (poly q (Alg p lb ub))" unfolding taq_def sgn_at_def
    unfolding sign_def by auto
  finally show ?thesis by simp
qed

lemma [code]:"changes_bpoly_at ps (Ratreal x) (Alg p lb ub) =
      (if valid_alg p lb ub then
        changes (map (\<lambda>q. sgn_at_core_old (poly_x q x) p lb ub) ps)
      else
        Code.abort (STR ''invalid alg in changes_bpoly_at'') 
                              (%_. changes_bpoly_at ps (Ratreal x) (Alg p lb ub)))"
  unfolding changes_bpoly_at_def bpoly_def 
  by (auto simp add: poly_y_poly_x sgn_at_core_old comp_def) 

lemma bsgn_at_code2[code]:"
  bsgn_at q (Alg p1 lb1 ub1) y =
    (if valid_alg p1 lb1 ub1 
     then real_of_int
       (let
          q'=degen q y
        in (if q'=0 then 0 else 
            let ps = spmods_y (lift_x (of_int_poly p1)) (lift_x (pderiv (of_int_poly p1)) * q') y
            in changes_bpoly_at ps (real_of_float lb1) y - changes_bpoly_at ps (real_of_float ub1) y))
 else Code.abort (STR ''invalid Alg'') (%_. bsgn_at q (Alg p1 lb1 ub1) y))"
 (is "?L=?R")
proof (cases "valid_alg p1 lb1 ub1 \<and> degen q y\<noteq>0")
  case False
  thus ?thesis unfolding bsgn_at_def bpoly_def by (auto simp add:degen_eq_0_iff)  
next
  case True
  define seq where "seq\<equiv>smods (of_int_poly p1) (pderiv (of_int_poly p1) * poly_y q y)"
  define q' where "q'\<equiv>degen q y"
  define seq' where "seq'\<equiv>spmods_y (lift_x (map_poly real_of_int p1)) (lift_x (pderiv (of_int_poly p1)) * q') y"
  have "p1\<noteq>0" and "q'\<noteq>0" using True valid_alg_def unfolding q'_def by auto
  have not_vanish:" poly (lead_coeff q') y \<noteq> 0" 
    using degen_lc_not_vanish `q'\<noteq>0` unfolding q'_def by auto 
  have "?L = sgn_at (poly_y q y) (Alg p1 lb1 ub1)"
    unfolding bsgn_at_def bpoly_def sgn_at_def by simp
  also have "... = (sgn (poly (poly_y q y) (Alg p1 lb1 ub1)))"
    unfolding sgn_at_def sgn_sign_eq by blast
  also have "... = changes_poly_at seq lb1 - changes_poly_at seq ub1"
    apply (subst sgn_at_core_old[symmetric])
    unfolding sgn_at_core_old_def changes_itv_smods_def seq_def Let_def using True
    by simp_all
  also have "... = changes_bpoly_at seq' lb1 y- changes_bpoly_at seq' ub1 y"
  proof -
    define q1 q2 where "q1\<equiv>(pderiv (of_int_poly p1) * poly_y q' y)" 
                       and "q2\<equiv>lift_x (pderiv (of_int_poly p1)) * q'" 
    have "changes_poly_at seq x =  changes_bpoly_at seq' x y" for x
    proof -
      have "pderiv (of_int_poly p1)\<noteq>0" using valid_alg_deg True pderiv_eq_0_iff 
        by (metis of_int_poly_degree)
      hence "poly (lead_coeff q2) y \<noteq> 0" 
        using not_vanish lc_not_vanish_lift_x unfolding q2_def 
        by (auto simp add:lead_coeff_mult)
      moreover have "of_int_poly p1\<noteq>(0::real poly)" using `p1\<noteq>0` by auto    
      moreover have "poly_y q2 y=q1" unfolding q2_def q1_def 
        by (simp add: poly_y_lift_x poly_y_mult)
      ultimately have "spmods (of_int_poly p1) q1 = map (\<lambda>p. poly_y p y) seq'" 
        using spmods_poly_y_dist[OF lc_not_vanish_lift_x[OF `of_int_poly p1\<noteq>(0::real poly)`]
            ,unfolded poly_y_lift_x,of q2 y]
        unfolding seq'_def 
        apply (fold q2_def)
        by auto
      moreover note spmods_smods_sgn_map_eq(1)[of x "of_int_poly p1"
          "pderiv (of_int_poly p1) * poly_y q y",folded seq_def 
          poly_y_degen[of q y,folded q'_def],folded q1_def]        
      ultimately show "changes_poly_at seq x =  changes_bpoly_at seq' x y"
        unfolding changes_poly_at_alternative changes_bpoly_at_def bpoly_def
        by (auto simp add:comp_def) 
    qed
    thus ?thesis by auto
  qed
  finally show ?thesis using True
    apply (unfold Let_def)
    apply (fold seq'_def[folded of_int_poly_def,unfolded q'_def])
    by auto
qed

declare [[coercion_enabled=false]]

(*test*)
value [code] "sgn_at [:1,2,3,4,5,6,7,8,9,10:]  (Alg [:-2,0,0,0,0,1:] 0 2) = 1"

value [code] "bsgn_at [:[:1:]:]  (Alg [:-2,0,1:] 0 2) (Alg [:-3,0,1:] 0 2)"

value [code] "bsgn_at [:[:1:]:]  (Alg [:-2,0,1:] 0 2) (Ratreal 4)"

end
