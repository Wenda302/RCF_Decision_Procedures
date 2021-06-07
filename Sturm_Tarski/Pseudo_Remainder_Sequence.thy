theory Pseudo_Remainder_Sequence 
  imports Sturm_Tarski
    "HOL-Computational_Algebra.Computational_Algebra"
    Poly_Conversion
    (*"Algebraic_Numbers.Algebraic_Numbers"*)
    (*"HOL-Library.Float" *)
begin

section \<open>pseudo remainder sequence\<close>

function spmods :: "'a::idom poly \<Rightarrow> 'a poly \<Rightarrow> ('a poly) list" where
  "spmods p q= (if p=0 then [] else 
      let 
        m=(if even(degree p+1-degree q) then -1 else -lead_coeff q) 
      in     
        Cons p (spmods q (smult m (pseudo_mod p q))))"
by auto
termination
 apply (relation "measure (\<lambda>(p,q).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
 by (simp_all add: degree_pseudo_mod_less)

declare spmods.simps[simp del]

lemma spmods_0[simp]:
  "spmods 0 q = []"
  "spmods p 0 = (if p=0 then [] else [p])"
by (auto simp:spmods.simps)

lemma spmods_nil_eq:"spmods p q = [] \<longleftrightarrow> (p=0)"
  by (metis list.distinct(1) spmods.elims)

lemma changes_poly_at_alternative: 
  "changes_poly_at ps a= changes (map (\<lambda>p. sign(poly p a)) ps)" 
  "changes_poly_at ps a= changes (map (\<lambda>p. sgn(poly p a)) ps)" 
  unfolding changes_poly_at_def
  subgoal by (subst changes_map_sign_eq) (auto simp add:comp_def) 
  subgoal by (subst changes_map_sgn_eq) (auto simp add:comp_def)
  done

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

section \<open>Sign variations for pseudo-remainder sequences\<close>

locale order_hom =
  fixes hom :: "'a :: ord \<Rightarrow> 'b :: ord"
  assumes hom_less: "x < y \<longleftrightarrow> hom x < hom y"
   and hom_less_eq: "x \<le> y \<longleftrightarrow> hom x \<le> hom y"

locale linordered_idom_hom = order_hom hom + inj_idom_hom hom 
  for hom :: "'a :: linordered_idom \<Rightarrow> 'b :: linordered_idom" 
begin

lemma sgn_sign:"sgn (hom x) = sign x"
  by (simp add: sign_def hom_less sgn_if)

lemma sign_hom[simp]: "sign (hom x) = sign x"
  by (simp add: hom_less sign_def)

end
             
locale hom_pseudo_smods= comm_semiring_hom hom 
    + r1:linordered_idom_hom R\<^sub>1 + r2:linordered_idom_hom R\<^sub>2
  for hom::"'a::linordered_idom \<Rightarrow> 'b::{comm_semiring_1,linordered_idom}"
    and R\<^sub>1::"'a \<Rightarrow> real" 
    and R\<^sub>2::"'b \<Rightarrow> real" +
  assumes R_hom:"R\<^sub>1 x = R\<^sub>2 (hom x)"
begin

(*
  hom    R2

'a \<rightarrow> 'b \<rightarrow> real
      rat/float
int
p
      x
*)

lemma map_poly_R_hom_commute:
  "poly (map_poly R\<^sub>1 p) (R\<^sub>2 x) = R\<^sub>2 (poly (map_poly hom p) x)"
apply (induct p)
using r2.hom_add r2.hom_mult R_hom by auto

definition changes_hpoly_at::"'a poly list \<Rightarrow> 'b \<Rightarrow> int" where
  "changes_hpoly_at ps a= changes (map (\<lambda>p. sgn(eval_poly hom p a)) ps)" 

lemma changes_hpoly_at_Nil[simp]: "changes_hpoly_at [] a = 0"
  unfolding changes_hpoly_at_def by simp

definition changes_itv_spmods:: "'b \<Rightarrow> 'b \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_itv_spmods a b p q= (let ps = spmods p q in 
        changes_hpoly_at ps a - changes_hpoly_at ps b)"

definition changes_gt_spmods:: "'b \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_gt_spmods a p q= (let ps = spmods p q in 
        changes_hpoly_at ps a - changes_poly_pos_inf ps)"

definition changes_le_spmods:: "'b \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_le_spmods b p q= (let ps = spmods p q in 
        changes_poly_neg_inf ps - changes_hpoly_at ps b)"

definition changes_R_spmods:: "'a poly \<Rightarrow> 'a poly \<Rightarrow>  int" where
  "changes_R_spmods p q= (let ps= spmods p q in changes_poly_neg_inf ps 
      - changes_poly_pos_inf ps)"

lemma changes_spmods_smods:
  shows "changes_itv_spmods a b p q 
    = changes_itv_smods (R\<^sub>2 a) (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
  and "changes_R_spmods p q = changes_R_smods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
  and "changes_gt_spmods a p q = changes_gt_smods (R\<^sub>2 a) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
  and "changes_le_spmods b p q = changes_le_smods (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
proof -
  define pp qq where "pp = map_poly R\<^sub>1 p" and "qq = map_poly R\<^sub>1 q"

  have spmods_eq:"spmods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q) = map (map_poly R\<^sub>1) (spmods p q)" 
  proof (induct "spmods p q" arbitrary:p q )
    case Nil
    thus ?case by (metis list.simps(8) map_poly_0 spmods_nil_eq)
  next
    case (Cons p' xs)
    hence "p\<noteq>0" by auto
    define m where "m\<equiv>(if even (degree p + 1 - degree q) then - 1 else - lead_coeff q)"
    define r where "r\<equiv>smult m (pseudo_mod p q)"
    have xs1:"p#xs=spmods p q"  
      by (metis (no_types) Cons.hyps(2) list.distinct(1) list.inject  spmods.simps)
    have xs2:"xs=spmods q r" using xs1 \<open>p\<noteq>0\<close> r_def
      by (auto simp add:spmods.simps[of p q,folded exp_def,folded m_def])
    define ys where "ys\<equiv>spmods (map_poly R\<^sub>1 q) (map_poly R\<^sub>1 r)"
    have ys:"(map_poly R\<^sub>1 p)#ys=spmods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)" 
      using \<open>p\<noteq>0\<close> unfolding ys_def r_def 
      apply (subst (2) spmods.simps)
      unfolding m_def by (auto simp:r1.pseudo_mod_hom hom_distribs)
    show ?case using Cons.hyps(1)[OF xs2] 
      apply (fold xs1 xs2 ys ys_def)
      by auto
  qed

  have changes_eq_at:"changes_poly_at (smods pp qq) (R\<^sub>2 x) = changes_hpoly_at (spmods p q) x" 
    (is "?L=?R")
    for x
  proof -
    define ff where "ff = (\<lambda>p. sgn (poly p (R\<^sub>2 x)))"
    have "?L = changes (map ff (smods pp qq))"  
      using changes_poly_at_alternative unfolding ff_def by blast
    also have "... = changes (map ff (spmods pp qq))" 
      unfolding ff_def using spmods_smods_sgn_map_eq by simp
    also have "... = changes (map ff (map (map_poly R\<^sub>1) (spmods p q)))" 
      unfolding pp_def qq_def using spmods_eq by simp
    also have "... = ?R"
    proof -
      have "ff \<circ> map_poly R\<^sub>1 = sign \<circ> (\<lambda>p. eval_poly hom p x)" 
        unfolding ff_def comp_def
        by (simp add: map_poly_R_hom_commute poly_map_poly_eval_poly  r2.sgn_sign)
      then show ?thesis
        unfolding changes_hpoly_at_def
        apply (subst (2) changes_map_sign_eq)
        by (simp add:comp_def)
    qed
    finally show ?thesis .
  qed

  have changes_eq_neg_inf:
    "changes_poly_neg_inf (smods pp qq) = changes_poly_neg_inf (spmods p q)"
    (is "?L=?R")
  proof -
    have "?L = changes (map sgn_neg_inf (map (map_poly R\<^sub>1) (spmods p q)))"
      unfolding changes_poly_neg_inf_def spmods_smods_sgn_map_eq
      by (simp add: spmods_eq[folded pp_def qq_def])
    also have "... = changes (map (sgn_neg_inf \<circ> (map_poly R\<^sub>1)) (spmods p q))"
      using map_map by simp
    also have "... = changes (map ((sign:: _ \<Rightarrow> real) \<circ> sgn_neg_inf) (spmods p q))"
    proof - 
      have "(sgn_neg_inf \<circ> (map_poly R\<^sub>1)) = sign \<circ> sgn_neg_inf" 
        unfolding sgn_neg_inf_def comp_def
        by (auto simp:r1.sgn_sign)
      then show ?thesis by auto
    qed
    also have "... = changes (map sgn_neg_inf (spmods p q))"
      apply (subst (2) changes_map_sign_eq)
      by simp
    also have "... = ?R"
      unfolding changes_poly_neg_inf_def by simp
    finally show ?thesis .
  qed

  have changes_eq_pos_inf:
    "changes_poly_pos_inf (smods pp qq) = changes_poly_pos_inf (spmods p q)"
    (is "?L=?R")
  proof -
    have "?L = changes (map sgn_pos_inf (map (map_poly R\<^sub>1) (spmods p q)))"
      unfolding changes_poly_pos_inf_def spmods_smods_sgn_map_eq
      by (simp add: spmods_eq[folded pp_def qq_def])
    also have "... = changes (map (sgn_pos_inf \<circ> (map_poly R\<^sub>1)) (spmods p q))"
      using map_map by simp
    also have "... = changes (map ((sign:: _ \<Rightarrow> real) \<circ> sgn_pos_inf) (spmods p q))"
    proof - 
      have "(sgn_pos_inf \<circ> (map_poly R\<^sub>1)) = sign \<circ> sgn_pos_inf" 
        unfolding sgn_pos_inf_def comp_def
        by (auto simp:r1.sgn_sign)
      then show ?thesis by auto
    qed
    also have "... = changes (map sgn_pos_inf (spmods p q))"
      apply (subst (2) changes_map_sign_eq)
      by simp
    also have "... = ?R"
      unfolding changes_poly_pos_inf_def by simp
    finally show ?thesis .
  qed

  show "changes_itv_spmods a b p q 
          = changes_itv_smods (R\<^sub>2 a) (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_itv_spmods_def changes_itv_smods_def
    using changes_eq_at by (simp add: Let_def pp_def qq_def)
  show "changes_R_spmods p q = changes_R_smods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_R_spmods_def changes_R_smods_def Let_def
    using changes_eq_neg_inf changes_eq_pos_inf 
    by (simp add: pp_def qq_def)
  show "changes_gt_spmods a p q = changes_gt_smods 
                (R\<^sub>2 a) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_gt_spmods_def changes_gt_smods_def Let_def
    using changes_eq_at changes_eq_pos_inf
    by (simp add: pp_def qq_def)
  show "changes_le_spmods b p q = changes_le_smods 
                (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_le_spmods_def changes_le_smods_def Let_def
    using changes_eq_at changes_eq_neg_inf
    by (simp add: pp_def qq_def)
qed

end



end