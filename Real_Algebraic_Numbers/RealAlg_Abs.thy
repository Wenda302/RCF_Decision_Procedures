(*
    Author:     Wenda Li <wl302@cam.ac.uk>
*)
theory RealAlg_Abs
imports 
    Bivariate_Poly
    "../Rank_Nullity_Theorem/Generalizations"
begin

thm vector_space.span_explicit
thm span_explicit

text \<open>
  This theory formalizes real algebraic numbers on the abstract level without considering 
  executability. That is, we define a type of real algebraic numbers and formally show that 
  such type is, in fact, a linear order field.
\<close>  
  
section {*Misc*}
    
lift_definition truncate::"'a::zero poly \<Rightarrow> 'a poly" is 
  "\<lambda>p n. if n=degree p then 0 else coeff p n "
by (simp add: MOST_coeff_eq_0 MOST_imp_iff)

lemma truncate_0[simp]:"truncate 0=0"
  apply transfer'
  by auto

lemma truncate_pCons_0[simp]:"truncate [:a:]=0"
  apply transfer'
  by (auto simp add:coeff_eq_0)

lemma truncate_pCons:"p\<noteq>0 \<Longrightarrow> truncate (pCons a p) = pCons a (truncate p)"
  apply transfer'
  apply transfer'
  by (auto split:nat.split)

lemma truncate_imp_pos_degree:"truncate p \<noteq> 0 \<Longrightarrow> degree p >0"
  by (metis degree_eq_zeroE gr0I truncate_pCons_0)

lemma truncate_degree_le:"degree p\<noteq>0 \<Longrightarrow> degree (truncate p) < degree p "
  apply (induct p)
  by (auto simp add:truncate_pCons truncate_imp_pos_degree)

lemma truncate_degree_leq[simp]:"degree (truncate p) \<le> degree p"
  apply (induct p)
  by (auto simp add:truncate_pCons truncate_imp_pos_degree)

lemma truncate_monom:"p=truncate p + monom (lead_coeff p) (degree p)"
  apply (induct p)
  by (auto simp add:monom_0 truncate_pCons monom_Suc)


lemma monom_induct [case_names zero_deg induct]:
  assumes zero: "\<And>a. P [:a:]"
  assumes induct: "\<And>lc p n. lc\<noteq>0 \<Longrightarrow> degree p<n \<Longrightarrow> P p \<Longrightarrow> P (p+monom lc n)"
  shows "P p"
proof (induct p rule: measure_induct_rule [where f=degree])
  case (less p)
  have "degree p=0 \<Longrightarrow> ?case" 
  proof -
    assume "degree p=0"
    then obtain a where "p=[:a:]" using degree_eq_zeroE by auto
    thus ?case using zero by auto 
  qed
  moreover have "degree p\<noteq>0 \<Longrightarrow> ?case"
  proof -
    assume "degree p\<noteq>0"
    define p' where "p'\<equiv>truncate p"
    have p:"p=p'+ monom (lead_coeff p) (degree p)" and deg:"degree p'<degree p" 
      using truncate_monom truncate_degree_le[OF `degree p\<noteq>0`]  unfolding p'_def by auto 
    have "lead_coeff p\<noteq>0" using `degree p\<noteq>0` by auto
    thus ?case using less[OF deg] p induct[OF _ deg] by metis
  qed
  ultimately show ?case by blast
qed

lemma truncate_degree_y[simp]:"degree_y (truncate p) \<le> degree_y p"
proof (cases "truncate p=0")
  case True
  thus ?thesis by auto
next
  case False
  show ?thesis unfolding degree_y_def
    apply (rule Lattices_Big.linorder_class.Max.antimono)
    apply auto
    apply (rule_tac x=n in exI)
    by (metis eq_zero_or_degree_less leD le_trans truncate.rep_eq truncate_degree_leq False)
qed

section {*Rat-real vector space*}

global_interpretation rat:vector_space "(\<lambda>x y. (of_rat x * y))::rat \<Rightarrow> real \<Rightarrow> real"
  defines rat_span=rat.span
  apply (unfold_locales)
  apply (auto simp add:of_rat_mult of_rat_add ring_class.ring_distribs)
  done  

definition monom_base::"real \<Rightarrow> nat \<Rightarrow> real set" where
  "monom_base x n = {x^k | k. k\<le>n}"

definition monom_base_xy::"real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real set" where
  "monom_base_xy x n y m = {x^k1*y^k2 | k1 k2. k1\<le>n \<and> k2\<le> m}"

lemma monom_base_0[simp]: "monom_base x 0={1}" unfolding monom_base_def by auto

lemma monom_base_incl_1[simp]: "1 \<in> monom_base x n" unfolding monom_base_def by force

lemma monom_base_xy_0[simp]: 
    "monom_base_xy x 0 y m = monom_base y m" 
    "monom_base_xy x n y 0 = monom_base x n" 
  unfolding monom_base_def monom_base_xy_def by auto

lemma monom_base_xy_finite[simp]:"finite (monom_base_xy x n y m)"
  unfolding monom_base_xy_def by (simp add: finite_image_set2)

lemma monom_base_xy_mono:"n\<le>n' \<Longrightarrow> m\<le>m' \<Longrightarrow> monom_base_xy x n y m \<subseteq> monom_base_xy x n' y m'"
  unfolding monom_base_xy_def by fastforce

lemma finite_monom_base[simp]: "finite (monom_base x n)" unfolding monom_base_def by simp

lemma monom_base_Suc:"monom_base x (Suc n) = insert (x^(Suc n)) (monom_base x n)"
  unfolding monom_base_def using le_Suc_eq
  by (auto simp del:Power.power_class.power.power_Suc)

lemma monom_base_mono[simp]:"m\<le>n \<Longrightarrow> monom_base x m \<subseteq> monom_base x n" 
  unfolding monom_base_def by auto

lemma monom_base_incl[simp]:"k\<le>n \<Longrightarrow> x^k \<in> monom_base x n"
  unfolding monom_base_def by auto

lemma power_inject:
  fixes x::"'a::linordered_idom"
  assumes "x\<noteq>0" "x\<noteq>-1" "x\<noteq>1" and x_pow:"x^m = x^n" 
  shows "m=n"
proof -
  define ax where "ax\<equiv>abs x"
  have ax_pow:"ax^m = ax^n" using x_pow unfolding ax_def by (metis power_abs)
  have "ax>1 \<Longrightarrow> ?thesis" using ax_pow by auto
  moreover have "0<ax \<Longrightarrow> ax<1 \<Longrightarrow> ?thesis" using ax_pow 
    by (metis (full_types) less_irrefl linorder_cases power_strict_decreasing)
  moreover have "ax=0 \<Longrightarrow> False" using `x\<noteq>0` unfolding ax_def  by auto
  moreover have "ax=1 \<Longrightarrow> False" using `x\<noteq>-1` `x\<noteq>1` unfolding ax_def by auto
  moreover have "ax\<ge>0" unfolding ax_def by auto
  ultimately show ?thesis by fastforce
qed

lemma monom_base_card1:"card (monom_base x n) \<le> Suc n"
  apply (induct n)
  by (auto simp add:monom_base_Suc card_insert_if simp del:power.power_Suc)

lemma monom_base_card2:
  assumes "x\<noteq>0" "x\<noteq>-1" "x\<noteq>1" 
  shows "card (monom_base x n) = Suc n"
proof (induct n)
  case 0
  show ?case by auto
next
  case (Suc n)
  have "x^(Suc n) \<notin> monom_base x n" using power_inject[OF assms]
    unfolding monom_base_def using Suc_n_not_le_n by blast
  thus ?case using monom_base_Suc Suc by auto  
qed

lemma monom_base_xy_card:
  "card (monom_base_xy x n y m) \<le> (Suc n)*(Suc m)"
proof -
  define f where "f\<equiv>\<lambda>(u1,u2). x^u1 * y^u2"
  have "monom_base_xy x n y m = f ` ({0..n} \<times> {0..m})"
    unfolding monom_base_xy_def f_def by fastforce
  moreover have "card (f ` ({0..n} \<times> {0..m})) \<le> (Suc n)*(Suc m)"
    using card_image_le[of "{0..n} \<times> {0..m}" f, simplified] card_cartesian_product
    by auto
  ultimately show ?thesis by auto
qed

lemma poly_rat_span:
  fixes x::real and p::"rat poly"
  shows "poly (of_rat_poly p) x \<in> rat.span (monom_base x (degree p))"
proof (induct p rule:monom_induct)
  case (zero_deg a)
  show ?case 
    by (auto intro: rat.span_mul[of 1 _ a,simplified] rat.span_clauses)
next
  case (induct lc p n)
  have deg:"degree (p + monom lc n) = n" 
    using induct(1,2) degree_add_eq_right[of p "monom lc n"] degree_monom_eq[of lc n] 
    by auto
  hence "monom_base x (degree p) \<subseteq> monom_base x n"
    using induct(2) by (auto intro: monom_base_mono)
  hence "poly (of_rat_poly p) x \<in> rat.span (monom_base x n)"
    using induct(3) rat.span_mono by auto 
  moreover have "poly (monom (of_rat lc) n) x \<in> rat.span (monom_base x n)"
    by (auto simp add: Polynomial.poly_monom intro!:rat.span_clauses)
  ultimately show ?case using deg
    by (auto simp add: of_rat_poly_monom intro:rat.span_clauses)
qed 
  
lemma monom_span_monom_xy_base:
  "bpoly (monom (of_rat_poly p) n) x y \<in> rat.span (monom_base_xy x n y (degree p))"
proof (induct p rule:monom_induct)
  case (zero_deg a)
  show ?case unfolding bpoly_def
    by (simp add: poly_monom poly_y_monom rat.span_clauses span_mul)
next
  case (induct lc p m)
  define base pxy where "base\<equiv>monom_base_xy x n y (degree (p + monom lc m))"
    and "pxy\<equiv>bpoly (monom (of_rat_poly p) n) x y"
  have deg:"degree (p + monom lc m) = m" 
    using induct(1,2) degree_add_eq_right[of p "monom lc m"] degree_monom_eq[of lc m] 
    by auto
  hence "monom_base_xy x n y (degree p) \<subseteq> base"
    unfolding base_def  
    apply (intro monom_base_xy_mono)
    using induct(2) by auto
  hence "pxy \<in> rat.span base"
    using induct(3) rat.span_mono unfolding pxy_def base_def  by auto 
  moreover have "bpoly (monom (monom (of_rat lc) m) n) x y \<in> rat.span base"
    unfolding base_def[simplified deg]  
    apply (auto simp add:poly_monom poly_y_poly_x poly_x_def bpoly_def)
    apply (subst mult.assoc) 
    apply (rule rat.span_clauses(4)[of " y ^ m * x ^ n " _ "lc"])
    apply (rule rat.span_clauses(1))
    apply (unfold monom_base_xy_def)
    by force
  ultimately show ?case 
    unfolding base_def pxy_def
    by (auto simp add: of_rat_poly_monom add_monom[symmetric] intro:rat.span_clauses)
qed

lemma bpoly_rat_span:
  fixes x y::real and p::"rat bpoly"
  shows "bpoly (of_rat_bpoly p) x y \<in> rat.span (monom_base_xy x (degree p) y (degree_y p))"
proof (induct "degree p" arbitrary:p rule:nat_less_induct)
  case 1
  have "degree p=0 \<Longrightarrow> ?case" 
  proof -
    assume "degree p=0"
    then obtain a::"rat poly" where "p=[:a:]" 
      by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)
    thus ?case by (auto simp add:degree_y_pCons_0 poly_rat_span)
  qed
  moreover have "degree p\<noteq>0 \<Longrightarrow> ?case"
  proof -
    assume "degree p\<noteq>0"
    define p' base where "p'\<equiv>truncate p"
      and "base\<equiv>\<lambda>p::rat bpoly. monom_base_xy x (degree p) y (degree_y p)"
    have p:"p=p'+ monom (lead_coeff p) (degree p)" and deg:"degree p'<degree p" 
      using truncate_monom truncate_degree_le[OF `degree p\<noteq>0`]  unfolding p'_def by auto 
    have "bpoly (of_rat_bpoly p') x y \<in> rat.span (base p)"       
    proof -
      have "degree_y p' \<le> degree_y p" using deg unfolding  p'_def by simp
      hence "base p' \<subseteq> base p" using deg unfolding base_def monom_base_xy_def by fastforce 
      moreover have "bpoly (of_rat_bpoly p') x y \<in> rat.span (base p')"
        using "1.hyps"[rule_format,of _ p'] truncate_degree_le[of p, folded p'_def] `degree p\<noteq>0`
        unfolding base_def
        by auto
      ultimately show ?thesis using rat.span_mono by auto  
    qed
    moreover have "degree (lead_coeff p) \<le> degree_y p" unfolding degree_y_def 
      by (auto intro: Max_ge)
    hence "monom_base_xy x (degree p) y (degree (lead_coeff p)) \<subseteq> base p" 
      unfolding base_def
      apply (intro monom_base_xy_mono)
      by auto
    hence "bpoly (monom (of_rat_poly (lead_coeff p)) (degree p)) x y \<in>rat.span (base p)" 
      using monom_span_monom_xy_base unfolding base_def 
      by (meson monom_span_monom_xy_base rat.span_mono subsetCE)
    ultimately show ?case 
      apply (subst p)
      by (auto simp add: base_def intro:rat.span_clauses)
  qed
  ultimately show ?case by blast
qed
    
lemma bpoly_in_rat_span:
  fixes p q::"rat poly" and x y::real and bp::"rat bpoly"
  assumes p_root:"poly (of_rat_poly p) x =0" and "p\<noteq>0"
  assumes q_root:"poly (of_rat_poly q) y =0" and "q\<noteq>0"
  shows "bpoly (of_rat_bpoly bp) x y \<in> rat.span (monom_base_xy x (degree p) y (degree q))"
proof -
  have deg_q:"degree q>0" and deg_p:"degree p>0"
    by (metis (no_types, hide_lams) assms degree_pCons_eq_if neq0_conv 
      of_rat_poly_degree of_rat_poly_pCons old.nat.distinct(2) pCons_eq_0_iff synthetic_div_eq_0_iff
      synthetic_div_pCons)+
  define p' where "p'\<equiv>smult (inverse (lead_coeff p)) p"
  have "lead_coeff p'=1" and "p'\<noteq>0" and p'_root:"poly (of_rat_poly p') x=0" 
    unfolding p'_def using `p\<noteq>0` p_root by (auto simp add: lead_coeff_smult)
  define bp1 where "bp1\<equiv>pseudo_mod bp (lift_x p')" 
  have bp1_bpoly:"bpoly (of_rat_bpoly bp1) x y = bpoly (of_rat_bpoly bp) x y"
  proof -
    have "lead_coeff (of_rat_poly p') = 1"
      using \<open>lead_coeff p'=1\<close> by (metis of_rat_1 of_rat_lead_coeff)
    have "poly_x (lift_x (of_rat_poly p')) x=0" 
      using poly_x_lift_x[of "of_rat_poly p'" x] p'_root by auto
    then show "bpoly (of_rat_bpoly bp1) x y = bpoly (of_rat_bpoly bp) x y" 
      unfolding bp1_def poly_x_def bpoly_def [[]]
      apply (simp add:poly_y_poly_x poly_x_def of_rat_bpoly_pseudo_mod)
      apply (subst poly_pseudo_mod,
            simp_all add:\<open>p'\<noteq>0\<close> lead_coeff_lift_x \<open>lead_coeff (of_rat_poly p') = 1\<close>)  
      by (metis \<open>lead_coeff (of_rat_poly p') = 1\<close> degree_lift_x lead_coeff_lift_x 
          of_rat_poly_degree one_poly_eq_simps(1) poly_1 power_one)
  qed
  have bp1_deg:"degree bp1 <degree p"
    proof -
      have "degree p'=degree p" unfolding p'_def by auto
      moreover hence "degree bp1 <degree p'"
        unfolding bp1_def using pseudo_mod(2)[of "lift_x p'" bp] `p'\<noteq>0` deg_p
        by auto
      ultimately show ?thesis by auto
    qed
  define bp2 where "bp2\<equiv>map_poly (\<lambda>p'. p' mod q) bp1"
  have "bpoly (of_rat_bpoly bp2) x y = bpoly (of_rat_bpoly bp1) x y" 
    unfolding bpoly_def poly_y_def bp2_def of_rat_bpoly_def
    by (auto simp add:map_poly_map_poly comp_def poly_mod[OF q_root] )
  hence "bpoly (of_rat_bpoly bp) x y = bpoly (of_rat_bpoly bp2) x y" 
    using bp1_bpoly by simp
  moreover have "degree_y bp2<degree q" unfolding bp2_def degree_y_def
    apply (subst Lattices_Big.linorder_class.Max_less_iff,auto) 
    by (metis assms(4) coeff_map_poly deg_q degree_0 degree_mod_less' mod_poly_less)  
  moreover have "degree bp2 \<le> degree bp1"
    unfolding bp2_def
    by (metis coeffs_Poly degree_eq_length_coeffs diff_le_mono length_map 
        length_strip_while_le map_poly_def)  
  hence "degree bp2 < degree p" using bp1_deg by simp
  ultimately show ?thesis 
    using bpoly_rat_span[of bp2 x y,simplified] 
    monom_base_xy_mono[THEN rat.span_mono,of "degree bp2" "degree p" "degree_y bp2"  "degree q"] 
    by (auto intro: rat.span_clauses )
qed

lemma dependent_aux:
  fixes S::"real set" and f::"real \<Rightarrow> rat"
  assumes "S \<subseteq> monom_base x n"
  assumes "\<exists>v\<in>S. f v \<noteq> 0" and "(\<Sum>v\<in>S. (of_rat (f v)) * v) = a"
  shows "\<exists>p::rat poly. p\<noteq>0 \<and> degree p \<le> n \<and> poly (of_rat_poly p) x=a" using assms
proof (induct n arbitrary:a S)
  case 0
  have "S \<subseteq> {1}"  using 0 by auto
  moreover have "S={} \<Longrightarrow> ?case" using 0 by auto
  moreover have "S={1} \<Longrightarrow> ?case" using 0 by (rule_tac x="[:f 1:]" in exI,auto)
  ultimately show ?case by force
next
  case (Suc n)
  define mm where "mm \<equiv> x^(Suc n)"
  define S' where "S' \<equiv> S - {mm}"
  define lc where "lc \<equiv> f mm"
  define a' where "a'\<equiv>(\<Sum>v\<in>S'. real_of_rat (f v) * v)"        
  have a:"a' = (if mm \<in> S then a - (of_rat lc) * mm else a)" 
  proof -
    have "finite S" using Suc(2) rev_finite_subset[of "monom_base x (Suc n)"] by auto
    moreover note Groups_Big.sum_diff1[of S "\<lambda>v. real_of_rat (f v) * v" mm, 
         folded Suc(4)[symmetric] lc_def S'_def]
    ultimately show ?thesis unfolding a'_def by auto 
  qed
  have "\<not> (\<exists>v\<in>S'. f v \<noteq> 0) \<Longrightarrow> ?case"
  proof -
    assume "\<not> (\<exists>v\<in>S'. f v \<noteq> 0)"
    hence "\<forall>v\<in>S'. f v=0" by auto
    hence "mm \<in> S" and "lc \<noteq>0" and "a'=0" using Suc(3) S'_def lc_def a'_def by auto
    hence "of_rat lc * mm = a" using a by simp
    thus ?case using `lc\<noteq>0` degree_monom_le[of lc "Suc n"] unfolding mm_def
      apply (rule_tac x="monom lc (Suc n)" in exI)
      by (auto simp add:poly_monom of_rat_poly_monom) 
  qed
  moreover have "\<exists>v\<in>S'. f v \<noteq> 0 \<Longrightarrow> ?case"
  proof -
    assume asm:"\<exists>v\<in>S'. f v \<noteq> 0"
    have "S' \<subseteq> monom_base x n" using Suc(2) monom_base_Suc unfolding S'_def mm_def  by auto 
    then obtain p' where "p' \<noteq> 0" and p'_deg: "degree p'\<le>n" and p'_a': "poly (of_rat_poly p') x = a'"
      using Suc.hyps[OF _ asm] S'_def a'_def  by auto
    define p where "p\<equiv>(if mm \<in> S then p'+monom lc (Suc n) else p')"
    have "poly (of_rat_poly p) x=a" 
      using p'_a' a unfolding p_def mm_def
      by (auto simp add: of_rat_poly_monom poly_monom)
    moreover have "p\<noteq>0 \<and> degree p \<le> Suc n" 
    proof (cases "mm \<notin> S \<or> lc=0")
      case True
      thus ?thesis unfolding p_def using `p'\<noteq>0` p'_deg by auto
    next
      case False
      hence "degree p=Suc n" 
        using degree_add_eq_right[of p' "monom lc (Suc n)"] degree_monom_eq[of lc "Suc n"] p'_deg
        unfolding p_def by auto
      thus ?thesis using p'_deg by auto
    qed
    ultimately show ?case by auto
  qed
  ultimately show ?case by auto
qed

lemma dependent_imp_poly:
  assumes "rat.dependent (monom_base x n)"
  shows "\<exists>p::rat poly. p\<noteq>0 \<and> degree p\<le>n \<and>  poly (of_rat_poly p) x=0" 
proof -
  obtain S f where "S \<subseteq> monom_base x n" "\<exists>v\<in>S. f v \<noteq> 0" "(\<Sum>v\<in>S. real_of_rat (f v) * v) = 0"
    using assms[unfolded rat.dependent_explicit] by auto 
  thus ?thesis using dependent_aux by auto
qed

lemma (in vector_space) span_card_imp_dependent:
  assumes "S \<subseteq> span B"  "finite B" "card S > card B"
  shows "dependent S"
proof (rule ccontr)
  assume "independent S"
  hence "card S \<le> card B" using independent_span_bound[OF `finite B` _ `S \<subseteq> span B`] by auto
  thus False using `card S > card B` by auto
qed

lemma dependent_base:
  fixes x y z::real and p q::"rat poly"
  assumes p_root:"poly (of_rat_poly p) x = 0" and "p\<noteq>0" 
  assumes q_root:"poly (of_rat_poly q) y = 0" and "q\<noteq>0"
  defines "n\<equiv>(degree p+1)*(degree q+1)+1"
  defines "dep\<equiv>(\<lambda>u. rat.dependent (monom_base u n) \<or> u=1)"
  shows "dep (x+y)" and "dep (x-y)" and "dep (x*y)"
proof -
  define base where "base\<equiv>monom_base_xy x (degree p) y (degree q)"
  define z1 z2 where "z1\<equiv>x+y" and "z2\<equiv>x*y"
  have "monom_base (x+y) n \<subseteq> rat_span base"
  unfolding monom_base_def
  proof clarify
    fix k 
    define bp where "bp\<equiv>[:[:0::rat,1:],[:1:]:] ^ k"
    have "(x+y)^k = bpoly (of_rat_bpoly bp) x y " unfolding bp_def
      by (auto simp add:algebra_simps)
    moreover note bpoly_in_rat_span[OF p_root `p\<noteq>0` q_root `q\<noteq>0`,of bp,folded base_def]
    ultimately show "(x + y) ^ k \<in> rat_span base" by auto
  qed
  moreover have "monom_base (x-y) n \<subseteq> rat_span base"
  unfolding monom_base_def
  proof clarify
    fix k 
    define bp where "bp\<equiv>[:[:0::rat,- 1:],[:1:]:] ^ k"
    have "(x-y)^k = bpoly (of_rat_bpoly bp) x y " unfolding bp_def
      by (auto simp add:algebra_simps)
    moreover note bpoly_in_rat_span[OF p_root `p\<noteq>0` q_root `q\<noteq>0`,of bp,folded base_def]
    ultimately show "(x - y) ^ k \<in> rat_span base" by auto
  qed
  moreover have "monom_base (x*y) n \<subseteq> rat_span base"
  unfolding monom_base_def
  proof clarify
    fix k 
    define bp where "bp\<equiv>[:0,[:0::rat,1:]:] ^ k"
    have "(x*y)^k = bpoly (of_rat_bpoly bp) x y " unfolding bp_def
      by (auto simp add:algebra_simps)
    moreover note bpoly_in_rat_span[OF p_root `p\<noteq>0` q_root `q\<noteq>0`,of bp,folded base_def]
    ultimately show "(x * y) ^ k \<in> rat_span base" by auto
  qed
  moreover have "\<And>z. \<lbrakk>z\<noteq>0;z\<noteq>-1;z\<noteq>1\<rbrakk> \<Longrightarrow> card (monom_base z n) > card base" 
    using monom_base_xy_card[of x "degree p" y "degree q",folded base_def] 
      monom_base_card2[where n=n] unfolding n_def
    by auto
  moreover have "finite base" unfolding base_def by simp
  ultimately have 
    "\<lbrakk>x+y\<noteq>0;x+y\<noteq>-1;x+y\<noteq>1\<rbrakk> \<Longrightarrow> rat.dependent (monom_base (x+y) n)"
    and "\<lbrakk>x-y\<noteq>0;x-y\<noteq>-1;x-y\<noteq>1\<rbrakk> \<Longrightarrow> rat.dependent (monom_base (x-y) n)"
    and "\<lbrakk>x*y\<noteq>0;x*y\<noteq>-1;x*y\<noteq>1\<rbrakk> \<Longrightarrow> rat.dependent (monom_base (x*y) n)"
    by (auto intro!:rat.span_card_imp_dependent)
  moreover have "rat.dependent (monom_base (-1) n)" 
  proof -
    have "1\<in> monom_base (-1) n" by simp
    moreover have "-1 \<in> monom_base (-1) n" unfolding monom_base_def n_def by force
    ultimately show ?thesis unfolding rat.dependent_def
      apply (rule_tac x=1 in bexI)
      apply (intro rat.span_mul[of "-1" _ "-1",simplified])
      by (auto intro: rat.span_clauses)
  qed
  moreover have "rat.dependent (monom_base 0 n)" 
    apply (rule rat.dependent_0)
    by (auto simp add:monom_base_def n_def)
  ultimately show "dep (x+y)" and "dep (x-y)" and "dep (x*y)"
    unfolding dep_def
    by metis+
qed

lemma rat_int_poly_exist:
  fixes p::"rat poly"
  shows "\<exists>(q::int poly) (n::int).n\<noteq>0 \<and> of_int_poly q = smult (of_int n) p "
proof (induct p)
  case 0
  show ?case 
    apply (rule_tac x=0 in exI)
    apply (rule_tac x=1 in exI)
    by simp
next
  case (pCons a p)
  then obtain q::"int poly" and n::int where qn:"of_int_poly q = smult (rat_of_int n) p "
    and "n\<noteq>0" by auto
  obtain a1 a2 ::int where "quotient_of a = (a1,a2)" by fastforce
  hence a:"a = of_int a1 / of_int a2" and "a2>0" using quotient_of_denom_pos quotient_of_div 
    by auto
  define n' where "n'\<equiv>a2*n"  
  define q' where "q'\<equiv>pCons (n*a1) (smult a2 q)"
  show ?case using `a2>0` `n\<noteq>0`
    apply (rule_tac x=q' in exI)
    apply (rule_tac x=n' in exI)
    apply (unfold a n'_def q'_def)
    by (simp add:qn of_int_poly_smult)
qed

lemma inverse_root_exist:
  fixes x::real and p::"rat poly"
  assumes p_root:"poly (of_rat_poly p) x = 0" and "p\<noteq>0" 
  shows "\<exists>q::int poly. q\<noteq>0 \<and> poly (of_int_poly q) (inverse x) = 0"
proof (cases "x=0")
  case True
  thus ?thesis
    apply (rule_tac x="[:0::int,1:]" in exI)
    by auto
next
  case False
  obtain q n where "n\<noteq>0" and q:"of_int_poly q = smult (real_of_int n) (of_rat_poly (rev_poly p))"
    using rat_int_poly_exist[of "rev_poly p"] 
    by (metis (no_types) of_rat_of_int_eq of_rat_poly_of_int_poly_eq of_rat_poly_smult)
  hence "x ^ degree p \<noteq>0" using False by auto
  hence "poly (of_int_poly q) (inverse x) = 0"
    using rev_poly_poly[OF False, of "of_rat_poly p"] p_root `n\<noteq>0` 
    unfolding q by (auto simp add:of_rat_poly_rev_poly)
  moreover have "q\<noteq>0" using `p\<noteq>0` using q `n\<noteq>0` by auto
  ultimately show ?thesis
    apply (rule_tac x=q in exI)
    by auto
qed  

lemma root_exist:
  fixes x y::real and p q::"rat poly"
  assumes p_root:"poly (of_rat_poly p) x = 0" and "p\<noteq>0" 
  assumes q_root:"poly (of_rat_poly q) y = 0" and "q\<noteq>0"
  defines "rt\<equiv>(\<lambda>z. \<exists>r::int poly. r\<noteq>0 \<and> poly (of_int_poly r) z = 0)"
  shows "rt (x+y)" and "rt (x-y)" and "rt (x*y)"
proof -
  define n where "n\<equiv>(degree p+1)*(degree q+1)+1"
  define dep where "dep\<equiv>(\<lambda>u. rat.dependent (monom_base u n) \<or> u=1)"
  define rt' where "rt'\<equiv>(\<lambda>z::real. \<exists>r::rat poly. r\<noteq>0 \<and> poly (of_rat_poly r) z = 0)"
  have "dep (x+y)" and "dep (x-y)" and "dep (x*y)"
    using dependent_base[OF p_root `p\<noteq>0` q_root `q\<noteq>0`,folded n_def] unfolding dep_def by auto
  moreover have "rt 1" unfolding rt_def
    apply (rule_tac x="[:-1,1:]" in exI)
    by auto
  moreover have "\<And>z::real. rt' z \<Longrightarrow> rt z" 
  proof -
    fix z::real assume "rt' z"
    then obtain r::"rat poly" where "r\<noteq>0" and r_root:"poly (of_rat_poly r) z=0"
      unfolding rt'_def by auto
    then obtain r1::"int poly" and n::int where "n\<noteq>0" and  r1:"of_int_poly r1 = smult (of_int n) r"
      using rat_int_poly_exist[of r] by auto
    hence "r1\<noteq>0" using `r\<noteq>0` by auto
    moreover have "(of_int_poly::_\<Rightarrow>real poly) r1 = smult (of_int n) (of_rat_poly r)"
      using r1 by (metis of_rat_of_int_eq of_rat_poly_of_int_poly_eq of_rat_poly_smult)
    hence " poly (of_int_poly r1) z = 0" using r_root
      by simp
    ultimately show "rt z" unfolding rt_def using r_root `r\<noteq>0`
      apply (rule_tac x=r1 in exI)
      by simp
  qed
  ultimately show "rt (x+y)" and "rt (x-y)" and "rt (x*y)"
    using dependent_imp_poly unfolding rt_def dep_def rt'_def by metis+
qed

section{*Real algebraic numbers*}
    
typedef alg="{x::real. \<exists>p::int poly. p\<noteq>0 \<and> poly (of_int_poly p) x =0}"
  apply (rule_tac x=0 in exI,simp)
by (rule_tac x="[:0,1:]" in exI,simp)

setup_lifting type_definition_alg

instantiation alg::field
begin

lift_definition zero_alg:: alg is 0 
  apply (rule_tac x="[:0,1:]" in exI)
  by simp

lift_definition one_alg:: alg is 1 
  apply (rule_tac x="[:-1,1:]" in exI)
  by simp

lift_definition plus_alg :: "alg \<Rightarrow> alg \<Rightarrow> alg" is plus 
  apply (elim exE)
  apply (rule_tac p="of_int_poly p" and q="of_int_poly pa" in root_exist(1))
  by auto  

lift_definition minus_alg :: "alg \<Rightarrow> alg \<Rightarrow> alg" is minus 
  apply (elim exE)
  apply (rule_tac p="of_int_poly p" and q="of_int_poly pa" in root_exist(2))
  by auto 

lift_definition times_alg :: "alg \<Rightarrow> alg \<Rightarrow> alg" is times 
  apply (elim exE)
  apply (rule_tac p="of_int_poly p" and q="of_int_poly pa" in root_exist(3))
  by auto 

lift_definition inverse_alg :: "alg \<Rightarrow> alg"  is inverse 
  apply (elim exE)
  apply (rule_tac p="of_int_poly p" in inverse_root_exist)
  by auto

definition "- x = (0::alg) - x"

definition "x div y = (x::alg) * (inverse y)"

instance proof
  fix a b c :: alg
  show "a + b = b + a"
    by transfer simp
  show "(a + b) + c = a + (b + c)"
    by transfer simp 
  show "0 + a = a"
    by transfer simp
  show "- a + a = 0" unfolding uminus_alg_def
    by transfer simp
  show "a - b = a + - b" unfolding uminus_alg_def
    by transfer simp
  show "(a * b) * c = a * (b * c)"
    by transfer auto
  show "a * b = b * a"
    by transfer simp
  show "1 * a = a"
    by transfer simp
  show "(a + b) * c = a * c + b * c"
    by transfer (simp add: distrib_right)
  show "(0::alg) \<noteq> (1::alg)"
    by transfer simp 
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
    by transfer simp
  show "a div b = a * inverse b" unfolding divide_alg_def
    by transfer simp
  show "inverse (0::alg) = 0"
    by transfer simp
qed

end


instantiation alg :: linordered_field
begin

lift_definition less_alg::"alg \<Rightarrow> alg \<Rightarrow> bool" is less .

lift_definition less_eq_alg::"alg \<Rightarrow> alg \<Rightarrow> bool" is less_eq .
  
definition abs_alg::"alg \<Rightarrow> alg" where
  "abs (a::alg) = (if a < 0 then - a else a)"

definition sgn_alg::"alg \<Rightarrow> alg" where
  "sgn (a::alg) = (if a = 0 then 0 else if 0 < a then 1 else - 1)"

instance proof
  fix a b c :: alg
  show "\<bar>a\<bar> = (if a < 0 then - a else a)"
    by (rule abs_alg_def)
  show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
    by transfer auto
  show "a \<le> a"
    by transfer simp
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    by transfer simp
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
    by transfer simp
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by transfer simp
  show "sgn a = (if a = 0 then 0 else if 0 < a then 1 else - 1)"
    by (rule sgn_alg_def)
  show "a \<le> b \<or> b \<le> a"
    by transfer auto
  show "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
    by transfer simp
qed
end


instantiation alg :: equal
begin

definition
  [code]: "HOL.equal (x::alg) y \<longleftrightarrow> HOL.equal (Rep_alg x) (Rep_alg y)"

instance proof
qed (simp add: equal_alg_def equal Rep_alg_inject)
end
 
end