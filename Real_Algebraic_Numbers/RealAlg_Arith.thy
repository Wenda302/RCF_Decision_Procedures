(*
    Author:     Wenda Li <wl302@cam.ac.uk>
*)
theory RealAlg_Arith 
  imports 
  RealAlg_Imp
begin

hide_const Fraction_Field.Fract

SML_import \<open>val println = Output.writeln\<close>
SML_import \<open>val zz_gcd = Integer.gcd\<close>
SML_import \<open>val zz_lcm = Integer.lcm\<close>
SML_import \<open>val pointerEq = pointer_eq\<close>

(*code from MetiTarski*)
SML_file "../MetiTarski_source/Random.sig" SML_file "../MetiTarski_source/Random.sml"
SML_file "../MetiTarski_source/Portable.sig" SML_file "../MetiTarski_source/PortablePolyml.sml"
SML_file "../MetiTarski_source/Polyhash.sig" SML_file "../MetiTarski_source/Polyhash.sml"
SML_file "../MetiTarski_source/Useful.sig" SML_file "../MetiTarski_source/Useful.sml"
SML_file "../MetiTarski_source/rat.sml"
SML_file "../MetiTarski_source/Lazy.sig" SML_file "../MetiTarski_source/Lazy.sml"
SML_file "../MetiTarski_source/Map.sig" SML_file "../MetiTarski_source/Map.sml"
SML_file "../MetiTarski_source/Ordered.sig" SML_file "../MetiTarski_source/Ordered.sml"
SML_file "../MetiTarski_source/KeyMap.sig" SML_file "../MetiTarski_source/KeyMap.sml"
SML_file "../MetiTarski_source/ElementSet.sig" SML_file "../MetiTarski_source/ElementSet.sml"
SML_file "../MetiTarski_source/Sharing.sig" SML_file "../MetiTarski_source/Sharing.sml"
SML_file "../MetiTarski_source/Stream.sig" SML_file "../MetiTarski_source/Stream.sml"
SML_file "../MetiTarski_source/Print.sig" SML_file "../MetiTarski_source/Print.sml"
SML_file "../MetiTarski_source/Parse.sig" SML_file "../MetiTarski_source/Parse.sml"
SML_file "../MetiTarski_source/Name.sig"  SML_file "../MetiTarski_source/Name.sml"
SML_file "../MetiTarski_source/NameArity.sig" SML_file "../MetiTarski_source/NameArity.sml"
SML_file "../MetiTarski_source/Term.sig" SML_file "../MetiTarski_source/Term.sml"
SML_file "../MetiTarski_source/Subst.sig" SML_file "../MetiTarski_source/Subst.sml"
SML_file "../MetiTarski_source/Atom.sig" SML_file "../MetiTarski_source/Atom.sml"
SML_file "../MetiTarski_source/Formula.sig" SML_file "../MetiTarski_source/Formula.sml"
SML_file "../MetiTarski_source/RCF/Common.sig" SML_file "../MetiTarski_source/RCF/Common.sml"
SML_file "../MetiTarski_source/RCF/Algebra.sig" SML_file "../MetiTarski_source/RCF/Algebra.sml"
SML_file "../MetiTarski_source/RCF/Groebner.sig" SML_file "../MetiTarski_source/RCF/Groebner.sml"
SML_file "../MetiTarski_source/RCF/SMT.sig" SML_file "../MetiTarski_source/RCF/SMT.sml"
SML_file "../MetiTarski_source/RCF/Resultant.sig" SML_file "../MetiTarski_source/RCF/Resultant.sml"
SML_file "../MetiTarski_source/RCF/IntvlsFP.sig" SML_file "../MetiTarski_source/RCF/IntvlsFP.sml"
SML_file "../MetiTarski_source/RCF/Sturm.sig" SML_file "../MetiTarski_source/RCF/Sturm.sml"

(*Modified a little by adding an implementation of substraction of real algebraic numbers*)
SML_file "../MetiTarski_source/RCF/RealAlg.sig" SML_file "../MetiTarski_source/RCF/RealAlg.sml"


(*interface to connect Isabelle/ML and MetiTarski*)
SML_file "RealAlg_Arith.sml"
SML_export \<open>
    val untrustedAdd = RealAlg_Arith.alg_add;
    val untrustedMult = RealAlg_Arith.alg_mult;
    val untrustedMinus = RealAlg_Arith.alg_minus;
    val untrustedInverse = RealAlg_Arith.alg_inverse\<close> 

consts alg_inverse:: "integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow>  (integer \<times> integer) \<times> (integer \<times> integer)"

consts alg_add:: "integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow> integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow> integer list \<times> (integer\<times> integer) \<times> (integer \<times> integer) \<times> ((integer \<times> integer) option)"

consts alg_mult:: "integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow> integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow> integer list \<times> (integer\<times> integer) \<times> (integer \<times> integer) \<times> ((integer \<times> integer) option)"

consts alg_minus:: "integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow> integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer) 
    \<Rightarrow> integer list \<times> (integer\<times> integer) \<times> (integer \<times> integer) \<times> ((integer \<times> integer) option)"


definition to_alg_code::"int poly \<Rightarrow> float \<Rightarrow> float \<Rightarrow> integer list \<times> (integer \<times> integer) \<times> (integer \<times> integer)" where
  "to_alg_code p lb ub = (let 
        (lb1,lb2) = quotient_of (rat_of_float lb);
        (ub1,ub2) = quotient_of (rat_of_float ub)
      in (map integer_of_int (coeffs p),(integer_of_int lb1,integer_of_int lb2)
          ,(integer_of_int ub1,integer_of_int ub2)) 
      )"

definition of_rat_code::"integer \<Rightarrow> integer \<Rightarrow> rat" where
  "of_rat_code r1 r2 =Fract (int_of_integer r1) (int_of_integer r2)"

definition of_alg_code::"integer list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow>
    int poly \<times> float \<times> float" where
  "of_alg_code ps lb1 lb2 ub1 ub2 = (poly_of_list (map int_of_integer ps)
    ,lapprox_rat 10 (int_of_integer lb1) (int_of_integer lb2), 
     rapprox_rat 10 (int_of_integer ub1) (int_of_integer ub2))"

code_printing constant alg_inverse \<rightharpoonup> (SML) "untrustedInverse"

code_printing constant alg_add \<rightharpoonup> (SML) "untrustedAdd"

code_printing constant alg_mult \<rightharpoonup> (SML) "untrustedMult"

code_printing constant alg_minus \<rightharpoonup> (SML) "untrustedMinus"

lemma poly_y_pcompose:"poly_y (pcompose p q) y = pcompose (poly_y p y) (poly_y q y)"
  apply (induct p)
  by (auto simp add:pcompose_pCons poly_y_add poly_y_mult)
  
lemma bpoly_pcompose:
  shows "bpoly (pcompose p q) x y =  bpoly p (bpoly q x y) y" 
unfolding bpoly_def  
  by (simp add:poly_y_pcompose poly_pcompose)

lemma alg_add_bsgn:
  fixes p1 p2 p3::"int poly" and lb1 lb2 lb3 ub1 ub2 ub3::"float"
  defines "x\<equiv>Alg p1 lb1 ub1" and "y\<equiv>Alg p2 lb2 ub2" and "z\<equiv>Alg p3 lb3 ub3"
        and "pxy\<equiv>[:[:0::real,1:],[:1:]:]"
  assumes valid:"valid_alg p3 lb3 ub3"
    and bsgn1:"bsgn_at (pcompose (lift_x (of_int_poly p3)) pxy) x y = 0"
    and bsgn2:"bsgn_at ([:[:Ratreal (- rat_of_float lb3),1:],[:1:]:]) x y > 0"
    and bsgn3:"bsgn_at ([:[:Ratreal (- rat_of_float ub3),1:],[:1:]:]) x y < 0"
  shows "Alg p3 lb3 ub3 = Alg p1 lb1 ub1 + Alg p2 lb2 ub2"
proof -
  def xy\<equiv>"x+y"
  have "poly (of_int_poly p3) xy = 0" 
    using bsgn1 unfolding bsgn_at_def pxy_def xy_def
    apply (auto simp add:sgn_zero_iff bpoly_pcompose)
    by (simp add:bpoly_def algebra_simps)
  moreover have "xy>real_of_float lb3"
    using bsgn2 unfolding bsgn_at_def pxy_def xy_def 
    by (auto simp:of_rat_minus)
  moreover have "xy<real_of_float ub3"
    using bsgn3 unfolding bsgn_at_def pxy_def xy_def 
    by (auto simp:of_rat_minus)
  ultimately show ?thesis using alg_eq[OF valid,of xy] unfolding xy_def x_def y_def by auto
qed

lemma alg_add_bsgn':
  fixes p1 p2::"int poly" and lb1 lb2 ub1 ub2::"float" and r::rat
  defines "x\<equiv>Alg p1 lb1 ub1" and "y\<equiv>Alg p2 lb2 ub2"
        and "pxy\<equiv>[:[:0::real,1:],[:1:]:]"
  assumes bsgn:"bsgn_at (pcompose (lift_x (of_rat_poly [:-r,1:])) pxy) x y = 0"
  shows "of_rat r = Alg p1 lb1 ub1 + Alg p2 lb2 ub2"
using bsgn unfolding pxy_def bsgn_at_def
apply (fold x_def y_def)
by (auto simp add:sgn_zero_iff bpoly_pcompose of_rat_minus)

lemma alg_minus_bsgn:
  fixes p1 p2 p3::"int poly" and lb1 lb2 lb3 ub1 ub2 ub3::"float"
  defines "x\<equiv>Alg p1 lb1 ub1" and "y\<equiv>Alg p2 lb2 ub2" and "z\<equiv>Alg p3 lb3 ub3"
        and "pxy\<equiv>[:[:0::real,-1:],[:1:]:]"
  assumes valid:"valid_alg p3 lb3 ub3"
    and bsgn1:"bsgn_at (pcompose (lift_x (of_int_poly p3)) pxy) x y = 0"
    and bsgn2:"bsgn_at [:[:Ratreal (- rat_of_float lb3),-1:],[:1:]:] x y > 0"
    and bsgn3:"bsgn_at [:[:Ratreal (- rat_of_float ub3),-1:],[:1:]:] x y < 0"
  shows "Alg p3 lb3 ub3 = Alg p1 lb1 ub1 - Alg p2 lb2 ub2"
proof -
  def xy\<equiv>"x-y"
  have "poly (of_int_poly p3) xy = 0" 
    using bsgn1 unfolding bsgn_at_def pxy_def xy_def
    apply (auto simp add:sgn_zero_iff bpoly_pcompose)
    by (simp add:bpoly_def algebra_simps)
  moreover have "xy>real_of_float lb3 \<and> xy<real_of_float ub3" 
    using bsgn2 bsgn3 unfolding bsgn_at_def pxy_def xy_def by (auto simp:of_rat_minus)
  ultimately show ?thesis using alg_eq[OF valid,of xy] unfolding xy_def x_def y_def by auto
qed

lemma alg_minus_bsgn':
  fixes p1 p2::"int poly" and lb1 lb2 ub1 ub2::float and r::rat
  defines "x\<equiv>Alg p1 lb1 ub1" and "y\<equiv>Alg p2 lb2 ub2"
        and "pxy\<equiv>[:[:0::real,-1:],[:1:]:]"
  assumes bsgn:"bsgn_at (pcompose (lift_x (of_rat_poly [:-r,1:])) pxy) x y = 0"
  shows "of_rat r = Alg p1 lb1 ub1 - Alg p2 lb2 ub2"
using bsgn unfolding pxy_def bsgn_at_def
apply (fold x_def y_def)
by (auto simp add:sgn_zero_iff bpoly_pcompose of_rat_minus)

lemma alg_mult_bsgn:
  fixes p1 p2 p3::"int poly" and lb1 lb2 lb3 ub1 ub2 ub3::"float"
  defines "x\<equiv>Alg p1 lb1 ub1" and "y\<equiv>Alg p2 lb2 ub2" and "z\<equiv>Alg p3 lb3 ub3"
        and "pxy\<equiv>[:0,[:0,1::real:]:]"
  assumes valid:"valid_alg p3 lb3 ub3"
    and bsgn1:"bsgn_at (pcompose (lift_x (of_int_poly p3)) pxy) x y = 0"
    and bsgn2:"bsgn_at [:[:Ratreal (- rat_of_float lb3):],[:0,1:]:] x y > 0"
    and bsgn3:"bsgn_at [:[:Ratreal (- rat_of_float ub3):],[:0,1:]:] x y < 0"
  shows "Alg p3 lb3 ub3 = Alg p1 lb1 ub1 * Alg p2 lb2 ub2"
proof -
  def xy\<equiv>"x*y"
  have "poly (of_int_poly p3) xy = 0" 
    using bsgn1 unfolding bsgn_at_def pxy_def xy_def
    apply (auto simp add:sgn_zero_iff bpoly_pcompose)
    by (simp add:bpoly_def algebra_simps)
  moreover have "xy>real_of_float lb3 \<and> xy<real_of_float ub3"
     using bsgn2 bsgn3 unfolding bsgn_at_def pxy_def xy_def by (auto simp:of_rat_minus)
  ultimately show ?thesis using alg_eq[OF valid,of xy] unfolding xy_def x_def y_def by auto
qed

lemma alg_minus_code:
  assumes valid:"valid_alg p lb ub"
  shows "-Alg p lb ub = Alg (pcompose p [:0,-1:]) (-ub) (-lb)"
proof -
  def x\<equiv>"Alg p lb ub" and q\<equiv>"pcompose p [:0,-1:]"
  have "poly (of_int_poly p) x=0" and "real_of_float lb<x" and "x<real_of_float ub" 
    using alg_bound_and_root[OF valid] unfolding x_def by auto
  moreover hence "poly (of_int_poly q) (-x) =0"
    unfolding q_def by (simp add:poly_pcompose)
  moreover have "valid_alg q (-ub) (-lb)"
    proof -
      def S\<equiv>"roots_btw (of_int_poly p) (real_of_float lb) (real_of_float ub)" 
        and S'\<equiv>"roots_btw (of_int_poly q) (-real_of_float ub) (-real_of_float lb)"
      have "\<And>y. y\<in>S \<longleftrightarrow> -y \<in> S'" 
        unfolding S_def S'_def roots_btw_def q_def
        by (auto simp add:poly_pcompose of_rat_minus)
      hence "card S= card S'" 
        apply (intro Fun.bij_betw_byWitness[THEN bij_betw_same_card,of _ uminus uminus])
        by force+
      thus ?thesis using valid unfolding valid_alg_def 
        apply simp
        apply (fold S_def S'_def)
        by (auto simp add:of_rat_minus q_def poly_pcompose algebra_simps)
    qed
  ultimately have  "- x = Alg q (-ub) (-lb)" 
    by (intro alg_eq,auto simp add:of_rat_minus)
  thus ?thesis unfolding x_def q_def by auto
qed

definition rat_to_alg::"rat \<Rightarrow> int poly \<times> float \<times> float" where
  "rat_to_alg r = (
      if r=0 then 
        ([:0,1:],-1,1) 
      else if r>0 then (
        let
          (r1,r2) = quotient_of r;
          lb = lapprox_rat 0 r1 r2 * Float 1 (-1);
          ub = rapprox_rat 0 r1 r2 * Float 1 1
        in
          ([:-r1,r2:],lb,ub)
      ) else (
        let
          (r1,r2) = quotient_of r;
          lb = lapprox_rat 0 r1 r2*Float 1 1;
          ub =  rapprox_rat 0 r1 r2 * Float 1 (-1)
        in
          ([:-r1,r2:],lb,ub)
      ))"

lemma rat_to_alg_eq:"of_rat r = (let (p,lb,ub) = rat_to_alg r in Alg p lb ub)"
proof (cases "r=0")
  case True
  moreover have "0 = Alg [:0, 1:] (- 1) 1"
  proof (rule alg_eq)
    have "{x::real. x = 0 \<and> - 1 < x \<and> x < 1} = {0}" by auto
    then show "valid_alg [:0, 1:] (- 1) 1" unfolding valid_alg_def roots_btw_def by simp
  qed auto
  then show ?thesis unfolding rat_to_alg_def using True by auto
next
  case False
  obtain p lb ub where to_alg:"rat_to_alg r = (p,lb,ub)" by (metis prod_cases3)  
  obtain r1 r2 where r1r2:"quotient_of r = (r1,r2)" by (metis small_lazy'.cases)
  let ?lb = "real_of_float lb" and ?ub = "real_of_float ub"
  have p_alt:"p=[:-r1,r2:]"
    using to_alg  False unfolding rat_to_alg_def Let_def r1r2 by (auto split:if_splits)
  have "r2>0" using quotient_of_denom_pos[OF r1r2] .

  have r_btw:"real_of_float lb<of_rat r \<and> of_rat r<real_of_float ub" 
  proof (cases "r>0")
    case True
    then have "real_of_float lb = real_of_float (lapprox_rat 0 r1 r2 * Float 1 (- 1))"
      using to_alg r1r2 unfolding rat_to_alg_def by auto
    also have "... \<le> (real_of_int r1 / real_of_int r2) / 2"
      using lapprox_rat[of 0 r1 r2] by (auto simp add:powr_neg_one)
    also have "... < of_rat r"
      using \<open>r2>0\<close> True unfolding quotient_of_div[OF r1r2]  
      by (auto simp add:of_rat_divide field_simps)
    finally have *:"real_of_float lb < real_of_rat r" .
    have "real_of_rat r < real_of_float (rapprox_rat 0 r1 r2 * Float 1 1)"
      using rapprox_rat[of r1 r2 0]  \<open>r2>0\<close> True unfolding quotient_of_div[OF r1r2]  
      by (auto simp add:of_rat_divide field_simps)
    also have "... = real_of_float ub"
      using to_alg r1r2 True unfolding rat_to_alg_def by auto
    finally have "real_of_rat r < real_of_float ub" .
    with * show ?thesis by simp
  next
    case False
    then have "r<0" using \<open>r\<noteq>0\<close> by auto
    then have "real_of_float lb = real_of_float (lapprox_rat 0 r1 r2 * Float 1 1)"
      using to_alg r1r2 unfolding rat_to_alg_def by auto
    also have "... < of_rat r"
      using lapprox_rat[of 0 r1 r2] \<open>r2>0\<close> \<open>r<0\<close> unfolding quotient_of_div[OF r1r2]  
      by (auto simp add:of_rat_divide field_simps)
    finally have *:"real_of_float lb < of_rat r" .
    have "real_of_rat r < real_of_float (rapprox_rat 0 r1 r2 * Float 1 (-1))"
      using rapprox_rat[of r1 r2 0]  \<open>r2>0\<close> \<open>r<0\<close> unfolding quotient_of_div[OF r1r2]  
      by (auto simp add:of_rat_divide field_simps powr_neg_one)
    also have "... = real_of_float ub"
      using to_alg r1r2 \<open>r<0\<close> unfolding rat_to_alg_def by auto
    finally have "real_of_rat r < real_of_float ub" .
    with * show ?thesis by simp
  qed
  moreover have "valid_alg p lb ub"
  proof -
    have "lb < ub" using r_btw by auto
    moreover have "poly (of_int_poly p) lb * poly (of_int_poly p) ub < 0"
      using r_btw \<open>r2>0\<close> unfolding p_alt quotient_of_div[OF r1r2] 
      by (auto simp add:of_rat_divide divide_simps mult_neg_pos)
    moreover have "card (roots_btw (of_int_poly p) ?lb ?ub) = 1"
    proof -
      have "{x. poly (of_int_poly p) x = 0 \<and> ?lb < x \<and> x < ?ub} = {of_rat r}"
        using \<open>r2>0\<close> r_btw unfolding quotient_of_div[OF r1r2] p_alt
        by (auto simp add:of_rat_divide divide_simps mult_neg_pos)
      then show ?thesis unfolding roots_btw_def by auto
    qed
    ultimately show ?thesis unfolding valid_alg_def by auto
  qed
  moreover have "poly (of_int_poly p) (of_rat r) = 0"
    using r_btw \<open>r2>0\<close> unfolding p_alt quotient_of_div[OF r1r2]
    by (auto simp add:of_rat_divide divide_simps)
  ultimately show ?thesis using alg_eq unfolding to_alg by auto
qed

definition ter_ub :: "int poly \<Rightarrow> rat \<Rightarrow> nat" where
  "ter_ub p ub = (let 
                  x= Real (to_cauchy (of_int_poly p, 0, ub)) 
               in
                  (LEAST n. (of_rat ub)/2^n < x))"

definition ter_lb :: "int poly \<Rightarrow> rat \<Rightarrow> nat" where
  "ter_lb p lb = (let 
                  x= Real (to_cauchy (of_int_poly p, lb, 0)) 
               in
                  (LEAST n. x<(of_rat lb)/2^n ))"

lemma vanishes_shift:
  assumes "cauchy X" and shift:"\<And>n. X (n+k) = Y n"
  shows "vanishes (\<lambda>n. X n - Y n)"
unfolding vanishes_def
proof clarify
  fix r::rat assume "r>0"
  obtain k1 where k1:"\<forall>m\<ge>k1.\<forall>n\<ge>k1. \<bar>X m - X n\<bar> < r" 
    using `cauchy X` `0 < r` unfolding cauchy_def 
    using  half_gt_zero_iff by blast
  have "\<forall>m\<ge>k1. \<bar>X m - X (m+k)\<bar> < r"
    using k1 by auto
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>X n - Y n\<bar> < r" using shift by auto
qed

(* something useful for the next version
lemma ter_lb_Suc:
  fixes p::"int poly" and lb ::rat
  assumes "lb<0" 
    and sgn_diff1: "poly (of_int_poly p) lb * poly (of_int_poly p) 0 <0" 
    and sgn_diff2:"poly p (lb/2) * poly p 0 > 0"
  shows "ter_lb p lb = Suc (ter_ub p (lb/2))"
sorry
*)

lemma power_Archimedean':
  fixes x y a::real
  assumes "x>0" "a>1"
  shows "\<exists>n. y < a^n * x" 
proof (cases "y>0")
  assume "\<not> 0 < y" 
  thus " \<exists>n. y < a ^ n * x" using assms 
    apply (rule_tac x=0 in exI)
    by auto
next
  assume "y>0"
  obtain n::nat where "of_nat n > log a (y/x)" 
    using reals_Archimedean2 by auto
  hence "a powr (of_nat n) > a powr (log a (y/x))" 
    by (intro powr_less_mono,auto simp add:`a>1`)
  hence "a ^ n > y/x"  using `y>0` `x>0` `a>1`
    apply (subst (asm) powr_realpow,simp)
    by (subst (asm) powr_log_cancel,auto)
  thus "\<exists>n. y < a ^ n * x" by (auto simp add:field_simps `x>0`)
qed

lemma ter_ub_Suc:
  fixes p::"int poly" and ub ::rat
  assumes "ub>0" 
    and sgn_diff1: "poly (of_int_poly p) 0 * poly (of_int_poly p) ub <0" 
    and sgn_diff2:"poly (of_int_poly p) 0 * poly (of_int_poly p) (ub/2) \<le> 0"
  shows "ter_ub p ub = Suc (ter_ub p (ub/2))"
proof -
  define X where "X\<equiv>to_cauchy (of_int_poly p, 0, ub)"
  define Y where "Y\<equiv>to_cauchy (of_int_poly p, 0, ub/2)"
  define x y where "x\<equiv>Real X" and "y\<equiv>Real Y"
  define P1 P2 where "P1\<equiv>\<lambda>n. (of_rat ub)/2^n < x" and "P2\<equiv>\<lambda>n. (of_rat (ub/2))/2^n < y"  
  define ter1 ter2 where "ter1\<equiv>ter_ub p ub" and "ter2\<equiv>ter_ub p (ub/2)"
  have ter1:"ter1= (LEAST n. P1 n)" and ter2:"ter2=(LEAST n. P2 n)"
    unfolding ter1_def P1_def ter2_def P2_def ter_ub_def x_def X_def y_def Y_def 
    by auto
  have "x=y"
  proof -
    have "\<And>n.  Y n = X (Suc n)"
      unfolding X_def Y_def using sgn_diff2 
      by (simp add:Let_def of_int_poly_poly)
    moreover have "cauchy X" and "cauchy Y"
      unfolding X_def Y_def
      by (auto simp:to_cauchy_cauchy `ub>0`)
    ultimately show ?thesis
      unfolding x_def y_def
      apply (auto simp add: eq_Real cauchy_def vanishes_def)
      by (meson le_less le_less_trans lessI)
  qed
  have "x>0" and "x<of_rat ub"
    using to_cauchy_bound'[OF `ub>0` sgn_diff1] unfolding x_def X_def by auto
  have p12:"\<And>n. P1 (Suc n) \<longleftrightarrow> P2 n"
    unfolding P1_def P2_def `x=y`
    by (auto simp add:field_simps of_rat_divide)
  have "P1 ter1" and "P2 ter2" 
  proof -
    have "\<exists>n. P1 n" and "\<exists>n. P2 n"
      unfolding P1_def P2_def
      using power_Archimedean'[OF `x>0`,of 2] 
      by (auto simp add:field_simps of_rat_power `x=y`) 
    thus "P1 ter1" and "P2 ter2" using LeastI_ex unfolding ter1 ter2 by auto 
  qed
  have "ter1 \<le>Suc ter2" 
    using Least_le[of P1 "Suc ter2",folded ter1] p12[of ter2] `P2 ter2` by auto
  moreover have "Suc ter2 \<le> ter1"
  proof -
    have "ter1\<noteq>0"
    proof
      assume "ter1=0"
      hence "of_rat ub<x" using `P1 ter1` unfolding P1_def by auto
      thus False using `x<of_rat ub` by auto
    qed
    thus ?thesis
      using Least_le[of P2 "nat.pred ter1",folded ter2] 
        p12[of "nat.pred ter1",symmetric] `P1 ter1` `ter1\<noteq>0`
      apply (subgoal_tac "ter1=Suc (nat.pred ter1)")
      by auto
  qed
  ultimately have "ter1=Suc ter2" by auto
  thus ?thesis unfolding ter1_def ter2_def .
qed

function refine_pos::"int poly \<Rightarrow> rat \<Rightarrow> (rat \<times> rat) \<times> rat option " where
  "refine_pos p ub = (
      if ub\<le>0 \<or> poly (of_int_poly p) 0 * poly (of_int_poly p) ub \<ge>0 then 
        undefined
      else if poly (of_int_poly p) 0 * poly (of_int_poly p) (ub/2) <0 then
        refine_pos p (ub/2)
      else if poly (of_int_poly p) (ub/2) =0 then
        (undefined,Some (ub/2))
      else
        ((ub/2,ub),None))
      "
by auto
termination
  apply (relation "measure (\<lambda>(p,ub).  ter_ub p ub )")
  apply auto
  using ter_ub_Suc
  by (metis le_less lessI not_less of_int_0 of_int_poly_def of_int_poly_poly)


(* something useful for the next version
lemma
  fixes p::"int poly" and ub ub' lb'::rat
  assumes "ub>0" and sgn_diff:"poly (of_int_poly p) 0 * poly (of_int_poly p) ub < 0"
  defines
    "X\<equiv> (\<lambda>p ub. to_cauchy (of_int_poly p, 0, ub))" and
    "Y\<equiv> (\<lambda>p ub. case refine_pos p ub of
            (_,Some r) \<Rightarrow> (\<lambda>n. r) | 
            ((lb',ub'),None) \<Rightarrow> to_cauchy (of_int_poly p, lb',ub'))"
  shows "\<exists>k. X p ub (n+k) = Y p ub n" using `ub>0` sgn_diff
proof (induct rule:refine_pos.induct[of _ p ub])
  case (1 p ub)
  obtain k where k:" X p (ub / 2) (n + k) = Y p (ub / 2) n" sorry
  show ?case using k "1.prems" unfolding X_def Y_def
    apply (rule_tac x="if poly (of_int_poly p) 0 * poly (of_int_poly p) (ub / 2) < 0 
        then Suc k  else if poly (of_int_poly p) (ub/2) = 0 then undefined  else 1" in exI)
    apply (subst refine_pos.simps)
    apply (auto simp del:refine_pos.simps simp add: Let_def)


lemma
  fixes p::"int poly" and ub ub' lb'::rat
  assumes "ub>0" and sgn_diff:"poly (of_int_poly p) 0 * poly (of_int_poly p) ub < 0"
  defines
    "r \<equiv> refine_pos p ub" 
  defines
    "x\<equiv> Real (to_cauchy (of_int_poly p, 0, ub))" and
    "y\<equiv> Real (to_cauchy (of_int_poly p, fst r, snd r))"
  shows "x=y" using sgn_diff
proof (induct rule:refine_pos.induct)
 
*)

(*
It would be interesting to have such function, but certifying its termination seems not so easy :-(

function refine_alg:: "int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int poly \<times> rat \<times> rat" where
  "refine_alg p lb ub = (
      if lb>0 \<or> ub <0 \<or> poly (of_int_poly p) lb * poly (of_int_poly p) ub \<ge>0   then 
        (p,lb,ub) 
      else 
        let c=(if lb<0 \<and> ub>0 then 0 else (lb+ub)/2) 
        in
          if  poly (of_int_poly p) lb * poly (of_int_poly p) c \<le>0  then refine_alg p lb c
                                    else refine_alg p c ub)"
by auto

termination
  apply (relation "measure (\<lambda>(p,lb,ub). if lb=0 then ter_ub p ub else ter_lb p lb)")
  apply auto
oops
*)

lemma alg_inverse_code:
  assumes valid1:"valid_alg p a1 b1" and valid2:"valid_alg (rev_poly p) a2 b2" 
    and ineq_asm:"(a2>0 \<and> a2 * b1 \<ge> 1 \<and> a1 * b2 \<le> 1) \<or> (b2<0 \<and> a2*b1 \<le> 1 \<and> a1 * b2\<ge>1)"
  shows "inverse (Alg p a1 b1) = (
      if a1 < 0 \<and> 0 < b1 \<and> poly p 0=0 then 0 else Alg (rev_poly p) a2 b2)"
proof -
  have ?thesis when "a1 < 0 \<and> 0 < b1 \<and> poly p 0=0"
  proof -
    have "0 = Alg p a1 b1"
      apply (rule alg_eq[OF valid1,of 0])
      using that by (auto,metis of_int_0 of_int_poly_poly)
    then show ?thesis using that by auto
  qed
  moreover have ?thesis when "\<not>(a1 < 0 \<and> 0 < b1 \<and> poly p 0=0)" 
  proof -
    define x1 where "x1=Alg p a1 a2"
    define x2 where "x2=Alg (rev_poly p) a2 b2"
    then have *:"real_of_float a2 < x2 \<and> x2 < real_of_float b2" "x2\<noteq>0"
      using alg_bound_and_root[OF valid2] ineq_asm by auto
    from this(1) ineq_asm
    have "inverse (real_of_float b2) < inverse x2 \<and> inverse x2 < inverse (real_of_float a2)"
      by auto
    moreover have "real_of_float a1 \<le> inverse (real_of_float b2)"
        "inverse (real_of_float a2) \<le> real_of_float b1"
      using ineq_asm * by (auto simp add:field_simps)
    ultimately have "real_of_float a1 < inverse x2 \<and> inverse x2 < real_of_float b1"
      by auto
    moreover have "poly (of_int_poly p) (inverse x2) = 0"
      apply (subst rev_poly_poly_iff[symmetric])
      subgoal using \<open>x2\<noteq>0\<close> by auto
      subgoal using alg_bound_and_root[OF valid2,folded x2_def] by (simp add: of_int_poly_rev_poly)
      done
    ultimately have "Alg p a1 b1 = inverse x2"
      using alg_eq[OF valid1,of "inverse x2"] by auto
    then show ?thesis using that(1) unfolding x2_def by auto 
  qed
  ultimately show ?thesis by auto
qed

lemma [code]:"inverse (Alg p1 lb1 ub1) = 
        (if valid_alg p1 lb1 ub1 then 
            if lb1 < 0 \<and> 0<ub1 \<and> poly p1 0 =0 then
              0
            else 
              let ((lb2_1,lb2_2),(ub2_1,ub2_2)) = alg_inverse (to_alg_code p1 lb1 ub1);
                  lb2 = lapprox_rat 10 (int_of_integer lb2_1) (int_of_integer lb2_2);
                  ub2 = rapprox_rat 10 (int_of_integer ub2_1) (int_of_integer ub2_2);
                  p2 = rev_poly p1   
              in         
                (if valid_alg p2 lb2 ub2 \<and> 
                  ((lb2>0 \<and> lb2 * ub1 \<ge> 1 \<and> lb1 * ub2 \<le> 1) \<or> (ub2<0 \<and> lb2*ub1 \<le> 1 \<and> lb1 * ub2\<ge>1)) 
                then 
                   Alg p2 lb2 ub2
                else 
                  Code.abort (STR ''alg_inverse fails to compute a valid answer'') 
                    (%_. inverse (Alg p1 lb1 ub1))
                )
         else 
            Code.abort (STR ''invalid Alg'') (%_. inverse (Alg p1 lb1 ub1)))"
proof -
  have ?thesis when "lb1 < 0 \<and> 0<ub1 \<and> poly p1 0 =0" 
  proof (cases "valid_alg p1 lb1 ub1")
    case True
    have "0 = Alg p1 lb1 ub1"
      apply (rule alg_eq[OF True,of 0])
      using that by (auto,metis of_int_0 of_int_poly_poly)
    then show ?thesis using that by auto
  next
    case False
    then show ?thesis by auto
  qed
  moreover have ?thesis when "\<not> (lb1 < 0 \<and> 0<ub1 \<and> poly p1 0 =0)"
    using that alg_inverse_code[of p1 lb1 ub1,symmetric] 
    by (auto simp add:Let_def split: prod.split option.split)
  ultimately show ?thesis by fastforce
qed

lemma [code]:"- Alg p lb ub = 
        (if valid_alg p lb ub then 
            Alg (pcompose p [:0,-1:]) (-ub) (-lb)
         else 
            Code.abort (STR ''invalid Alg'') (%_. - Alg p lb ub))"
using alg_minus_code by auto

lemma [code]:"Alg p1 lb1 ub1 + Alg p2 lb2 ub2 = 
    (if valid_alg p1 lb1 ub1 \<and> valid_alg p2 lb2 ub2 then
      (let     
        (ns,(lb3_1,lb3_2),(ub3_1,ub3_2),r') = alg_add (to_alg_code p1 lb1 ub1) (to_alg_code p2 lb2 ub2)
      in
        (case r' of
          None \<Rightarrow>  (let (p3,lb3,ub3) = of_alg_code ns lb3_1 lb3_2 ub3_1 ub3_2 in
                    (if (valid_alg p3 lb3 ub3 \<and>
                        bsgn_at (pcompose (lift_x (of_int_poly p3)) [:[:0, 1:], [:1:]:]) 
                          (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) = 0 \<and>
                         bsgn_at ([:[:Ratreal (- rat_of_float lb3),1:],[:1:]:]) (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) > 0
                         \<and> 
                        bsgn_at ([:[:Ratreal (- rat_of_float ub3),1:],[:1:]:]) (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) < 0)
                     then 
                        Alg p3 lb3 ub3
                     else
                        Code.abort (STR ''alg_add fails to compute a valid answer'') 
                          (%_. Alg p1 lb1 ub1 + Alg p2 lb2 ub2)))|
          Some (r1,r2) \<Rightarrow> ( let r = of_rat_code r1 r2 in
                            (if bsgn_at (pcompose (lift_x (of_rat_poly [:- r, 1:])) [:[:0, 1:], [:1:]:])
                            (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) = 0
                         then
                            Ratreal r 
                         else 
                            Code.abort (STR ''alg_add fails to compute a valid answer'') 
                              (%_. Alg p1 lb1 ub1 + Alg p2 lb2 ub2))
                        )
      ))
    else 
      Code.abort (STR ''alg_add fails to compute a valid answer'') (%_. Alg p1 lb1 ub1 + Alg p2 lb2 ub2)
    )" 
using alg_add_bsgn[of _ _ _ p1 lb1 ub1 p2 lb2 ub2,symmetric]  
  alg_add_bsgn'[of _ p1 lb1 ub1 p2 lb2 ub2,symmetric]
by (auto simp add:Let_def split: prod.split  option.split)

lemma [code]:"Alg p1 lb1 ub1 - Alg p2 lb2 ub2 = 
  (if valid_alg p1 lb1 ub1 \<and> valid_alg p2 lb2 ub2 then
    (let     
      (ns,(lb3_1,lb3_2),(ub3_1,ub3_2),r') = alg_minus (to_alg_code p1 lb1 ub1) (to_alg_code p2 lb2 ub2)
     
    in
      (case r' of
        None \<Rightarrow>  (let (p3,lb3,ub3) = of_alg_code ns lb3_1 lb3_2 ub3_1 ub3_2 in
                    (if (valid_alg p3 lb3 ub3 \<and>
                        bsgn_at (pcompose (lift_x (of_int_poly p3)) [:[:0, -1:], [:1:]:]) 
                          (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) = 0 \<and>
                        bsgn_at [:[:Ratreal (- rat_of_float lb3),-1:],[:1:]:] (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) > 0 \<and>
                        bsgn_at [:[:Ratreal (- rat_of_float ub3),-1:],[:1:]:] (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) < 0)
                     then 
                        Alg p3 lb3 ub3
                     else
                        Code.abort (STR ''alg_add fails to compute a valid answer'') 
                          (%_. Alg p1 lb1 ub1 - Alg p2 lb2 ub2)))|
        Some (r1,r2) \<Rightarrow> ( let r = of_rat_code r1 r2 in
                            (if bsgn_at (pcompose (lift_x (of_rat_poly [:- r, 1:])) [:[:0, -1:], [:1:]:])
                            (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) = 0
                         then
                            Ratreal r 
                         else 
                            Code.abort (STR ''alg_add fails to compute a valid answer'') 
                              (%_. Alg p1 lb1 ub1 - Alg p2 lb2 ub2))
                        )))
   else 
      Code.abort (STR ''alg_add fails to compute a valid answer'') 
      (%_. Alg p1 lb1 ub1 - Alg p2 lb2 ub2))
" 
using alg_minus_bsgn[of _ _ _ p1 lb1 ub1 p2 lb2 ub2,symmetric]  
  alg_minus_bsgn'[of _ p1 lb1 ub1 p2 lb2 ub2,symmetric]
by (auto simp add:Let_def split:prod.split option.split)   
                                                             
lemma [code]:"Alg p1 lb1 ub1 * Alg p2 lb2 ub2 = 
  (if valid_alg p1 lb1 ub1 \<and> valid_alg p2 lb2 ub2 then 
      (let     
        (ns,(lb3_1,lb3_2),(ub3_1,ub3_2),_) = alg_mult (to_alg_code p1 lb1 ub1) (to_alg_code p2 lb2 ub2);
        (p3,lb3,ub3) = of_alg_code ns lb3_1 lb3_2 ub3_1 ub3_2
       in
        (if (valid_alg p3 lb3 ub3 \<and>
            bsgn_at (pcompose (lift_x (of_int_poly p3)) [:0, [:0,1:]:]) 
              (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) = 0 \<and>
             bsgn_at ([:[:Ratreal (- rat_of_float lb3):],[:0,1:]:])  (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) > 0 \<and>
             bsgn_at ([:[:Ratreal (- rat_of_float ub3):],[:0,1:]:])  (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) < 0)
         then 
            Alg p3 lb3 ub3
         else
            Code.abort (STR ''alg_mult fails to compute a valid answer'') 
            (%_. Alg p1 lb1 ub1 * Alg p2 lb2 ub2)))
    else
        Code.abort (STR ''invalid alg in alg mult'') 
        (%_. Alg p1 lb1 ub1 * Alg p2 lb2 ub2))
   " 
using alg_mult_bsgn[of _ _ _ p1 lb1 ub1 p2 lb2 ub2,symmetric]
by (auto simp add:prod.split)

lemma [code]: "Alg p1 lb1 ub1 / Alg p2 lb2 ub2 = Alg p1 lb1 ub1 * (inverse (Alg p2 lb2 ub2))"
  using Real.divide_real_def by auto

(*TODO: This can be optimized by exploiting something like
    poly (pcompose p [:-r1,r2:]) (Alg p lb ub + r) =0
  where r=(of_int r1)/(of_int r2)
 *)
lemma [code]:
  "Alg p lb ub + Ratreal r = (let (p', lb', ub') = rat_to_alg r in Alg p lb ub +  Alg p' lb' ub')"
  "Ratreal r + Alg p lb ub = (let (p', lb', ub') = rat_to_alg r in Alg p' lb' ub'+ Alg p lb ub)"
  "Alg p lb ub - Ratreal r = (let (p', lb', ub') = rat_to_alg r in Alg p lb ub -  Alg p' lb' ub')"
  "Ratreal r - Alg p lb ub = (let (p', lb', ub') = rat_to_alg r in Alg p' lb' ub' - Alg p lb ub )"
  "Alg p lb ub * Ratreal r = (let (p', lb', ub') = rat_to_alg r in Alg p lb ub *  Alg p' lb' ub')"
  "Ratreal r * Alg p lb ub = (let (p', lb', ub') = rat_to_alg r in Alg p' lb' ub' * Alg p lb ub)"
  "Alg p lb ub / Ratreal r = (let (p', lb', ub') = rat_to_alg r in Alg p lb ub /  Alg p' lb' ub')"
  "Ratreal r / Alg p lb ub = (let (p', lb', ub') = rat_to_alg r in Alg p' lb' ub' / Alg p lb ub)"
  using rat_to_alg_eq[of r]
  by (auto split:prod.split)

lemma alg_sgn_code:
  fixes p::"int poly" and lb ub ::float
  defines "x\<equiv>Alg p lb ub"
  assumes valid:"valid_alg p lb ub"
  shows "if lb\<ge>0 then x>0 else if ub\<le>0 then x<0 else 
    sgn x= sgn_at_core_old [:0,1:] p lb ub"
proof -
  have "x>real_of_float lb" and "x<real_of_float ub" and "lb<ub" 
    using alg_bound_and_root[OF valid,folded x_def] valid by (auto simp add:valid_alg_def)
  hence "lb\<ge>0 \<or> ub\<le>0 \<Longrightarrow> ?thesis" 
    using order.strict_trans[of x "real_of_float ub" 0,simplified] 
          order.strict_trans[of 0 "real_of_float lb" x,simplified]
    by auto
  moreover have "\<not> (lb\<ge>0 \<or> ub\<le>0) \<Longrightarrow> ?thesis"
  proof -
    assume asm:"\<not> (lb\<ge>0 \<or> ub\<le>0)"
    have "sgn x = sgn (poly [:0,1:] x)" by auto
    also have "... = sgn_at_core_old [:0,1:] p lb ub"
      using sgn_at_core_old[OF valid,symmetric] unfolding x_def by blast
    finally have "sgn x = sgn_at_core_old [:0,1:] p lb ub" .
    then show ?thesis using asm by auto
  qed
  ultimately show ?thesis by auto
qed

lemma [code]: "sgn (Alg p lb ub) =  
        (if valid_alg p lb ub then 
            if lb \<ge> 0 then 1
            else if ub \<le> 0 then -1
            else sgn_at_core_old [:0,1:] p lb ub
         else 
            Code.abort (STR ''invalid Alg'') (%_. sgn (Alg p lb ub)))"
using alg_sgn_code[of p lb ub]
by auto

lemma [code]: "sgn (Ratreal r) = Ratreal (sgn r)" unfolding sgn_if by auto

(*could be refined further for computational efficiency by eliminating the minus operation*)
definition compare::"real \<Rightarrow> real \<Rightarrow> real" where
  "compare x y = sgn (x-y)"

lemma [code]: "(x::real)<y = (compare x y =-1)"
  unfolding compare_def sgn_if by auto

lemma [code]: "(x::real)\<le>y = (let s=compare x y in s=-1 \<or> s=0)"
  unfolding compare_def sgn_if by auto

lemma [code]: "(HOL.equal (Alg p1 lb1 ub1) (Alg p2 lb2 ub2)) 
    \<longleftrightarrow> (compare (Alg p1 lb1 ub1) (Alg p2 lb2 ub2) = 0)"
  "(HOL.equal (Ratreal r) (Alg p2 lb2 ub2)) 
    \<longleftrightarrow> (compare (Ratreal r) (Alg p2 lb2 ub2) = 0)"
  "(HOL.equal (Alg p2 lb2 ub2) (Ratreal r)) 
    \<longleftrightarrow> (compare (Alg p2 lb2 ub2) (Ratreal r) = 0)"
  unfolding compare_def sgn_if equal_real_def by auto

end