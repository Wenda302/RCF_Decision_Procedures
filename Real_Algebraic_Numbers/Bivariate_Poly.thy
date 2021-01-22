theory Bivariate_Poly imports 
  Poly_Maps
  More_PolyMisc
begin


section{*bivariate polynomials*}

type_synonym 'a bpoly = "'a poly poly"

definition poly_y:: "'a::{comm_semiring_0} bpoly \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "poly_y p y= map_poly (\<lambda>p'. poly p' y) p"

definition poly_x:: "'a::{comm_semiring_0} bpoly \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "poly_x p x= poly p [:x:]"

definition bpoly :: "'a::comm_semiring_0 bpoly \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "bpoly p x y = poly (poly_y p y) x"

definition lift_to_y::"'a::zero poly \<Rightarrow> 'a bpoly" where
  "lift_to_y p= [:p:]"

definition lift_x::"'a::zero poly \<Rightarrow> 'a bpoly" where
  "lift_x p = map_poly (\<lambda>x. [:x:]) p"

lemma poly_y_0[simp]: "poly_y 0 y = 0" unfolding poly_y_def by auto

lemma poly_y_pCons[simp]: "poly_y (pCons a p) y = pCons (poly a y) (poly_y p y)"
  unfolding poly_y_def        
  apply (cases "a\<noteq>0 \<or> p \<noteq>0")
  by (auto simp add:map_poly_pCons)

lemma poly_y_add[simp]:"poly_y (p+q) y = poly_y p y + poly_y q y"
  apply (induct p arbitrary:q,simp)
  apply (case_tac q)
  by auto

lemma poly_y_minus [simp]:
  fixes y :: "'a::comm_ring"
  shows "poly_y (- p) y = - poly_y p y"
  by (induct p) simp_all

lemma poly_y_diff[simp]: 
  fixes y :: "'a::comm_ring"
  shows "poly_y (p-q) y = poly_y p y - poly_y q y"
  using poly_y_add[of p "- q" y] by simp
  
lemma poly_y_smult[simp]:
  "poly_y (smult a p) y = smult (poly a y) (poly_y p y)"
  apply (induct p, simp)
  by (simp add:algebra_simps)
  
lemma poly_y_mult[simp]:
  "poly_y (p * q) y = (poly_y p y) * (poly_y q y)"
apply (induct p)
by (auto simp add: poly_y_add poly_y_smult)

lemma poly_y_degree:
  "degree (poly_y p y) \<le> degree p"
  apply (induct p)
  by auto
    
lemma poly_y_monom:
  "poly_y (monom p n) y = monom (poly p y) n"
by (simp add: map_poly_monom poly_y_def) 

lemma poly_x_0[simp]: "poly_x 0 y = 0" unfolding poly_x_def by auto

lemma poly_x_pCons[simp]: "poly_x (pCons a p) x = a + smult x (poly_x p x)"
  unfolding poly_x_def by simp

lemma poly_y_poly_x:"poly (poly_y p y) x= poly (poly_x p x) y"
  apply (induct p)
  by auto


definition degree_y:: "'a::zero bpoly \<Rightarrow> nat" where
  "degree_y p = Max {degree (coeff p n)| n. n\<le>degree p }"

  
lemma degree_y_0[simp]:"degree_y 0=0" unfolding degree_y_def by auto

lemma degree_y_pCons_0:"degree_y [:a:] = degree a" unfolding degree_y_def by auto

lemma bpoly_0[simp]: "bpoly 0 x y = 0" unfolding bpoly_def by auto

lemma bpoly_1[simp]: "bpoly 1 x y = 1" unfolding bpoly_def poly_y_def  by simp

lemma bpoly_pCons[simp]: "bpoly (pCons a p) x y = poly a y + x * bpoly p x y"
  unfolding bpoly_def by auto  

lemma bpoly_add[simp]: "bpoly (p+q) x y = bpoly p x y + bpoly q x y"
  unfolding bpoly_def by auto

lemma bpoly_mult[simp]: "bpoly (p*q) x y = bpoly p x y * bpoly q x y" 
  unfolding bpoly_def by simp

lemma bpoly_power[simp]: 
  fixes p :: "'a::{comm_semiring_1} bpoly"
  shows "bpoly (p^n) x y = (bpoly p x y) ^ n"
  apply (induct n)
by auto

definition swap_xy::"'a::{comm_semiring_0,one} bpoly \<Rightarrow> 'a bpoly" where
  "swap_xy p= poly (map_poly lift_x p) [:[:0,1:]:]" 

lemma lift_x_0[simp]: "lift_x 0 = 0"
  unfolding lift_x_def by simp

lemma lift_x_pCons[simp]:"lift_x (pCons a x) = pCons [:a:] (lift_x x) "
  unfolding lift_x_def 
  apply (cases "a\<noteq>0 \<or> x\<noteq>0")
  by (auto simp add:map_poly_pCons)

lemma lift_x_iff[simp]: "lift_x x = 0 \<longleftrightarrow> x=0"
  apply (induct x) 
  by auto

lemma degree_lift_x[simp]:"degree (lift_x x) = degree x" 
  apply (induct x)
  by (auto)

lemma poly_y_lift_x[simp]:"poly_y (lift_x p) y =  p"
  apply (induct p)
by (auto)

lemma lift_x_add[simp]:"lift_x (p+q) = lift_x p + lift_x q" 
  apply (induct p arbitrary:q,simp)
  apply (case_tac q)
  by (auto)

lemma lift_x_smult[simp]: "lift_x (smult x p) = smult [:x:] (lift_x p)"
  apply (induct p)
  by (auto simp add:algebra_simps)

lemma lift_x_mult[simp]:"lift_x (p*q) = lift_x p * lift_x q" 
  apply (induct p)
  by auto
    
lemma lead_coeff_lift_x:
  "lead_coeff (lift_x p) = [:lead_coeff p:]" 
apply (induct p,simp)
apply (case_tac "lift_x p=0")  
by auto

lemma poly_x_lift_x:"poly_x (lift_x p) x = [:poly p x:]" 
   apply (induct p)
by (auto simp add: poly_x_def algebra_simps)

lemma coeff_poly_y:"coeff (poly_y p y) n = poly (coeff p n) y"
  apply (induct p arbitrary:n)
  by (auto simp add:Polynomial.coeff_pCons split:Nat.nat.split)

lemma lc_not_vanish_1: 
  assumes  "poly (lead_coeff q) y \<noteq> 0"
  shows "degree (poly_y q y) = degree q" using assms 
  apply (induct q)
  apply (simp_all)
by (metis (mono_tags) coeff_0 coeff_pCons_Suc coeff_poly_y)

lemma lc_not_vanish_2: 
  assumes  "poly (lead_coeff q) y \<noteq> 0"
  shows "poly_y q y \<noteq>0" using assms
by (metis coeff_0 coeff_poly_y) 

lemma lc_not_vanish_lift_x:
  "q\<noteq>0 \<Longrightarrow> poly (lead_coeff (lift_x q)) y \<noteq> 0"
  by (metis coeff_poly_y degree_lift_x leading_coeff_neq_0 poly_y_lift_x)    
    
lemma pseudo_divmod_poly_y:
  fixes f::"'a::idom bpoly"
  assumes "pseudo_divmod f g = (q,r)"
    and not_degen:"poly (lead_coeff f) y0 \<noteq>0" "poly (lead_coeff g) y0 \<noteq>0"
  shows "pseudo_divmod (poly_y f y0) (poly_y g y0) = (poly_y q y0,poly_y r y0)"
proof -
  have "g\<noteq>0" "poly_y g y0\<noteq>0"
    subgoal using not_degen(2) by auto
    subgoal by (auto simp add: lc_not_vanish_2 not_degen)    
    done  
  have [simp]:"degree (poly_y g y0) = degree g"
    by (simp add: lc_not_vanish_1 not_degen(2))
        
  define a where "a=(lead_coeff g) ^ (Suc (degree f) - degree g)"
  define a' where "a'=(lead_coeff (poly_y g y0)) ^ (Suc (degree f) - degree g)"
  obtain q' r' where qr':"pseudo_divmod (poly_y f y0) (poly_y g y0) = (q',r')" 
    by fastforce
  have "smult a f = g * q + r" and deg: "r = 0 \<or> degree r < degree g"
    using pseudo_divmod[OF \<open>g\<noteq>0\<close> assms(1)] unfolding a_def by auto
  have "smult a' (poly_y f y0) = (poly_y g y0) * (poly_y q y0) + (poly_y r y0)"
  proof -
    have "poly_y (smult a f) y0 = poly_y (g * q +r) y0" 
      using \<open>smult a f = g * q + r\<close> by simp
    then have "smult (poly a y0) (poly_y f y0) = poly_y g y0 * poly_y q y0 + poly_y r y0"
      by (simp)
    moreover have "poly a y0 = a'"
      unfolding a_def a'_def 
      by (metis coeff_poly_y lc_not_vanish_1 not_degen(2) poly_power)  
    ultimately show ?thesis by auto
  qed
  moreover have "smult a' (poly_y f y0) = (poly_y g y0) * q' + r'" 
    and deg': "r' = 0 \<or> degree r' < degree g"
    using pseudo_divmod[OF \<open>poly_y g y0\<noteq>0\<close> qr']  
    unfolding a'_def 
    by (auto simp add:lc_not_vanish_1 not_degen)  
  ultimately have "(q'-poly_y q y0) * (poly_y g y0) = (poly_y r y0 - r')"
    by (auto simp add:algebra_simps)
  then have "q'-poly_y q y0 = 0 \<and> poly_y r y0 - r'=0"
    apply (elim degree_less_timesD)
    subgoal using deg' deg poly_y_degree[of r y0] by (auto intro!:degree_diff_less)
    subgoal using \<open>poly_y g y0\<noteq>0\<close> .
    done
  then show ?thesis using qr' by auto
qed  

lemma poly_y_dist_pmod:
  fixes p::"'a::idom bpoly"
  assumes not_degen:"poly (lead_coeff p) y \<noteq>0" "poly (lead_coeff q) y \<noteq>0" 
  shows "poly_y (pseudo_mod p q) y = pseudo_mod (poly_y p y) (poly_y q y)" 
  using pseudo_divmod_poly_y[OF _ assms] unfolding pseudo_mod_def
  by (metis prod.collapse sndI)

section{*of_rat_bpoly*}

definition of_rat_bpoly:: "rat bpoly \<Rightarrow> ('a::field_char_0) bpoly" where
  "of_rat_bpoly = map_poly of_rat_poly"

lemma coeff_of_rat_bpoly:"coeff (of_rat_bpoly p)  = of_rat_poly o (coeff p)"
  unfolding of_rat_bpoly_def comp_def
  using coeff_map_poly of_rat_poly_0 by blast  
    
lemma of_rat_bpoly_0[simp]:"of_rat_bpoly 0 = 0" unfolding of_rat_bpoly_def by simp

lemma of_rat_bpoly_1[simp]:"of_rat_bpoly 1 = 1"  
  unfolding of_rat_bpoly_def by simp
 
lemma of_rat_bpoly_eq_iff[simp]:"of_rat_bpoly p = of_rat_bpoly q \<longleftrightarrow> p = q" 
  unfolding  poly_eq_iff
  by (auto simp add:coeff_of_rat_bpoly coeff_of_rat_poly  poly_eq_iff)

lemma of_rat_bpoly_eq_0_iff [simp]: "(of_rat_bpoly a = 0) = (a = 0)"
  using of_rat_bpoly_eq_iff [of _ 0] by simp

lemma zero_eq_of_rat_bpoly_iff [simp]: "(0 = of_rat_bpoly a) = (0 = a)"
  by simp

lemma of_rat_bpoly_eq_1_iff [simp]: "(of_rat_bpoly a = 1) = (a = 1)"
  using of_rat_bpoly_eq_iff [of _ 1] by simp

lemma one_eq_of_rat_bpoly_iff [simp]: "(1 = of_rat_bpoly a) = (1 = a)"
  by simp

lemma of_rat_bpoly_pCons[simp]:"of_rat_bpoly (pCons a p) = pCons (of_rat_poly a) (of_rat_bpoly p)" 
  unfolding of_rat_bpoly_def
  apply (cases "a\<noteq>0 \<or> p\<noteq>0")
  by (auto simp add:map_poly_pCons)

lemma of_rat_bpoly_plus[simp]: "of_rat_bpoly (p + q) = of_rat_bpoly p +  of_rat_bpoly q" 
  using of_rat_poly_plus
  by (auto simp add: poly_eq_iff coeff_of_rat_bpoly)

lemma of_rat_bpoly_smult[simp]:"of_rat_bpoly (smult s p) = smult (of_rat_poly s) (of_rat_bpoly p)" 
  using of_rat_poly_mult 
  by (auto simp add: poly_eq_iff coeff_of_rat_bpoly)

lemma of_rat_bpoly_times[simp]: "of_rat_bpoly (p * q) = of_rat_bpoly p * of_rat_bpoly q"
  by (induct p,intro poly_eqI,auto)

lemma of_rat_bpoly_power[simp]: "of_rat_bpoly (p ^ n) =  of_rat_bpoly p ^ n"
  apply (induct n)
  by auto

lemma of_rat_bpoly_lift_x[simp]:"of_rat_bpoly (lift_x p) = lift_x (of_rat_poly p)"
  by (induct p,auto)

lemma of_rat_bpoly_degree[simp]:"degree (of_rat_bpoly p) = degree p"
  by (induct p,auto)
  
lemma of_rat_bpoly_monom[simp]:
  "of_rat_bpoly (monom x n) = monom (of_rat_poly x) n"
apply (induct n)
by (auto simp add:monom_0 monom_Suc)

lemma of_rat_poly_lead_coeff[simp]: "of_rat_poly (lead_coeff p) = lead_coeff (of_rat_bpoly p)" 
  by (simp add: coeff_of_rat_bpoly)  
    
lemma of_rat_poly_pseudo_divmod_iff:
  shows "pseudo_divmod f g = (q,r) 
      \<longleftrightarrow> pseudo_divmod (of_rat_poly f) (of_rat_poly g) = (of_rat_poly q,of_rat_poly r)" 
  (is "?L \<longleftrightarrow> ?R")
proof (cases "g=0")
  case True
  then show ?thesis by auto
next
  case False
  define a where "a=(lead_coeff g) ^ (Suc (degree f) - degree g)"
  define a'::'a where "a'=(lead_coeff (of_rat_poly g)) ^ (Suc (degree f) - degree g)"
  have ?R when ?L
  proof -
    obtain q' r' where qr':"pseudo_divmod (of_rat_poly f) (of_rat_poly g) = (q'::'a poly,r')" 
      by fastforce
    have "smult a f = g * q + r" and deg: "r = 0 \<or> degree r < degree g"
      using pseudo_divmod[OF False that] unfolding a_def by auto
    have "smult a' (of_rat_poly f) = (of_rat_poly g) * (of_rat_poly q) 
        + (of_rat_poly r)" 
    proof -
      have "of_rat_poly (smult a f) = of_rat_poly (g * q + r)"
        using \<open>smult a f = g * q + r\<close> by simp
      then show ?thesis unfolding a_def a'_def 
        by (auto simp add: of_rat_power)
    qed
    moreover have "smult a' (of_rat_poly f) = (of_rat_poly g) * q' + r'" 
        and deg': "r' = 0 \<or> degree r' < degree g"
      using pseudo_divmod[OF _ qr'] False unfolding a'_def 
      by auto
    ultimately have "(q'-of_rat_poly q) * (of_rat_poly g) = (of_rat_poly r - r')"
      by (auto simp add:algebra_simps)
    then have "q'-of_rat_poly q = 0 \<and> of_rat_poly r - r' = 0" 
      apply (elim degree_less_timesD) 
      subgoal 
        by (metis deg deg' degree_diff_less diff_self of_rat_poly_0 of_rat_poly_degree)  
      using False by auto
    then show ?thesis using qr' by auto
  qed
  moreover have ?L when ?R
  proof -
    obtain q' r' where qr':"pseudo_divmod f g = (q',r')" 
      by fastforce
    have "of_rat_poly g \<noteq> 0" using False by auto
    from pseudo_divmod[OF this that]
    have "smult a' (of_rat_poly f) = (of_rat_poly g) * (of_rat_poly q) + (of_rat_poly r)" 
        and deg: "r = 0 \<or> degree r < degree g"
      unfolding a'_def by auto
    moreover have "smult a f = g * q' + r'" and deg': "r' = 0 \<or> degree r' < degree g"  
      using pseudo_divmod[OF False qr'] unfolding a_def by auto
    then have "of_rat_poly (smult a f) = of_rat_poly (g * q' + r')"
      by simp
    then have "smult a' (of_rat_poly f) 
        = (of_rat_poly g) * (of_rat_poly q') + (of_rat_poly r')"
      unfolding a_def a'_def by (auto simp add: of_rat_power)
    ultimately have "(of_rat_poly q-of_rat_poly q') * (of_rat_poly g) 
        = ((of_rat_poly r' - of_rat_poly r)::'a poly)"
      by (auto simp add:algebra_simps)
    then have "of_rat_poly q-of_rat_poly q' = (0::'a poly) 
      \<and> of_rat_poly r' - of_rat_poly r = (0::'a poly)" 
      apply (elim degree_less_timesD) 
      subgoal by (metis deg deg' degree_0 degree_diff_less diff_zero not_gr_zero 
            not_less_zero of_rat_poly_0 of_rat_poly_degree)
      using False by auto
    then show ?thesis using qr' by auto
  qed
  ultimately show ?thesis by auto
qed  
  
lemma of_rat_bpoly_degree_y[simp]:"degree_y (of_rat_bpoly p) = degree_y p"
  unfolding degree_y_def by (auto simp add:coeff_of_rat_bpoly)  
  
lemma of_rat_poly_pseudo_mod:
  "of_rat_poly (pseudo_mod p q) = pseudo_mod (of_rat_poly p) (of_rat_poly q)"
  unfolding pseudo_mod_def using of_rat_poly_pseudo_divmod_iff
  by (metis prod.collapse snd_conv)
 
  
lemma of_rat_bpoly_pseudo_divmod_iff:
  shows "pseudo_divmod f g = (q,r) 
      \<longleftrightarrow> pseudo_divmod (of_rat_bpoly f) (of_rat_bpoly g) = (of_rat_bpoly q,of_rat_bpoly r)" 
  (is "?L \<longleftrightarrow> ?R")
proof (cases "g=0")
  case True
  then show ?thesis by auto
next
  case False
  define a where "a=(lead_coeff g) ^ (Suc (degree f) - degree g)"
  define a'::"'a poly" where "a'=(lead_coeff (of_rat_bpoly g)) ^ (Suc (degree f) - degree g)"
  have ?R when ?L
  proof -
    obtain q' r' where qr':"pseudo_divmod (of_rat_bpoly f) (of_rat_bpoly g) = (q'::'a bpoly,r')" 
      by fastforce
    have "smult a f = g * q + r" and deg: "r = 0 \<or> degree r < degree g"
      using pseudo_divmod[OF False that] unfolding a_def by auto
    have "smult a' (of_rat_bpoly f) = (of_rat_bpoly g) * (of_rat_bpoly q) 
        + (of_rat_bpoly r)" 
    proof -
      have "of_rat_bpoly (smult a f) = of_rat_bpoly (g * q + r)"
        using \<open>smult a f = g * q + r\<close> by simp
      then show ?thesis unfolding a_def a'_def 
        by (auto simp add: of_rat_power)
    qed
    moreover have "smult a' (of_rat_bpoly f) = (of_rat_bpoly g) * q' + r'" 
        and deg': "r' = 0 \<or> degree r' < degree g"
      using pseudo_divmod[OF _ qr'] False unfolding a'_def 
      by auto
    ultimately have "(q'-of_rat_bpoly q) * (of_rat_bpoly g) = (of_rat_bpoly r - r')"
      by (auto simp add:algebra_simps)
    then have "q'-of_rat_bpoly q = 0 \<and> of_rat_bpoly r - r' = 0" 
      apply (elim degree_less_timesD) 
      subgoal by (metis (mono_tags, hide_lams) cancel_comm_monoid_add_class.diff_cancel deg deg' 
            degree_diff_less of_rat_bpoly_degree of_rat_bpoly_eq_0_iff)
      using False by auto
    then show ?thesis using qr' by auto
  qed
  moreover have ?L when ?R
  proof -
    obtain q' r' where qr':"pseudo_divmod f g = (q',r')" 
      by fastforce
    have "of_rat_bpoly g \<noteq> 0" using False by auto
    from pseudo_divmod[OF this that]
    have "smult a' (of_rat_bpoly f) = (of_rat_bpoly g) * (of_rat_bpoly q) + (of_rat_bpoly r)" 
        and deg: "r = 0 \<or> degree r < degree g"
      unfolding a'_def by auto
    moreover have "smult a f = g * q' + r'" and deg': "r' = 0 \<or> degree r' < degree g"  
      using pseudo_divmod[OF False qr'] unfolding a_def by auto
    then have "of_rat_bpoly (smult a f) = of_rat_bpoly (g * q' + r')"
      by simp
    then have "smult a' (of_rat_bpoly f) 
        = (of_rat_bpoly g) * (of_rat_bpoly q') + (of_rat_bpoly r')"
      unfolding a_def a'_def by (auto simp add: of_rat_power)
    ultimately have "(of_rat_bpoly q-of_rat_bpoly q') * (of_rat_bpoly g) 
        = ((of_rat_bpoly r' - of_rat_bpoly r)::'a bpoly)"
      by (auto simp add:algebra_simps)
    then have "of_rat_bpoly q-of_rat_bpoly q' = (0::'a bpoly) 
      \<and> of_rat_bpoly r' - of_rat_bpoly r = (0::'a bpoly)" 
      apply (elim degree_less_timesD) 
      subgoal by (metis deg deg' degree_diff_less diff_self of_rat_bpoly_degree)
      using False by auto
    then show ?thesis using qr' by auto
  qed
  ultimately show ?thesis by auto
qed      

lemma of_rat_bpoly_pseudo_mod:
  "of_rat_bpoly (pseudo_mod p q) = pseudo_mod (of_rat_bpoly p) (of_rat_bpoly q)"
  unfolding pseudo_mod_def using of_rat_bpoly_pseudo_divmod_iff
  by (metis prod.collapse snd_conv)  

section \<open>Mapping bivariate polynomials\<close>

definition map_bpoly :: "('a :: zero \<Rightarrow> 'b :: zero) \<Rightarrow> 'a bpoly \<Rightarrow> 'b bpoly" where
  "map_bpoly f pp= map_poly (\<lambda>p. map_poly f p) pp"

value [code] "map_bpoly (\<lambda>x::int. x+ 1) [:[:1,2:],[:3:]:] "

section \<open> @{typ "rat bpoly"} to @{typ "int bpoly"} by clearing the denominators\<close>

term "coeffs (p::rat bpoly)"

term "(Lcm o set o (map (\<lambda>x. snd (quotient_of x))) o concat o (map coeffs) o coeffs) p"

definition de_lcm_bpoly::"rat bpoly \<Rightarrow> int" where
  "de_lcm_bpoly p = (Lcm o set o (map (\<lambda>x. snd (quotient_of x))) o concat o (map coeffs) o coeffs) p"

definition clear_de_bpoly::"rat bpoly \<Rightarrow> int bpoly" where
  "clear_de_bpoly p = (SOME q. (map_bpoly of_int q) = map_bpoly (\<lambda>x. x * of_int (de_lcm_bpoly p)) p)"


value [code] "de_lcm_bpoly [:[:3/4,2/5:]:]"

end
