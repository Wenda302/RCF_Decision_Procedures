(* 
    Author:     Wenda Li, University of Cambridge
*)

theory RCF_Decision_Proc
imports 
   Univ_RCF_Reification
  "../New_Real_Algebraic_Numbers/Univariate_Sign_Determination"
  (*"HOL-Library.Code_Target_Numeral"*)

begin


section \<open>Decision procedure\<close>

(*representation of real algebraic numbers*)
(*
datatype alg_float = Arep "int poly" float float  
                   | Flt float \<comment>\<open>a small optimization when the number is dyadic\<close>
*)

fun extractPols_num:: "norm_num2 \<Rightarrow> (int poly) set option" where
  "extractPols_num (Pol p v) = (if v=0 then Some {of_int_poly p} else None)" |
  "extractPols_num (Const c) =  Some {}" |
  "extractPols_num (Abnorm v) = None"

fun extractPols:: "qf_form2 \<Rightarrow> (int poly) set option" where
  "extractPols (Pos norm_num) = (extractPols_num norm_num )"|
  "extractPols (Zero norm_num) = (extractPols_num norm_num)"|
  "extractPols (Neg norm_form) = (extractPols norm_form)" |
  "extractPols (Conj norm_form1 norm_form2) = (
    case (extractPols norm_form1, extractPols norm_form2) of
      (Some s1,Some s2) \<Rightarrow> Some (s1 \<union> s2) |
      (_ , _) \<Rightarrow> None)"|
  "extractPols (Disj norm_form1 norm_form2) = (
    case (extractPols norm_form1, extractPols norm_form2) of
      (Some s1,Some s2) \<Rightarrow> Some (s1 \<union> s2) |
      (_ , _) \<Rightarrow> None)"|
  "extractPols T  = Some {}"|
  "extractPols F  = Some {}"


definition invar_sgn_on:: "real poly \<Rightarrow> real set \<Rightarrow> bool" where
  "invar_sgn_on p pts = (\<forall>p1\<in>pts.\<forall>p2\<in>pts. sgn (poly p p1) = sgn (poly p p2))"

fun decomp_aux :: "real list \<Rightarrow> real set list" where
  "decomp_aux []          = []"|
  "decomp_aux [x1]        = [{x1}]"|
  "decomp_aux (x1#x2#xs)  = {x1} # {x1<..<x2} # decomp_aux (x2#xs)"

definition decomp :: "real list \<Rightarrow> real set list" where
  "decomp xs = (if xs=[] then [UNIV::real set] else {..<hd xs} # decomp_aux xs @ [{last xs<..}])"

lemma decomp_aux:
  assumes "xs\<noteq>[]" "sorted xs"
  shows "\<Union>(set(decomp_aux xs)) ={hd xs..last xs}" using assms
  apply (induct xs rule:decomp_aux.induct)
  subgoal by blast
  subgoal by auto
  subgoal 
    apply (auto simp add:sorted2_simps less_imp_le)
    using last_in_set by fastforce
  done


lemma union_decomp:"sorted xs \<Longrightarrow> \<Union>(set(decomp xs)) = \<real>" unfolding decomp_def 
  by (auto simp add: decomp_aux Reals_def)

lemma sorted_last:"sorted (x#xs) \<Longrightarrow> x \<le> last (x#xs)"
  apply (induct xs arbitrary:x)
  by auto

lemma union_decomp_tl: "sorted (x#xs) \<Longrightarrow> \<Union>(set(tl(decomp (x#xs)))) = {x..}"
  apply (cases xs)
  apply (auto simp add:decomp_def decomp_aux dest:sorted_last)
  using last_in_set by fastforce


lemma finite_decomp: "finite (set(decomp xs))" unfolding decomp_def
  by (induct xs rule:decomp_aux.induct) auto

lemma decomp_Cons:
  "decomp (x1#x2#xs) = {..<x1}#{x1}#{x1<..<x2}#tl (decomp (x2#xs))"
unfolding decomp_def by auto

lemma least_in_decomp:"strict_sorted (x#xs) \<Longrightarrow> \<forall>y\<in>(\<Union> (set (tl(decomp (x#xs))))). y\<ge>x"
proof (induct xs arbitrary:x)
  case Nil
  show ?case unfolding decomp_def by simp  
next
  case (Cons y xs)
  hence "\<forall>a\<in>\<Union>(set (tl (decomp (y # xs)))). y \<le> a" by auto
  thus ?case unfolding decomp_Cons
    apply auto
    by (metis Cons.prems less_imp_le order.trans strict_sorted.simps(3))
qed

lemma decomp_distinct:
  "strict_sorted xs \<Longrightarrow> distinct (decomp xs)" 
proof (induct xs )
  case Nil
  show ?case unfolding decomp_def by auto
next
  case (Cons x1 xs)
  have "xs=[] \<Longrightarrow> ?case" unfolding decomp_def 
    apply simp 
    by (metis Diff_cancel equals0I finite.emptyI finite_insert greaterThan_iff infinite_Ioi 
      insert_not_empty lessThan_iff not_less_iff_gr_or_eq single_Diff_lessThan)
  moreover have "xs\<noteq>[] \<Longrightarrow> ?case"
  proof -
    assume "xs\<noteq>[]"
    then obtain x2 xs' where xs:"xs=x2#xs'" by (metis hd_Cons_tl)
    define decomps where "decomps=set (tl (decomp (x2 # xs')))"
    have "strict_sorted xs" and "x1<x2" using Cons.prems unfolding xs by auto
    hence union:"\<Union> decomps = {x2..}" 
      unfolding decomps_def xs using union_decomp_tl strict_sorted_sorted 
      by blast
    hence "{..<x1} \<notin> decomps" and "{x1} \<notin> decomps"   using `x1<x2` 
      apply -
      apply (metis UnionI all_not_in_conv atLeast_iff lessThan_iff lessThan_non_empty less_trans not_less)
      by (metis UnionI atLeast_iff insertI1 not_less)
    moreover have "{x1<..<x2} \<notin> decomps" 
    proof (rule ccontr)
      assume asm:"\<not> {x1<..<x2} \<notin> decomps"
      define mid where "mid\<equiv>(x1+x2)/2"
      hence "mid\<in>{x1<..<x2}" using `x1<x2` by auto
      hence "mid\<in>\<Union> decomps" using asm by blast
      hence "mid\<ge>x2" using union by auto
      thus False unfolding mid_def using `x1<x2` by auto
    qed
    moreover have "distinct (tl (decomp (x2 # xs')))" 
      using `strict_sorted xs` unfolding xs by (intro List.distinct_tl Cons.hyps[unfolded xs])
    ultimately show ?case unfolding xs decomp_Cons using `x1<x2`
       apply (simp, fold decomps_def,simp)
       by (metis greaterThanLessThan_iff lessThan_def less_imp_not_less lt_ex mem_Collect_eq singletonI)
  qed
  ultimately show ?case by auto
qed

fun are_samples:: "real list \<Rightarrow> real set list \<Rightarrow> bool" where
  "are_samples [] [] = True" |
  "are_samples [] (y#ys) = False" |
  "are_samples (x#xs) [] = False" |
  "are_samples (x#xs) (y#ys) = ((x\<in>y) \<and> are_samples xs ys) " 
  
lemma samples_imp_bij:
  fixes samples:: "real list" and decomps:: "real set list"
  assumes "are_samples samples decomps" "distinct samples" "distinct decomps" 
  shows "\<exists>f. (\<forall>d\<in>set decomps. f d\<in>d) \<and> bij_betw f (set decomps) (set samples)" using assms
proof (induct rule:are_samples.induct) 
  case 1
  show ?case by (auto, metis bij_betwI' equals0D)
next
  case (2 y ys)
  thus ?case by auto
next
  case (3 x xs)
  thus ?case by auto
next
  case (4 x xs y ys) 
  hence "x\<in>y" by auto
  obtain f where f:"\<forall>d\<in>set ys. f d \<in> d" "bij_betw f (set ys) (set xs)" using 4 by auto
  define g where "g\<equiv>(\<lambda>s. if s=y then x else f s)"
  have "\<forall>d\<in>set (y # ys). g d \<in> d" unfolding g_def using f(1) `x\<in>y` by simp
  moreover have "bij_betw g (set (y # ys)) (set (x # xs))" 
  proof -
    have "bij_betw g (set ys) (set xs)" unfolding g_def using f(2) `distinct (y # ys)` 
      by (subst bij_betw_cong[where g=f],auto)
    hence "bij_betw g (set ys \<union> {y}) (set xs \<union> {g y})" using 4(3,4) 
      apply (elim Fun.notIn_Un_bij_betw[of y "set ys" g "set xs",rotated 2])
      by (auto simp add:g_def)
    thus ?thesis unfolding g_def by auto
  qed
  ultimately show ?case by auto
qed
       
lemma utilize_samples:
  fixes P::"real \<Rightarrow> bool"
  assumes decomp:"(\<Union>decomps = \<real>)"
  assumes decomp_adapt:"\<forall>d\<in>decomps. \<forall>x1\<in>d.\<forall>x2\<in>d. P x1 = P x2"
  assumes samples:"\<forall>d\<in>decomps. f d\<in>d" and bij_f:"bij_betw f decomps samples" 
  shows "(\<forall>x. P x) = (\<forall>pt\<in>samples. P pt)" using assms
proof -
  have "(\<forall>x. P x) = (\<forall>x\<in>\<real>. P x)" unfolding Reals_def by auto
  also have "... = (\<forall>x\<in>\<Union>decomps. P x)" using decomp by auto
  also have "... = (\<forall>d\<in>decomps.\<forall>x\<in>d. P x )" by simp
  also have "... = (\<forall>d\<in>decomps. P (f d))"
    using decomp_adapt samples by metis
  also have "... = (\<forall>pt\<in>samples. P pt)"
    using bij_f  
    by (metis bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw)
  finally show ?thesis .
qed

(*
definition mid::"float \<Rightarrow> float \<Rightarrow> float" where
  "mid a b = (a+b)*Float 1 (- 1)"

lemma mid_ordering_intros:
  "a<b \<Longrightarrow> real_of_float a < real_of_float b"
  "\<lbrakk>a<b;b<c \<or> b=c\<rbrakk>\<Longrightarrow>mid a b < c"
  "\<lbrakk>a<b;c<a \<or> c=a\<rbrakk>\<Longrightarrow>c < mid a b "
  unfolding mid_def using powr_neg_one by auto
*)

fun mk_samples_aux :: "alg_imp list \<Rightarrow> alg_imp list" where
  "mk_samples_aux []  = []"|
  "mk_samples_aux [x] = [x]"|
  "mk_samples_aux (x1#x2#xs) = x1#btw_alg x1 x2# mk_samples_aux (x2#xs)"

definition mk_samples:: "alg_imp list \<Rightarrow> alg_imp list" where
  "mk_samples xs = (if xs=[] then [Floatalg 0] else 
    (lower_alg (hd xs))# mk_samples_aux xs @ [upper_alg (last xs)]) "

(*
definition mk_samples:: "alg_float list \<Rightarrow> alg_float list" where
  "mk_samples xs = (if xs=[] then [Flt 0] else ( let
     fst_s = (case (hd xs) of
       Arep _ lb1 _ \<Rightarrow> Flt (lb1-1)|
       Flt r1 \<Rightarrow> Flt (r1 - 1));
     last_s = (case (last xs) of
       Arep _ _ ub2 \<Rightarrow> Flt (ub2+1) |
       Flt r2 \<Rightarrow> Flt (r2+1))
   in  [fst_s]@mk_samples_aux xs@[last_s]))"
*)

lemma mk_samples_neq_nil:"mk_samples xs\<noteq>[]"
  by (simp add: mk_samples_def)


lemma mk_samples_Cons:
  "mk_samples (x1#x2#xs) = (
      (lower_alg x1)#x1# btw_alg x1 x2 #tl (mk_samples (x2#xs)))"
  unfolding mk_samples_def by simp

(*
lemma mk_samples_Cons:
  "mk_samples (x1#x2#xs) = (
    case (x1,x2) of
      (Arep p1 lb1 ub1,Arep p2 lb2 ub2) 
        \<Rightarrow> Flt (lb1-1)#Arep p1 lb1 ub1# (Flt (mid ub1 lb2))#tl (mk_samples (x2#xs))|
      (Arep p1 lb1 ub1,Flt r2) 
        \<Rightarrow> Flt (lb1-1)#Arep p1 lb1 ub1# (Flt (mid ub1 r2))#tl (mk_samples (x2#xs))|
      (Flt r1,Arep p2 lb2 ub2) \<Rightarrow>  Flt (r1 - 1)#Flt r1#Flt (mid r1 lb2)#tl (mk_samples (x2#xs))|
      (Flt r1,Flt r2) \<Rightarrow> Flt (r1 - 1)#Flt r1#Flt (mid r1 r2)#tl (mk_samples (x2#xs)))"
unfolding mk_samples_def
by (auto simp add:of_rat_add of_rat_divide split:alg_float.split )
*)

fun ordered_reps:: "alg_imp list \<Rightarrow> bool" where
  "ordered_reps [] = True" |
  "ordered_reps [_] = True" |
  "ordered_reps (x1#x2#xs) = (strict_less_alg_imp x1 x2 \<and> ordered_reps (x2#xs))"

(*
fun of_alg_float:: "alg_float \<Rightarrow> real" where
  "of_alg_float (Arep p lb ub) = Alg p lb ub"|
  "of_alg_float (Flt f) = real_of_float f"
*)

definition valid_list::"alg_imp list \<Rightarrow> bool" where
  "valid_list vs = list_all valid_alg_imp vs"

lemma valid_list_mk_samples: "valid_list vs \<Longrightarrow> valid_list (mk_samples vs)"
proof (induct vs rule:list_Cons_induct)
  case Nil
  thus ?case unfolding mk_samples_def valid_list_def by auto
next
  case (Cons x)
  thus ?case unfolding mk_samples_def valid_list_def 
    by (simp add: valid_lower_alg valid_upper_alg)
next
  case (CCons x1 x2 xs)
  hence "valid_list (mk_samples (x2 # xs))" unfolding valid_list_def by auto
  hence "valid_list (tl (mk_samples (x2 # xs)))"
    unfolding mk_samples_def by (simp add: valid_list_def)
  thus ?case using CCons.prems unfolding valid_list_def
    by (simp add: mk_samples_Cons valid_btw_alg valid_lower_alg)
qed

(*
lemma alg_ordering_intros:
  "\<lbrakk>valid_alg p1 lb1 ub1;valid_alg p2 lb2 ub2;ub1<lb2\<rbrakk> \<Longrightarrow> Alg p1 lb1 ub1 < Alg p2 lb2 ub2"
  "\<lbrakk>valid_alg p lb ub;lb'<real_of_float lb \<or> lb' = real_of_float lb\<rbrakk> \<Longrightarrow> lb' < Alg p lb ub "
  "\<lbrakk>valid_alg p lb ub;real_of_float ub < ub' \<or> real_of_float ub = ub'\<rbrakk> \<Longrightarrow> Alg p lb ub<ub'"
subgoal by (meson alg_bound_and_root(1) alg_bound_and_root(2) less_float.rep_eq less_trans)
subgoal using alg_bound_and_root(1) less_trans by blast
subgoal using alg_bound_and_root(2) less_trans by blast
done  
*)

lemma strict_sorted_algs:
  fixes root_reps:: "alg_imp list"
  defines "algs\<equiv>(map real_of_alg_imp root_reps)"
  assumes "ordered_reps root_reps" 
    "valid_list root_reps"
  shows "strict_sorted algs" using assms
proof (induct algs arbitrary:root_reps rule:list_Cons_induct) 
  case Nil
  thus ?case by simp
next
  case (Cons x)
  thus ?case by auto
next
  case (CCons x1 x2 xs) 
  have "strict_sorted (x2 # xs)" using CCons.prems CCons.hyps(2)  
    by (intro CCons.hyps(1)[of "tl root_reps"], auto simp add:valid_list_def)
  moreover have "x1<x2" using CCons(2-)
    by (auto intro!:alg_imp_less simp: valid_list_def)
  ultimately show ?case by simp
qed

lemma strict_sorted_algs_mk_samples:
  fixes root_reps:: "alg_imp list"
  defines "samples\<equiv> (map real_of_alg_imp (mk_samples root_reps))" 
  assumes order:"ordered_reps root_reps" 
    and valid:"valid_list root_reps"
  shows "strict_sorted samples" 
proof -
  have "ordered_reps (mk_samples root_reps)"
  using order valid
  proof (induct root_reps rule:list_Cons_induct) 
    case Nil
    thus ?case unfolding mk_samples_def by auto
  next
    case (Cons x1)
    thus ?case unfolding mk_samples_def 
      by (auto simp add: lower_alg_less_imp upper_alg_less_imp valid_list_def)
  next
    case (CCons x1 x2 xs)
    have "strict_less_alg_imp (lower_alg x1) x1"
      using CCons.prems(2) lower_alg_less_imp valid_list_def by force
    moreover have "strict_less_alg_imp x1 (btw_alg x1 x2)"
      apply (rule btw_alg_imp_between)
      using CCons.prems(1) ordered_reps.simps(3) by blast
    moreover have "ordered_reps (btw_alg x1 x2 # tl (mk_samples (x2 # xs)))"
    proof -
      define ys where "ys = tl (tl (mk_samples (x2 # xs)))"
      have ys_Cons:"mk_samples (x2 # xs) = lower_alg x2 # x2 # ys"
        unfolding mk_samples_def ys_def
        by (cases xs) auto
      then have "ordered_reps (lower_alg x2 # x2 # ys)"
        using CCons unfolding ys_def valid_list_def by auto
      then have " ordered_reps (btw_alg x1 x2 # x2 # ys)" 
        using CCons.prems(1) btw_alg_imp_between(2) by force
      then show ?thesis using ys_Cons by simp
    qed     
    ultimately show ?case by (auto simp add:mk_samples_Cons)
  qed
  moreover have "list_all valid_alg_imp (mk_samples root_reps)" 
    using valid valid_list_def valid_list_mk_samples by auto
  ultimately show ?thesis unfolding samples_def
    by (intro strict_sorted_algs,auto simp add:valid_list_def)
qed

lemma not_eq_sets:
  fixes x y::real
  shows "{..<x} \<noteq> {y}" "{..<x}\<noteq>{y<..}" "{x}\<noteq>{y<..}"
apply (metis lessThan_non_empty lessThan_subset_iff linear lt_ex not_le subset_singletonD)
apply (metis greaterThan_iff gt_ex lessThan_iff less_irrefl less_trans)
by (metis finite.emptyI finite_insert infinite_Ioi)

lemma decomp_neq_Nil: "decomp xs\<noteq>[]" unfolding decomp_def by auto

lemma validate_samples:
  fixes root_reps:: "alg_imp list"
  defines "samples\<equiv>map real_of_alg_imp (mk_samples root_reps)" 
      and "decomps\<equiv>decomp (map real_of_alg_imp root_reps)"
  assumes "ordered_reps root_reps" "valid_list root_reps"
  shows "are_samples samples decomps \<and> distinct decomps" using assms
proof (induct root_reps arbitrary:samples decomps rule:list_Cons_induct)
  case Nil
  show ?case unfolding mk_samples_def decomp_def by simp
next
  case (Cons x)
  thus ?case unfolding mk_samples_def decomp_def valid_list_def
    by (simp add: not_eq_sets alg_imp_less lower_alg_less_imp upper_alg_less_imp 
          valid_lower_alg valid_upper_alg)
next
  case (CCons x1 x2 xs)
  then have "are_samples (map real_of_alg_imp (mk_samples (x2 # xs))) 
                (decomp (map real_of_alg_imp (x2 # xs))) \<and>
      distinct (decomp (map real_of_alg_imp (x2 # xs)))" 
    unfolding valid_list_def by auto
  then have "are_samples (map real_of_alg_imp (tl (mk_samples (x2 # xs))))
     (tl (decomp (map real_of_alg_imp (x2 # xs))))" 
     by (metis are_samples.elims(2) decomp_neq_Nil list.sel(3) map_tl)
  then have "are_samples (map real_of_alg_imp (mk_samples (x1 # x2 # xs)))
     (decomp (map real_of_alg_imp (x1 # x2 # xs)))"
    using mk_samples_Cons decomp_Cons CCons.prems 
    by (auto intro!:btw_alg_between lower_alg_less simp:valid_list_def)
  moreover have "distinct (decomp (map real_of_alg_imp (x1#x2 # xs)))"
    using decomp_distinct  strict_sorted_algs[OF CCons.prems]
    by auto
  ultimately show ?case by auto
qed

lemma qf_form_interp_cong:
  fixes x1 x2::real
  assumes "Some pols = extractPols qf_form"
          "\<forall>p\<in>pols. sgn (poly (of_int_poly p) x1) = sgn (poly (of_int_poly p) x2)"
  shows "qf_form2_interp qf_form (x1#vs) = qf_form2_interp qf_form (x2#vs)"
    using assms
proof (induct  arbitrary: x1 x2 pols vs rule:qf_form2_interp.induct ) 
  case (1 norm_num vs) 
  thus ?case 
    apply (cases norm_num)
    by (auto simp:sgn_if split!:if_splits)
next
  case (2 norm_num vs)
  thus ?case 
    apply (cases norm_num)
    by (auto simp:sgn_if split!:if_splits)
next
  case (3 qf_form vs)
  hence "qf_form2_interp qf_form (x1 # vs) = qf_form2_interp qf_form (x2 # vs)" 
    by auto
  thus ?case by auto
next
  case (4 qf_form1 qf_form2 vs)  
  obtain pols1 pols2 where pols1:"Some pols1 = extractPols qf_form1" 
      and pols2:"Some pols2 = extractPols qf_form2" and "pols=pols1 \<union> pols2"
    using "4.prems" by (simp split:option.splits)
  hence "qf_form2_interp qf_form1 (x1 # vs) = qf_form2_interp qf_form1 (x2 # vs)" 
      and "qf_form2_interp qf_form2 (x1 # vs) = qf_form2_interp qf_form2 (x2 # vs)"
    using 4 by simp+
  thus ?case by simp
next
  case (5 qf_form1 qf_form2 vs)  
  obtain pols1 pols2 where pols1:"Some pols1 = extractPols qf_form1" 
      and pols2:"Some pols2 = extractPols qf_form2" and "pols=pols1 \<union> pols2"
    using "5.prems" by (simp split:option.splits)
  hence "qf_form2_interp qf_form1 (x1 # vs) = qf_form2_interp qf_form1 (x2 # vs)" 
      and "qf_form2_interp qf_form2 (x1 # vs) = qf_form2_interp qf_form2 (x2 # vs)"
    using 5 by simp+
  thus ?case by simp
next
  case 6
  thus ?case by simp
next
  case 7
  thus ?case by simp
qed

lemma no_root_imp_same_sgn:
  fixes S::"real set" and p::"real poly"
  assumes "connected S" and "\<forall>x\<in>S. poly p x\<noteq>0" "x1\<in>S" "x2\<in>S"
  shows "sgn (poly p x1) =sgn (poly p x2)"
proof -
  have "sgn (poly p x1)\<noteq>0" "sgn (poly p x2)\<noteq>0" 
    unfolding  sgn_0_0 using assms  by auto
  moreover have "sgn (poly p x1)=1 \<Longrightarrow> sgn (poly p x2) = -1 \<Longrightarrow> False" 
  unfolding sgn_1_pos sgn_1_neg
  proof -
    assume at_x1:"0 < poly p x1" and at_x2: "poly p x2 < 0"
    show False
    proof (cases rule:linorder_cases[of x1 x2]) print_cases
      case less
      obtain x where "x>x1" "x < x2"  "poly p x = 0" 
        using poly_IVT_neg[OF less at_x1 at_x2] by auto
      hence "x\<in>S" using connectedD_interval[OF `connected S` `x1\<in>S` `x2\<in>S`,of x] by auto
      thus False using assms(2) `poly p x=0` by auto
    next
      case equal
      thus False using at_x1 at_x2 by auto
    next
      case greater
      obtain x where "x>x2" "x < x1" and x_root: "poly p x = 0" 
        using poly_IVT_pos[OF greater at_x2 at_x1] by auto
      hence "x\<in>S" using connectedD_interval[OF `connected S` `x2\<in>S` `x1\<in>S`,of x] by auto
      thus False using assms(2) x_root by auto
    qed
  qed
  moreover have "sgn (poly p x1)=-1 \<Longrightarrow> sgn (poly p x2) = 1 \<Longrightarrow> False" 
  unfolding sgn_1_pos sgn_1_neg
  proof -
    assume at_x1:"poly p x1<0" and at_x2: "poly p x2 > 0"
    show False
    proof (cases rule:linorder_cases[of x1 x2]) print_cases
      case less
      obtain x where "x>x1" "x < x2"  "poly p x = 0" 
        using poly_IVT_pos[OF less at_x1 at_x2] by auto
      hence "x\<in>S" using connectedD_interval[OF `connected S` `x1\<in>S` `x2\<in>S`,of x] by auto
      thus False using assms(2) `poly p x=0` by auto
    next
      case equal
      thus False using at_x1 at_x2 by auto
    next
      case greater
      obtain x where "x>x2" "x < x1" and x_root: "poly p x = 0" 
        using poly_IVT_neg[OF greater at_x2 at_x1] by auto
      hence "x\<in>S" using connectedD_interval[OF `connected S` `x2\<in>S` `x1\<in>S`,of x] by auto
      thus False using assms(2) x_root by auto
    qed
  qed
  ultimately show "sgn (poly p x1) = sgn (poly p x2)" 
    by (metis sgn_if)
qed

lemma decomp_by_roots_base:
  fixes roots:: "real list" and p::"real poly"
  assumes "{r. poly p r=0} \<subseteq> set points" "strict_sorted points" 
  shows  "\<forall>d\<in>set (decomp points). \<forall>y1\<in>d.\<forall>y2\<in>d. sgn (poly p y1) = sgn (poly p y2)" 
    using assms
proof (induct points arbitrary:p)
  case Nil
  thus ?case unfolding decomp_def 
    by (simp add:no_root_imp_same_sgn[of "UNIV::real set",simplified])    
next
  case (Cons x1 xs) thm no_root_imp_same_sgn[of "{..<x1}",simplified]
  have "p=0 \<Longrightarrow> ?case" by simp
  moreover have "p\<noteq>0 \<Longrightarrow> xs=[] \<Longrightarrow> poly p x1=0  \<Longrightarrow> ?case" 
  proof -
    assume "xs=[]" "poly p x1=0"
    hence "{x1} = {r. poly p r = 0}" using Cons.prems by auto
    hence "\<forall>x\<in>{..<x1}. poly p x\<noteq>0" and "\<forall>x\<in>{x1<..}. poly p x\<noteq>0" by auto
    thus ?case 
      apply (auto simp add:`xs=[]` decomp_def)
      by (auto intro: no_root_imp_same_sgn[of "{..<x1}",simplified]
         no_root_imp_same_sgn[of "{x1<..}",simplified])
  qed
  moreover have "p\<noteq>0 \<Longrightarrow> xs=[] \<Longrightarrow> poly p x1\<noteq>0  \<Longrightarrow> ?case" 
  proof -
    assume "xs=[]" "poly p x1\<noteq>0"
    hence "\<forall>x. poly p x\<noteq>0" using Cons.prems by auto
    thus ?case unfolding decomp_def 
      using no_root_imp_same_sgn[of "UNIV::real set" p,simplified] by simp
  qed
  moreover have "xs\<noteq>[] \<Longrightarrow> p\<noteq>0 \<Longrightarrow> ?case"
  proof -
    assume "xs\<noteq>[]" "p\<noteq>0"
    then obtain x2 xs' where xs:"xs=x2#xs'" by (metis hd_Cons_tl)
    hence "x2>x1" using Cons.prems(2) unfolding xs by auto
    have "\<forall>d\<in>set (tl (decomp xs)). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn (poly p y1) = sgn (poly p y2)"
    proof (cases  "poly p x1=0")
      case False
      have "\<forall>d\<in>set (decomp xs). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn (poly p y1) = sgn (poly p y2)"
        using Cons `poly p x1\<noteq>0` strict_sorted_Cons by auto
      thus ?thesis by (meson decomp_neq_Nil list.set_sel(2))
    next
      case True
      define x1_p where "x1_p\<equiv>[:-x1,1:]^(order x1 p)"
      have "order x1 p\<noteq>0" using True order_root `p \<noteq> 0` by auto
      obtain p' where p:"p=p' * x1_p" and not_dvd: "\<not> [:-x1,1:] dvd p'" unfolding x1_p_def 
        by (metis `p\<noteq>0` mult.commute order_decomp)
      have "\<forall>d\<in>set (tl (decomp xs)). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn (poly p' y1) = sgn (poly p' y2)"
      proof -
        have "{x. poly x1_p x=0} = {x1}" 
          unfolding x1_p_def using PolyMisc.poly_power_n_eq `order x1 p\<noteq>0` by auto
        moreover have "poly p' x1\<noteq>0" using not_dvd by (metis poly_eq_0_iff_dvd)
        moreover have "x1\<notin>set xs" using Cons.prems(2) strict_sorted_Cons by auto
        ultimately have  "{r. poly p' r = 0} \<subseteq> set xs "
          using Cons.prems(1) unfolding p by auto
        hence "\<forall>d\<in>set (decomp xs). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn (poly p' y1) = sgn (poly p' y2)" 
          by (elim Cons.hyps,metis Cons.prems(2) strict_sorted_Cons)
        thus ?thesis by (metis decomp_neq_Nil list.set_sel(2))
      qed
      moreover have "\<forall>d\<in>set (tl (decomp xs)). \<forall>y1\<in>d. \<forall>y2\<in>d. 
        sgn (poly x1_p y1 )= sgn (poly x1_p y2)"
      proof (rule+)
        fix d y1 y2 assume d:"d \<in> set (tl(decomp xs))" and y1:  "y1 \<in> d" and y2: "y2 \<in> d"
        have "\<Union>(set (tl (decomp (x2 # xs')))) = {x2..}" 
          using Cons.prems(2) union_decomp_tl strict_sorted_sorted unfolding xs 
          using strict_sorted_Cons by blast
        hence "x2\<le>y1" and "x2\<le>y2" using d y1 y2 unfolding xs by auto
        moreover have "\<forall>x\<in>{x2..}. poly x1_p x \<noteq> 0" unfolding x1_p_def 
          using PolyMisc.poly_power_n_eq[OF `order x1 p\<noteq>0`,of x1] `x2>x1` by auto
        ultimately show "sgn (poly x1_p y1) = sgn (poly x1_p y2)"
          using no_root_imp_same_sgn[of "{x2..}" x1_p y1 y2,simplified] by auto
      qed
      ultimately show ?thesis 
        by (metis p sgn_mult poly_mult)
    qed
    moreover have "\<forall>y1\<in>{..<x1}. \<forall>y2\<in>{..<x1}. sgn (poly p y1) = sgn (poly p y2)"
    proof (rule+)
      fix y1 y2 assume y1:"y1 \<in> {..<x1}" and y2:"y2 \<in> {..<x1}"
      moreover have "\<forall>x\<in>{..<x1}. poly p x \<noteq> 0 "
      proof (rule ccontr)
        assume "\<not> (\<forall>x\<in>{..<x1}. poly p x \<noteq> 0)"
        then obtain x where "x<x1" "poly p x=0" by auto
        hence "x\<in> set xs" using Cons.prems(1) unfolding xs by auto
        moreover have "\<forall>y\<in>set xs. x1 < y" 
          using Cons.prems(2) strict_sorted_Cons by auto
        ultimately show False using `x<x1` by auto
      qed
      ultimately show "sgn (poly p y1) = sgn (poly p y2)"
        using no_root_imp_same_sgn[of "{..<x1}" p y1 y2,simplified] by auto
    qed
    moreover have "\<forall>y1\<in>{x1<..<x2}. \<forall>y2\<in>{x1<..<x2}. sgn (poly p y1) = sgn (poly p y2)"
    proof (rule+)
      fix y1 y2 assume y1:"y1 \<in> {x1<..<x2}" and y2: "y2 \<in> {x1<..<x2}" 
      have "\<forall>x\<in>{x1<..<x2}. poly p x \<noteq> 0"           
      proof (rule ccontr) 
        assume "\<not> (\<forall>x\<in>{x1<..<x2}. poly p x \<noteq> 0)"
        then obtain x where "x1<x" "x<x2" "poly p x=0" by auto
        hence "x\<in> set xs'" using Cons.prems(1) unfolding xs by auto
        moreover have "\<forall>y\<in>set xs'. x2 < y" 
          using Cons.prems(2) strict_sorted_Cons unfolding xs by auto
        ultimately show False using `x<x2` by auto
      qed
      thus "sgn (poly p y1) = sgn (poly p y2)" 
        using y1 y2  no_root_imp_same_sgn[of "{x1<..<x2}" p y1 y2,simplified] by auto
    qed
    ultimately show ?case unfolding xs decomp_Cons by (simp (no_asm))
  qed
  ultimately show ?case by linarith
qed
     
lemma decomp_by_roots:
  fixes roots:: "real list" and pols::"int poly set"
  assumes roots:"{r::real. \<exists>p\<in>pols. p\<noteq>0 \<and> poly (of_int_poly p) r=0} \<subseteq> set roots " and 
          sorted:"strict_sorted roots"
  shows  "\<forall>p\<in>pols. \<forall>d\<in>set (decomp roots). 
          \<forall>x1\<in>d.\<forall>x2\<in>d. sgn (poly (of_int_poly p) x1) = sgn (poly  (of_int_poly p) x2)" 
proof (rule ccontr)
  assume "\<not> (\<forall>p\<in>pols.\<forall>d\<in>set (decomp roots). 
      \<forall>x1\<in>d. \<forall>x2\<in>d. sgn (poly (of_int_poly p) x1) = sgn (poly (of_int_poly p) x2))"
  then obtain d x1 x2 p where "p\<in>pols" and 
    d:"d\<in>set (decomp roots)" and x1:"x1\<in>d" and x2:"x2\<in>d" and 
    sgn_diff:"sgn (poly (of_int_poly p) x1) \<noteq> sgn (poly (of_int_poly p) x2)" 
    by auto
  have "p\<noteq>0" using sgn_diff by auto
  moreover have "{x. p\<noteq>0 \<and> poly (of_int_poly p) x=0} \<subseteq> set roots" 
    using `p\<in>pols` roots by auto
  ultimately have "\<forall>d\<in>set (decomp roots). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn (poly (of_int_poly p) y1) 
      = sgn (poly (of_int_poly p) y2)"
    using decomp_by_roots_base[of "of_int_poly p" roots,OF _ sorted]  by blast
  thus False using d x1 x2 sgn_diff by fast
qed 

(*
definition sgn_at_alg_float_core::"float poly \<Rightarrow> alg_float \<Rightarrow> int" where
  "sgn_at_alg_float_core q x = (
              case x of
                Arep p lb ub \<Rightarrow>sgn_at_core q (of_int_poly p) lb ub|
                Flt f \<Rightarrow> (let r=poly q f in 
                            if r>0 then 1 else if r=0 then 0 else -1))"


definition contain_all_roots:: "alg_float list \<Rightarrow> float poly set \<Rightarrow> bool" where
  "contain_all_roots algs pols\<equiv> (\<forall>pol\<in>pols. pol\<noteq>0 \<longrightarrow> changes_R_spmods pol (pderiv pol) = 
    (sum_list (map (\<lambda>x. if sgn_at_alg_float_core pol x = 0 then 1 else 0) 
      algs)))"
*)

term fi_changes_R_spmods

definition sign_int_coeffs_at_core::"int poly \<Rightarrow> alg_imp \<Rightarrow> int" where
  "sign_int_coeffs_at_core q x = (
              case x of
                Ratalg x lb ub \<Rightarrow> sign (eval_poly rat_of_int q x) |
                Polyalg p lb ub \<Rightarrow> fi_changes_itv_spmods lb ub p (pderiv p * q) |
                Floatalg f \<Rightarrow> sign (eval_poly float_of_int q f))"

lemma sign_int_coeffs_at_core:
  assumes "valid_alg_imp x"
  shows "sign_int_coeffs_at_core q x = sign (poly (of_int_poly q) (real_of_alg_imp x))"
    (is "?L=?R")
proof -
  have "?R = sign (eval_poly real_of_int q (real_of_alg_imp x))"
    unfolding eval_poly_def by simp
  also have "... = sign_int_coeffs_at q x" 
    unfolding sign_int_coeffs_at_def by simp
  also have "... = ?L"
  proof (cases x)
    case (Floatalg f)
    then show ?thesis 
      unfolding sign_int_coeffs_at_core_def using sign_int_coeffs_at_Floatalg
      by auto
  next
    case (Ratalg r1 lb1 ub1)
    then show ?thesis 
      unfolding sign_int_coeffs_at_core_def using sign_int_coeffs_at_Ratalg
      by auto
  next
    case (Polyalg p1 lb1 ub1)
    then show ?thesis 
      unfolding sign_int_coeffs_at_core_def 
      using sign_int_coeffs_at_Polyalg assms
      by (metis (no_types, lifting) alg_imp.simps(12) valid_alg_imp.simps(3))
  qed
  finally show ?thesis by simp
qed

definition contain_all_roots:: "alg_imp list \<Rightarrow> int poly set \<Rightarrow> bool" where
  "contain_all_roots algs pols\<equiv> 
    (\<forall>pol\<in>pols. pol\<noteq>0 \<longrightarrow> fi_changes_R_spmods pol (pderiv pol) = 
    (sum_list (map (\<lambda>x. if sign_int_coeffs_at_core pol x = 0 then 1 else 0) 
      algs)))"

lemma sum_list_map_cong:
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> f x=g x"
  shows "sum_list (map f xs) = sum_list (map g xs)"
  using assms
  by (metis map_eq_conv)

lemma sign_0_iff: "sign x = 0 \<longleftrightarrow> x =0"
  by (simp add: sign_def)

lemma contain_all_roots:
  fixes algrats::"alg_imp list" and pols::"int poly set"
  defines "points\<equiv>map real_of_alg_imp algrats"
  assumes valid: "valid_list algrats" and
        all_roots:"contain_all_roots algrats pols" and
        ordered:"ordered_reps algrats"
  shows "{r. \<exists>p\<in>pols. p\<noteq>0\<and>poly (of_int_poly p) r=0} \<subseteq> set points" 
proof 
  fix x assume "x \<in> {r::real. \<exists>p\<in>pols. p \<noteq> 0 \<and> poly (of_int_poly p) r = 0}"
  then obtain pol where "pol\<in>pols" "pol\<noteq>0" and "poly (of_int_poly pol) x=0" by auto
  define pol'::"real poly" where "pol'\<equiv> of_int_poly pol"
  have "pol'\<noteq>0" "poly pol' x=0" 
    using \<open>pol\<noteq>0\<close> \<open>poly (of_int_poly pol) x=0\<close> unfolding pol'_def by auto
  have card_eq:"card {r\<in>set points. poly pol' r =0} = card {x. poly pol' x=0} " 
  proof -
    have "distinct points"  
    proof -
      note valid
      hence "strict_sorted points" 
        using strict_sorted_algs[OF ordered]
        unfolding points_def valid_list_def by auto
      thus ?thesis using strict_sorted_imp_distinct by auto
    qed
    have "of_nat (card {x. poly pol' x=0}) = changes_R_smods pol' (pderiv pol')"
      using sturm_R by auto
    also have "... =  changes_R_smods (of_int_poly pol) (of_int_poly (pderiv pol))"
      unfolding pol'_def by (simp add: of_int_hom.map_poly_pderiv)
    also have "... =  fi_changes_R_spmods pol (pderiv pol)"
      using float_int.changes_spmods_smods(2) by simp
    also have "... = (\<Sum>x\<leftarrow>algrats. if sign_int_coeffs_at_core pol x = 0 then 1 else 0)"
      using all_roots[unfolded contain_all_roots_def,rule_format
        ,OF `pol\<in>pols` `pol\<noteq>0`] by simp
    also have "... = (\<Sum>x\<leftarrow>algrats. if sign (poly pol' (real_of_alg_imp x)) = (0::int) 
                          then 1 else 0)"
      unfolding pol'_def 
      apply (rule sum_list_map_cong)
      apply (subst sign_int_coeffs_at_core)
      apply (metis Ball_set valid valid_list_def)
      by simp
    also have "... = sum_list (map (\<lambda>r. if sign (poly pol' r) = (0::int) 
        then 1 else 0) points)"
      unfolding points_def by (induct algrats,auto)
    also have "... = of_nat (card {r\<in>set points. sign (poly pol' r) =(0::int)})"
      apply (subst sum_list_distinct_conv_sum_set[OF \<open>distinct points\<close>])
      apply (subst sum.mono_neutral_right[OF finite_set,
                of "{r \<in> set points. sign (poly pol' r) = (0::int)}" points])
      by auto
    also have "... = of_nat (card {r\<in>set points. poly pol' r =0})"
      by (simp add: sign_0_iff)
    finally have "int (card {x. poly pol' x = 0}) = 
      int (card {r \<in> set points. poly pol' r = 0})" .
    then show ?thesis using int_int_eq by simp
  qed
  moreover have "finite {x. poly pol' x=0}" 
    using `pol'\<noteq>0` by (metis poly_roots_finite)
  ultimately have " {r\<in>set points. poly pol' r =0} =  {x. poly pol' x=0}"
    by (elim Finite_Set.card_subset_eq[rotated 2]) auto
  thus "x \<in> set points" using \<open>poly pol' x=0\<close> by auto 
qed

lemma allQ_subst:
  fixes root_reps:: "alg_imp list"
  defines "samples\<equiv>map real_of_alg_imp (mk_samples root_reps)"
  assumes pols:"Some pols = extractPols qf_form" and  
          ordered:"ordered_reps root_reps" and 
          all_roots:"contain_all_roots root_reps pols" and
          valid: "valid_list root_reps"
  shows "norm_form2_interp (AllQ (QF qf_form)) vs 
    = (\<forall>x \<in> (set samples). norm_form2_interp (QF qf_form) (x#vs)) " (is "?L= ?R")
proof -
  define decomps where "decomps\<equiv>decomp (map real_of_alg_imp root_reps)" 
  define P where "P\<equiv>\<lambda>x. norm_form2_interp (QF qf_form) (x # vs)"
  have "finite (set decomps)" using finite_decomp unfolding decomps_def .
  have "are_samples samples decomps" and "strict_sorted (map real_of_alg_imp root_reps)" 
      and  "distinct decomps" and "strict_sorted samples" 
    using validate_samples[OF ordered]
      strict_sorted_algs[OF ordered]
      strict_sorted_algs_mk_samples[OF ordered]
      valid
    unfolding decomps_def samples_def valid_list_def by auto
  then obtain f where "\<forall>d\<in>set decomps. f d \<in> d" "bij_betw f (set decomps) (set samples)" 
    using strict_sorted_imp_distinct samples_imp_bij[of samples decomps]
    by auto
  moreover have "\<forall>d\<in>set decomps. \<forall>x1\<in>d.\<forall>x2\<in>d. P x1 = P x2"  
    using \<open>strict_sorted (map real_of_alg_imp root_reps)\<close> 
      contain_all_roots[THEN decomp_by_roots,
      OF valid all_roots ordered ,folded  samples_def decomps_def] 
      qf_form_interp_cong[OF pols,of _ _ vs]
    unfolding P_def 
    by (metis norm_form2_interp.simps(1))
  moreover have "(\<Union>(set decomps) = \<real>)" 
    using union_decomp \<open>strict_sorted (map real_of_alg_imp root_reps)\<close> 
    by (metis decomps_def strict_sorted_sorted)
  ultimately have "(\<forall>x. P x) = (\<forall>pt\<in>set samples. P pt)"   
    by (intro utilize_samples[of "set decomps" P f "set samples"]) fastforce+
  thus ?thesis by (simp add: P_def)
qed    

fun pol_var_bound::"norm_num2 \<Rightarrow> nat \<Rightarrow> bool" where
  "pol_var_bound (Pol _ n) ub = (n<ub)"|
  "pol_var_bound (Const _) _ = True"|
  "pol_var_bound _ _ = False"

fun var_bound::"qf_form2 \<Rightarrow> nat \<Rightarrow> bool" where
  "var_bound (Pos num) ub = pol_var_bound num ub" |
  "var_bound (Zero num) ub = pol_var_bound num ub" |
  "var_bound (Neg form) ub = var_bound form ub" |
  "var_bound (Conj form1 form2) ub = (var_bound form1 ub \<and> var_bound form2 ub)"|
  "var_bound (Disj form1 form2) ub = (var_bound form1 ub \<and> var_bound form2 ub)" |
  "var_bound T _ = True"|
  "var_bound F _ = True"
  
(*for efficient code generation*)

fun qf_form2_interp_core:: "qf_form2 \<Rightarrow> alg_imp list \<Rightarrow> bool" where 
  "qf_form2_interp_core (Pos (Pol p v)) vs = (sign_int_coeffs_at_core p (vs!v) = 1)"|
  "qf_form2_interp_core (Zero (Pol p v)) vs = (sign_int_coeffs_at_core p (vs!v) = 0)"|
  "qf_form2_interp_core (Neg qf_form) vs= (\<not> qf_form2_interp_core qf_form vs)"|
  "qf_form2_interp_core (Disj qf_form1 qf_form2) vs
      = (qf_form2_interp_core qf_form1 vs \<or> qf_form2_interp_core qf_form2 vs)"|
  "qf_form2_interp_core (Conj qf_form1 qf_form2) vs
      = (qf_form2_interp_core qf_form1 vs \<and> qf_form2_interp_core qf_form2 vs)"|
  "qf_form2_interp_core form vs= qf_form2_interp form (map real_of_alg_imp vs)"

lemma qf_form2_interp_core:
  assumes "valid_list vs" "var_bound form (length vs)" 
  shows "qf_form2_interp form (map real_of_alg_imp vs) = qf_form2_interp_core form vs" 
  using assms 
apply (induct form arbitrary:vs )
subgoal for num vs unfolding valid_list_def
  apply (cases num)
  by (auto simp add: list_all_length sign_int_coeffs_at_core sign_def)
subgoal for num vs unfolding valid_list_def
  apply (cases num)
  by (auto simp add: list_all_length sign_int_coeffs_at_core sign_def)
by auto

lemma allQ_intro:
  fixes root_reps:: "alg_imp list"
  assumes "Some pols = extractPols qf_form" and  
          "ordered_reps root_reps" and 
          "contain_all_roots root_reps pols" and
          valid:"valid_list root_reps" and
          "var_bound qf_form (Suc 0)" and
          interp_core: "(\<forall>x \<in> (set (mk_samples root_reps)). qf_form2_interp_core qf_form [x])"
  shows "norm_form2_interp (AllQ (QF qf_form)) []" 
apply (subst allQ_subst[OF assms(1-4)])
apply (auto intro!:qf_form2_interp_core)
proof -
  fix x assume "x \<in> set (mk_samples root_reps)"
  hence "valid_list [x]" 
    using valid_list_mk_samples[OF valid] 
    unfolding valid_list_def
    by (simp add: list.pred_set)
  moreover have "qf_form2_interp_core qf_form [x]" 
    using interp_core \<open>x \<in> set (mk_samples root_reps)\<close>
    by auto
  ultimately show "qf_form2_interp qf_form [real_of_alg_imp x]"
    apply (subst qf_form2_interp_core[of "[x]",simplified,OF _ assms(5)])
    by auto
qed

definition check_qf_form_samples::"alg_imp list \<Rightarrow> qf_form2 \<Rightarrow> bool" where
  "check_qf_form_samples ss fm = (\<forall>x \<in> (set ss). qf_form2_interp_core fm [x])"

lemma allQ_intro_code[unfolded Let_def]:
  fixes root_reps:: "alg_imp list"
  assumes "Some pols = extractPols qf_form" and  
          "let rs=root_reps;
               fm=qf_form
           in
              ordered_reps rs \<and>
              contain_all_roots rs pols \<and>
              valid_list rs \<and>
              var_bound fm (Suc 0) \<and>
              (check_qf_form_samples (mk_samples rs) fm)"
  shows "norm_form2_interp (AllQ (QF qf_form)) []" 
using assms by (intro allQ_intro,auto simp:check_qf_form_samples_def) 

lemma ExQ_intro:
  fixes x::"alg_imp"
  assumes "valid_list [x]" "var_bound form (Suc 0)" "qf_form2_interp_core form ([x])"
  shows "norm_form2_interp (ExQ (QF form)) []" 
apply simp
apply (intro exI[where x="real_of_alg_imp x"])
using qf_form2_interp_core[OF assms(1),simplified,OF assms(2)] assms(3)
by auto

lemma ExQ_intro_code[unfolded Let_def]:
  fixes x::"alg_imp"
  assumes "let
              fm = form;
              x = x
           in
            valid_list [x] \<and> var_bound form (Suc 0) \<and> qf_form2_interp_core form ([x])"
  shows "norm_form2_interp (ExQ (QF form)) []" 
  using assms
  by (intro ExQ_intro,auto)


datatype alg_rat_aux = ALG "int poly" rat rat 
                      | RAT rat

definition float_of_rat::"rat \<Rightarrow> float" where
  "float_of_rat r = (let (n,d) = quotient_of r in Float n (- bitlen d + 1))"


definition float_of_rat_l::"rat \<Rightarrow> float" where
  "float_of_rat_l r = (let (n,d) = quotient_of r in lapprox_rat 10 n d)"

definition float_of_rat_r::"rat \<Rightarrow> float" where
  "float_of_rat_r r = (let (n,d) = quotient_of r in rapprox_rat 10 n d)"

definition rat_to_alg::"rat \<Rightarrow> alg_imp" where
  "rat_to_alg r = (
      if r=0 then 
        Floatalg 0 
      else (
        let
          (r1,r2) = quotient_of r;
          lb = lapprox_rat 5 r1 r2;
          ub =  rapprox_rat 5 r1 r2
        in
          if lb=ub then Floatalg lb else Ratalg r lb ub
      ))"  

definition alg_rat_aux_conv::"alg_rat_aux \<Rightarrow> alg_imp" where
  "alg_rat_aux_conv = (\<lambda>x. case x of 
      ALG p lb ub \<Rightarrow> Polyalg p (float_of_rat_l lb) (float_of_rat_r ub)
     |RAT r \<Rightarrow> rat_to_alg r) "

definition alg_rat_list_conv::"alg_rat_aux list \<Rightarrow> alg_imp list" where
  "alg_rat_list_conv = map alg_rat_aux_conv " 

value "lapprox_rat 5 (-3) 1"

(*
declare [[ML_source_trace]] -- \<open>For debug purposes\<close>
*)

lemma [code_computation_unfold]:
  "numeral x = rat_of_int (Code_Target_Int.positive x)"
  "numeral x = real_of_int (Code_Target_Int.positive x)"
  by simp_all


term "(=):: alg_imp \<Rightarrow> _ \<Rightarrow> bool"

ML \<open>
  val rcf_holds = @{computation_check terms:
      Trueprop 

      (*bool*)
      HOL.conj

      (*Let*)
      (*The following is not necessary due to the exception: "Bad term, contains abstraction"*)
      (*
      "Let:: alg_float list \<Rightarrow> (_ \<Rightarrow> _) \<Rightarrow> bool"  
      "Let:: qf_form2 \<Rightarrow> (_ \<Rightarrow> _) \<Rightarrow> bool"
      *)

      (* nat *)
       Suc "0::nat" "1::nat" 
      "(+)::nat \<Rightarrow> nat \<Rightarrow> nat" 
      "(-) ::nat \<Rightarrow> nat \<Rightarrow> nat" 
      "(=)::nat\<Rightarrow>nat\<Rightarrow>bool"
      "(^)::nat\<Rightarrow>nat\<Rightarrow>nat"

      (* int / integer*)
      "(=)::int\<Rightarrow>int\<Rightarrow>bool"
      "(+)::int\<Rightarrow>int\<Rightarrow>int"
      "(-)::int\<Rightarrow>int\<Rightarrow>int"
      "(*)::int\<Rightarrow>int\<Rightarrow>int"
      "(^)::int\<Rightarrow>nat\<Rightarrow>int"
      "uminus::_\<Rightarrow>int"
      "uminus::_\<Rightarrow>integer"
      int_of_integer integer_of_int
      "0::int" "1::int"

      (* rat *)
      Rat.Fract
      "0::rat"
      "1::rat"
      "(+)::rat\<Rightarrow>rat\<Rightarrow>rat"
      "(-)::rat\<Rightarrow>rat\<Rightarrow>rat"
      "(*)::rat\<Rightarrow>rat\<Rightarrow>rat"
      "uminus::rat\<Rightarrow>_"
      "(/)::rat\<Rightarrow>rat\<Rightarrow>rat"
      "(^)::rat\<Rightarrow>nat\<Rightarrow>rat"
      "(>)::rat \<Rightarrow> rat \<Rightarrow> bool"
      "(=)::rat \<Rightarrow> rat \<Rightarrow> bool"
      rat_of_int

      (*float*)
      "(+)::float\<Rightarrow>_"
      "(-)::float\<Rightarrow>_"
      "(*)::float\<Rightarrow>_"
      "uminus::float\<Rightarrow>_"
      "(=)::float \<Rightarrow> float \<Rightarrow> bool"

      (*alg_float*)
       "(=)::alg_imp\<Rightarrow>alg_imp\<Rightarrow>bool"

      (*poly maps*)
      "of_int_poly :: _ \<Rightarrow> float poly"
    
      (*poly*)
      "times::int poly \<Rightarrow> _" 
      "times::float poly \<Rightarrow> _" 
      "pCons :: int \<Rightarrow> _" 
      "pCons :: float \<Rightarrow> _" 
      "pCons :: real \<Rightarrow> _"
      "smult::int \<Rightarrow> _"
      "smult::float \<Rightarrow> _"
      "HOL.equal ::int poly \<Rightarrow> _" 
      "HOL.equal ::float poly \<Rightarrow> _" 
      "0 :: int poly"
      "0 :: float poly"
      "0 :: real poly"
      "poly_of_list :: int list \<Rightarrow> _"

      (*real*)
      "0::real" "1::real"
      "uminus :: real \<Rightarrow> _"
      "(/) :: real \<Rightarrow> _"
      
      (*list*)
      "Cons :: alg_imp \<Rightarrow> _" "Nil :: alg_imp list"
      "list_all (\<lambda>x. qf_form2_interp_core fm [x])"

      (*set*)
      "{}::int poly set"
      "insert :: int poly \<Rightarrow> _"

      (*RealAlg_Imp*)
      int_poly
    
      (*RCF_Decision_Proc*)
      RCF_Decision_Proc.alg_rat_aux_conv
      RCF_Decision_Proc.alg_rat_list_conv
      RCF_Decision_Proc.contain_all_roots
      RCF_Decision_Proc.valid_list
      RCF_Decision_Proc.var_bound
      RCF_Decision_Proc.qf_form2_interp_core
      RCF_Decision_Proc.mk_samples
      Univ_RCF_Reification.qf_form2.Disj
      Univ_RCF_Reification.qf_form2.Conj
      Univ_RCF_Reification.qf_form2.Zero
      Univ_RCF_Reification.qf_form2.Neg
      Univ_RCF_Reification.qf_form2.Pos
      Univ_RCF_Reification.norm_num2.Pol
      RCF_Decision_Proc.ordered_reps
      RCF_Decision_Proc.check_qf_form_samples

      (*misc*)
      Code_Target_Nat.natural
      Code_Target_Int.positive
      Code_Target_Int.negative
      Code_Numeral.positive
      Code_Numeral.negative
  
     datatypes:Num.num bool alg_imp alg_rat_aux float real 
         "alg_rat_aux list" "int list" "int poly list"
  };
\<close>

term poly_of_list

code_thms fi_changes_itv_spmods
term fi_changes_itv_spmods
term Alg

value "fi_changes_itv_spmods 1 3 [:1,2,3:]"

SML_import \<open>val println = Output.writeln\<close>
SML_import \<open>val zz_gcd = Integer.gcd\<close>
SML_import \<open>val zz_lcm = Integer.lcm\<close>

SML_file "rat.sml"
SML_file "Algebra.sig"
SML_file "Algebra.sml"
SML_file "Mathematica.sml"

SML_export \<open>val execute_MathKernel_print = Mathematica.execute_and_print \<close>

SML_export \<open>val root_iso_code = Mathematica.root_iso_code\<close>

ML_val \<open>
writeln root_iso_code
\<close>

ML_file "univ_rcf.ML"


method_setup univ_rcf_cert = \<open>
     Args.term  >>
      (fn cert => fn ctxt => 
        let val _ = @{print} cert in 
        SIMPLE_METHOD' (Univ_RCF.univ_rcf_cert ctxt cert)
        end
      )
\<close>

text \<open>To use univ_rcf, MATH_KERNEL should point to an executable of Mathematica Kernel\<close>
method_setup univ_rcf = \<open>
     Scan.succeed 
      ( fn ctxt => SIMPLE_METHOD' (Univ_RCF.univ_rcf ctxt ))
\<close>

(*
ML \<open>
val root_iso_code =
" isolateRoots[polys_]:=Module[{sortedRoots,sortedRootsEx,minDiff,expr,floatbound}, \n \
\ (*{lb,ub}=floatbound[r,d] s.t. lb and ub are binary rationals, r-d<lb<r, and r<ub<r+d*) \
\ floatbound[r_,d_]:=With[ {n=Power[2,Ceiling[Log[2,1/d]]]}, \
\ {Floor[n*r]/n,Ceiling[n*r]/n}]; \

\ expr=Or@@((#==0)&/@ polys); \
\ sortedRoots = DeleteDuplicates[SortBy[RootReduce /@ (x /. SemialgebraicComponentInstances[expr, x]), N]];\
\ (*sortedRoots=Union[x /. SemialgebraicComponentInstances[expr,x]];*) \
\ (*sortedRootsEx=Sort[Append[sortedRoots,0],Less];*) \

\ (*minDiff calculates a suitable size for isolation interval such that those intervals don't overlap and exclude 0*) \
\ minDiff=Min[(#[[2]]-#[[1]])& /@ Transpose[{Drop[N /@ sortedRoots,-1],Drop[N /@ sortedRoots,1]}]]; \
\ \
\ (If [# \\[Element] Algebraics, \
\ If[# \\[Element]Rationals,{MinimalPolynomial[#],floatbound[#,minDiff/2]},{MinimalPolynomial[#],IsolatingInterval[#,minDiff]}],#])&/@ sortedRoots \
\ ] \n";
\<close>
*)

(*
ML\<open>
val io = TextIO.openOut("/home/wenda/foo.txt");
(*val io = TextIO.stdOut;*)
TextIO.output ( io,root_iso_code);
TextIO.closeOut io;
\<close>
*)

(*for quick debugging*)

ML_val \<open>
Thm.cterm_of;
Syntax.string_of_term;
Thm.prop_of
\<close>

(*
ML \<open>
fun my_print_tac ctxt thm = let
val _ = tracing (Pretty.string_of (pretty_thm_no_vars ctxt thm)) in
Seq.single thm end
\<close>
*)

ML \<open>
fun my_print_tac ctxt thm = let
val _ = tracing (Syntax.string_of_term ctxt (Thm.prop_of thm) ) in
Seq.single thm end;
\<close>

(*)
lemma example_7:"
\<forall>x::real. x < -1 | 0 > x | (41613*x)/2 + 26169*x^2 + (64405*x^3)/4 + 4983*x^4 + 
    (7083*x^5)/10 + (1207*x^6)/35 + x^7/8 > -6435 | 
  11821609800*x + 22461058620*x^2 + 35*x^12 <= 
   4171407240*x^3 + 45938678170*x^4 + 54212099480*x^5 + 31842714428*x^6 + 
    10317027768*x^7 + 1758662439*x^8 + 144537452*x^9 + 5263834*x^10 + 
    46204*x^11 | x <= 0 | 9609600*x + 45805760*x^2 + 92372280*x^3 + 
    102560612*x^4 + 68338600*x^5 + 27930066*x^6 + 6857016*x^7 + 
    938908*x^8 + 58568*x^9 + 753*x^10 <= 0 | 
  788107320*x + 1101329460*x^2 + 10*x^11 <= 
   782617220*x^3 + 2625491260*x^4 + 2362290448*x^5 + 1063536663*x^6 + 
    240283734*x^7 + 24397102*x^8 + 1061504*x^9 + 9179*x^10 | 
  90935460*x + 81290790*x^2 + 5*x^10 <= 125595120*x^3 + 237512625*x^4 + 
    161529144*x^5 + 51834563*x^6 + 6846880*x^7 + 356071*x^8 + 2828*x^9 | 
  640640*x + 2735040*x^2 + 4837448*x^3 + 4581220*x^4 + 2505504*x^5 + 
    794964*x^6 + 138652*x^7 + 11237*x^8 + 207*x^9 <= 0 | 
  5*x^8 <= 73920*x + 238560*x^2 + 303324*x^3 + 192458*x^4 + 63520*x^5 + 
    10261*x^6 + 608*x^7 | 73920*x + 278880*x^2 + 424284*x^3 + 
    332962*x^4 + 142928*x^5 + 32711*x^6 + 3514*x^7 + 98*x^8 <= 0 | x <= -1
"
apply (tactic \<open>
     (Reflection.default_reflection_tac 
      @{context}   
      @{thms norm_form2_correct} 
      @{thms num_interp_eqs form_interp.simps} 
      NONE) 1
  \<close>)
apply (tactic \<open>efficient_norm_tac @{context} 1\<close>)
apply (tactic \<open>
    resolve0_tac [(infer_instantiate' @{context}
        [NONE,NONE,SOME (Thm.cterm_of @{context} (@{term alg_rat_list_conv} 
        $ @{term "

[ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
    198324, 9656, 35:]
                        (- 34937541621241 / 137438953472)
                        (- 279500332969927 / 1099511627776),
ALG [:90935460, 81290790, - 125595120, - 237512625,
  - 161529144, - 51834563, - 6846880, - 356071,
- 2828, 5:]
                        (- 23923468024393 / 274877906944)
                        (- 765550976780575 / 8796093022208),
                       ALG [:788107320, 1101329460, - 782617220,
                             - 2625491260, - 2362290448, - 1063536663,
                             - 240283734, - 24397102, - 1061504, - 9179,
                             10:]
                        (- 348314866751655 / 4398046511104)
                        (- 696629733503309 / 8796093022208),
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (- 649996774163419 / 8796093022208)
                        (- 324998387081709 / 4398046511104),
                       ALG [:9609600, 45805760, 92372280, 102560612,
                             68338600, 27930066, 6857016, 938908, 58568,
                             753:]
                        (- 520047425729199 / 8796093022208)
                        (- 260023712864599 / 4398046511104),
                       ALG [:640640, 2735040, 4837448, 4581220, 2505504,
                             794964, 138652, 11237, 207:]
                        (- 87188559816435 / 2199023255552)
                        (- 43594279908217 / 1099511627776),
                       ALG [:73920, 278880, 424284, 332962, 142928, 32711,
                             3514, 98:]
                        (- 53674445178253 / 2199023255552)
                        (- 13418611294563 / 549755813888),
                       ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
                             198324, 9656, 35:]
                        (- 25415962588497 / 2199023255552)
                        (- 50831925176993 / 4398046511104),
                       ALG [:9609600, 45805760, 92372280, 102560612,
                             68338600, 27930066, 6857016, 938908, 58568,
                             753:]
                        (- 51102732948159 / 8796093022208)
                        (- 25551366474079 / 4398046511104),
                       ALG [:- 73920, - 238560, - 303324, - 192458, - 63520,
                             - 10261, - 608, 5:]
                        (- 97284234774957 / 17592186044416)
                        (- 24321058693739 / 4398046511104),
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (- 9422009463661 / 2199023255552)
                        (- 9422009463659 / 2199023255552),
                       ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
                             198324, 9656, 35:]
                        (- 9051274642631 / 2199023255552)
                        (- 4525637321315 / 1099511627776),
                       ALG [:788107320, 1101329460, - 782617220,
                             - 2625491260, - 2362290448, - 1063536663,
                             - 240283734, - 24397102, - 1061504, - 9179,
                             10:]
                        (- 6463912267981 / 2199023255552)
                        (- 1615978066995 / 549755813888),
                       ALG [:640640, 2735040, 4837448, 4581220, 2505504,
                             794964, 138652, 11237, 207:]
                        (- 1385623990739 / 549755813888)
                        (- 5542495962955 / 2199023255552),
                       ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
                             198324, 9656, 35:]
                        (- 2473395090017 / 1099511627776)
                        (- 4946790180033 / 2199023255552),
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (- 8507541941065 / 4398046511104)
                        (- 1063442742633 / 549755813888),
                       ALG [:90935460, 81290790, - 125595120, - 237512625,
                             - 161529144, - 51834563, - 6846880, - 356071,
                             - 2828, 5:]
                        (- 2092418221909 / 1099511627776)
                        (- 8369672887635 / 4398046511104),
                       ALG [:9609600, 45805760, 92372280, 102560612,
                             68338600, 27930066, 6857016, 938908, 58568,
                             753:]
                        (- 3745351061393 / 2199023255552)
                        (- 7490702122785 / 4398046511104),
                       ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
                             198324, 9656, 35:]
                        (- 6709098186489 / 4398046511104)
                        (- 838637273311 / 549755813888),
                       ALG [:788107320, 1101329460, - 782617220,
                             - 2625491260, - 2362290448, - 1063536663,
                             - 240283734, - 24397102, - 1061504, - 9179,
                             10:]
                        (- 3198968792683 / 2199023255552)
                        (- 1599484396341 / 1099511627776),
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (- 5662162575307 / 4398046511104)
                        (- 2831081287653 / 2199023255552),
                       ALG [:73920, 278880, 424284, 332962, 142928, 32711,
                             3514, 98:]
                        (- 2684462227745 / 2199023255552)
                        (- 83889444617 / 68719476736),
                       ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
                             198324, 9656, 35:]
                        (- 2622039237341 / 2199023255552)
                        (- 5244078474681 / 4398046511104),
                       ALG [:90935460, 81290790, - 125595120, - 237512625,
                             - 161529144, - 51834563, - 6846880, - 356071,
                             - 2828, 5:]
                        (- 4984539914289 / 4398046511104)
                        (- 9969079828577 / 8796093022208),
                       ALG [:640640, 2735040, 4837448, 4581220, 2505504,
                             794964, 138652, 11237, 207:]
                        (- 4874738978211 / 4398046511104)
                        (- 9749477956421 / 8796093022208),
                       ALG [:788107320, 1101329460, - 782617220,
                             - 2625491260, - 2362290448, - 1063536663,
                             - 240283734, - 24397102, - 1061504, - 9179,
                             10:]
                        (- 9537374415943 / 8796093022208)
                        (- 4768687207971 / 4398046511104),
                       ALG [:9609600, 45805760, 92372280, 102560612,
                             68338600, 27930066, 6857016, 938908, 58568,
                             753:]
                        (- 9412687822313 / 8796093022208)
                        (- 9412687822311 / 8796093022208),
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (- 2327300216149 / 2199023255552)
                        (- 9309200864595 / 8796093022208),
                       ALG [:- 73920, - 238560, - 303324, - 192458, - 63520,
                             - 10261, - 608, 5:]
                        (- 9171860959437 / 8796093022208)
                        (- 9171860959435 / 8796093022208),
                       ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
                             198324, 9656, 35:]
                        (- 4575639814519 / 4398046511104)
                        (- 9151279629037 / 8796093022208),
                       RAT (- 1),
                       ALG [:9609600, 45805760, 92372280, 102560612,
                             68338600, 27930066, 6857016, 938908, 58568,
                             753:]
                        (- 68426595789 / 68719476736)
                        (- 4379302130495 / 4398046511104),
                       ALG [:640640, 2735040, 4837448, 4581220, 2505504,
                             794964, 138652, 11237, 207:]
                        (- 1093559932491 / 1099511627776)
                        (- 4374239729963 / 4398046511104),
                       ALG [:73920, 278880, 424284, 332962, 142928, 32711,
                             3514, 98:]
                        (- 8732465080027 / 8796093022208)
                        (- 4366232540013 / 4398046511104),
                       RAT 0,
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (2785263117615 / 4398046511104)
                        (174078944851 / 274877906944),
                       ALG [:788107320, 1101329460, - 782617220,
                             - 2625491260, - 2362290448, - 1063536663,
                             - 240283734, - 24397102, - 1061504, - 9179,
                             10:]
                        (174078944865 / 274877906944)
                        (5570526235681 / 8796093022208),
                       ALG [:90935460, 81290790, - 125595120, - 237512625,
                             - 161529144, - 51834563, - 6846880, - 356071,
                             - 2828, 5:]
                        (2785263133073 / 4398046511104)
                        (5570526266147 / 8796093022208),
                       ALG [:- 73920, - 238560, - 303324, - 192458, - 63520,
                             - 10261, - 608, 5:]
                        (603599397717741 / 4398046511104)
                        (301799698858871 / 2199023255552),
                       ALG [:90935460, 81290790, - 125595120, - 237512625,
                             - 161529144, - 51834563, - 6846880, - 356071,
                             - 2828, 5:]
                        (2965443340708421 / 4398046511104)
                        (5930886681416843 / 8796093022208),
                       ALG [:788107320, 1101329460, - 782617220,
                             - 2625491260, - 2362290448, - 1063536663,
                             - 240283734, - 24397102, - 1061504, - 9179,
                             10:]
                        (9006496618758417 / 8796093022208)
                        (4503248309379209 / 4398046511104),
                       ALG [:11821609800, 22461058620, - 4171407240,
                             - 45938678170, - 54212099480, - 31842714428,
                             - 10317027768, - 1758662439, - 144537452,
                             - 5263834, - 46204, 35:]
                        (3139134067201133 / 2199023255552)
                        (6278268134402267 / 4398046511104)]


"}))] @{thm allQ_intro_code})]
    1\<close>
*)

(*
value "rat_to_alg  (- 34937541621241 / 137438953472)"
value "rat_to_alg (- 279500332969927 / 1099511627776)"

value "real_of_float (Float 4 (-1))"

  ML_val \<open>

@{cterm "

[ALG [:1801800, 5825820, 7327320, 4508350, 1395240,
    198324, 9656, 35:]
                        (- 34937541621241 / 137438953472)
                        (- 279500332969927 / 1099511627776)]


"}

\<close>

lemma example_2:
    "\<forall>x::real. (x^2/2  - 1) \<ge>0 \<or> x + 2 > 0 "
  apply (tactic \<open>
     (Reflection.default_reflection_tac 
      @{context}   
      @{thms norm_form2_correct} 
      @{thms num_interp_eqs form_interp.simps} 
      NONE) 1
  \<close>)
  apply (tactic \<open>efficient_norm_tac @{context} 1\<close>)
  apply (tactic \<open>
    resolve0_tac [(infer_instantiate' @{context}
        [NONE,NONE,SOME (Thm.cterm_of @{context} (@{term alg_rat_list_conv} 
        $ @{term "[RAT (-2),ALG [:-2,0,1:] (-3/2) (-1), ALG [:-2,0,1:] 1 2]"}))] @{thm allQ_intro_code})]
    1\<close>)
   apply simp
   apply (tactic \<open>
    (CONVERSION (rcf_holds @{context}) 1 )
  THEN 
    resolve0_tac [TrueI] 1\<close>)
  done


ML_val \<open>
OS.Process.getEnv "MATH_KERNEL";
OS.Process.getEnv "ISABELLE_HOME";
OS.Process.getEnv "USER_HOME";
OS.Process.getEnv "ML_HOME";
OS.Process.getEnv "USER_HOME";
OS.Process.getEnv "USER_HOME";
\<close>

*)
  
end
