theory Univ_RCF_Reification imports 
  Complex_Main
  "HOL-Library.Reflection"
  Preprocess_Polys
  (*"../New_Real_Algebraic_Numbers/Real_Alg_Imp"*)
begin

lemma list_Cons_induct[case_names Nil Cons CCons]:
  "\<lbrakk>P [];\<And>x. P [x];\<And>x1 x2 xs. P (x2#xs) \<Longrightarrow> P (x1 #x2 # xs)\<rbrakk> \<Longrightarrow> P xs"
apply (induct xs,simp)
by (case_tac xs,auto)


section \<open>strict_sorted\<close>

fun strict_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "strict_sorted [] = True" |
  "strict_sorted [x] = True" |
  "strict_sorted (x1#x2#xs) = (x1<x2 \<and> strict_sorted (x2#xs))"

lemma strict_sorted_sorted:"strict_sorted xs \<Longrightarrow> sorted xs"
  by (induct rule:strict_sorted.induct,auto) 

lemma strict_sorted_bot:"strict_sorted (x#xs) \<Longrightarrow> \<forall>y\<in>set xs. x<y"
  by (induct xs rule:strict_sorted.induct,auto)

lemma strict_sorted_imp_distinct:"strict_sorted xs \<Longrightarrow> distinct xs"
  apply (induct xs rule:strict_sorted.induct)
  apply auto
by (metis not_less_iff_gr_or_eq strict_sorted_bot)

lemma strict_sorted_Cons: "strict_sorted (x#xs) = (strict_sorted xs \<and> (\<forall> y\<in>set xs. x < y))"
  using strict_sorted_bot
  by (cases xs,auto,fastforce)
  
lemma strict_sorted_append:"strict_sorted (xs@ys) \<Longrightarrow> strict_sorted xs \<and> strict_sorted ys 
    \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. x < y)"
apply (induct xs rule:strict_sorted.induct,auto)
apply (cases ys)
by (auto simp add:strict_sorted_bot)

lemma strict_sorted_append':"strict_sorted (xs@ys@zs) \<Longrightarrow> strict_sorted (xs@zs)"
  apply (induct xs)
  by (auto simp add:strict_sorted_Cons dest:strict_sorted_append)

section \<open>Parse formulas (stratification)\<close>

datatype num = C real | Add num num | Minus num | Mul num num | Var nat | Power num nat

datatype form = Lt num num  | Eq num num | Ge num num | NEq num num | 
    Conj form form | Disj form form | Neg form | T | F  | ExQ form | AllQ form 

primrec num_interp:: "num \<Rightarrow> real list \<Rightarrow> real"
where
  num_interp_C  : "num_interp (C i) vs = i"
| num_interp_Var: "num_interp (Var v) vs = vs!v"
| num_interp_Add: "num_interp (Add num1 num2) vs = num_interp num1 vs + num_interp num2 vs "
| num_interp_Minus: "num_interp (Minus num) vs = - num_interp num vs "
| num_interp_Mul: "num_interp (Mul num1 num2) vs = num_interp num1 vs * num_interp num2 vs "
| num_interp_Power: "num_interp (Power num n) vs = (num_interp num vs)^n"

lemma num_interp_diff:"num_interp (Add num1 (Minus num2)) vs 
    = (num_interp num1 vs) - (num_interp num2 vs)"
  unfolding num_interp.simps by simp

lemma num_interp_number: "num_interp (C (numeral t)) vs = numeral t" by simp
lemma num_interp_rat: 
  "num_interp (C (numeral t1/numeral t2)) vs = numeral t1 / numeral t2" 
  "num_interp (Mul num (C (1/numeral c))) vs = num_interp num vs / numeral c"
  by simp_all 
lemma num_interp_01: "num_interp (C 0) vs = 0" "num_interp (C 1) vs = 1" 
    "num_interp (C 0) vs = 0/n" "num_interp (C 0) vs = n/0" 
    "num_interp (C (1/numeral t2)) vs = 1/numeral t2" 
    "num_interp (C (numeral t1)) vs = numeral t1/1"
  by simp_all
lemmas num_interp_eqs =  
  num_interp_Var num_interp_Add num_interp_Mul num_interp_Minus num_interp_number num_interp_01 
  num_interp_rat num_interp_diff num_interp_Power

primrec form_interp :: "form \<Rightarrow> real list \<Rightarrow> bool"
where
 "form_interp T vs = True"
| "form_interp F vs = False"
| "form_interp (Lt a b) vs = (num_interp a vs < num_interp b vs)"
| "form_interp (Eq a b) vs = (num_interp a vs = num_interp b vs)"
| "form_interp (Ge a b) vs = (num_interp a vs \<ge> num_interp b vs)"
| "form_interp (NEq a b) vs = (num_interp a vs \<noteq> num_interp b vs)"
| "form_interp (Neg p) vs = (\<not> (form_interp p vs))"
| "form_interp (Conj p q) vs = (form_interp p vs \<and> form_interp q vs)"
| "form_interp (Disj p q) vs = (form_interp p vs \<or> form_interp q vs)"
| "form_interp (ExQ f) vs \<longleftrightarrow> (\<exists>v. form_interp f (v # vs))"
| "form_interp (AllQ f) vs \<longleftrightarrow> (\<forall>v. form_interp f (v # vs))"

datatype norm_num = Pol "real poly" nat | Const real | Abnorm num

fun cancel_normalize_num:: "norm_num \<Rightarrow> num"  where
 "cancel_normalize_num (Pol p v) = fold_coeffs (\<lambda>a f x. Add (C a) (Mul x (f x))) p (\<lambda>_.C 0) (Var v)"|
 "cancel_normalize_num (Const c) = C c"|
 "cancel_normalize_num (Abnorm num) = num"

fun add_norm_num:: "norm_num \<Rightarrow> norm_num \<Rightarrow> norm_num" where
 "add_norm_num (Const c1) (Const c2) = Const (c1+c2)"|
 "add_norm_num (Pol p v) (Const c) = Pol (p+[:c:]) v"|
 "add_norm_num (Const c) (Pol p v)  = Pol (p+[:c:]) v"|
 "add_norm_num (Pol p1 v1) (Pol p2 v2) = 
    (if v1=v2 then Pol (p1+p2) v1 
    else (Abnorm (Add (cancel_normalize_num (Pol p1 v1)) (cancel_normalize_num (Pol p2 v2)))))" |
 "add_norm_num norm1 norm2 =(Abnorm (Add (cancel_normalize_num norm1) (cancel_normalize_num norm2)))"

fun mult_norm_num:: "norm_num \<Rightarrow> norm_num \<Rightarrow> norm_num" where
 "mult_norm_num (Const c1) (Const c2) = Const (c1*c2)"|
 "mult_norm_num (Pol p v) (Const c) = Pol (smult c p) v"|
 "mult_norm_num (Const c) (Pol p v)  = Pol (smult c p) v"|
 "mult_norm_num (Pol p1 v1) (Pol p2 v2) = 
    (if v1=v2 then Pol (p1*p2) v1 
    else (Abnorm (Mul (cancel_normalize_num (Pol p1 v1)) (cancel_normalize_num (Pol p2 v2)))))" |
 "mult_norm_num norm1 norm2 =(Abnorm (Mul (cancel_normalize_num norm1) (cancel_normalize_num norm2)))"

fun minus_norm_num:: "norm_num  \<Rightarrow> norm_num" where
 "minus_norm_num (Const c)= Const (- c)"|
 "minus_norm_num (Pol p v)  = Pol (- p) v"|
 "minus_norm_num (Abnorm ab) =(Abnorm (Minus ab))"

fun power_norm_num:: "norm_num \<Rightarrow> nat \<Rightarrow> norm_num" where
  "power_norm_num (Const c) n = Const ( c ^ n)"|
  "power_norm_num (Pol p v) n = Pol (p ^ n) v" |
  "power_norm_num (Abnorm ab) n = (Abnorm (Power ab n))"

fun normalize_num:: "num \<Rightarrow> norm_num" where 
  "normalize_num (C c) = Const c"|
  "normalize_num (Var v) = Pol [:0,1:] v"|
  "normalize_num (Minus n1) = minus_norm_num (normalize_num n1)"|
  "normalize_num (Add n1 n2) = add_norm_num (normalize_num n1) (normalize_num n2)"|
  "normalize_num (Mul n1 n2) = mult_norm_num (normalize_num n1) (normalize_num n2)"|
  "normalize_num (Power n1 n) = power_norm_num (normalize_num n1) n"
  
fun norm_num_interp :: "norm_num \<Rightarrow> real list \<Rightarrow> real" where
  "norm_num_interp (Pol p v) vs = poly p (vs!v)"|
  "norm_num_interp (Const c) vs = c"|
  "norm_num_interp (Abnorm num) vs = num_interp num vs"

lemma cancel_norm:"num_interp (cancel_normalize_num norm_num) = norm_num_interp norm_num"
proof (cases norm_num) 
  case (Const c)
  thus ?thesis by auto
next
  case (Abnorm num)
  thus ?thesis by auto
next
  case (Pol p v)
  show ?thesis unfolding Pol
    by (induct_tac p,auto)
qed

lemma norm_add:
  "norm_num_interp (add_norm_num n1 n2) vs = norm_num_interp n1 vs + norm_num_interp n2 vs" 
  apply (induct n1 n2 rule:add_norm_num.induct)
  by (simp_all add:cancel_norm del:cancel_normalize_num.simps ) 

lemma norm_mul:
  "norm_num_interp (mult_norm_num n1 n2) vs = norm_num_interp n1 vs * norm_num_interp n2 vs" 
  apply (induct n1 n2 rule:mult_norm_num.induct)
  by (simp_all add:cancel_norm del:cancel_normalize_num.simps ) 

lemma norm_minus:
  "norm_num_interp (minus_norm_num n1) vs = - norm_num_interp n1 vs" 
  apply (induct n1 rule:minus_norm_num.induct)
  by (simp_all add:cancel_norm del:cancel_normalize_num.simps ) 

lemma norm_power:
  "norm_num_interp (power_norm_num n1 n) vs = (norm_num_interp n1 vs) ^ n" 
  apply (induct n1)
  by (simp_all add:cancel_norm del:cancel_normalize_num.simps ) 


lemma normalize_num_correct:"norm_num_interp (normalize_num num) vs = num_interp num vs" 
  apply (induct num rule:normalize_num.induct)
  by (simp_all add:norm_add norm_mul norm_minus norm_power)
                              
datatype qf_form =  Pos norm_num | Zero norm_num | Neg qf_form 
    | Conj qf_form qf_form | Disj qf_form qf_form | T | F

datatype norm_form = QF qf_form | ExQ norm_form | AllQ norm_form

fun rename_num:: "nat \<Rightarrow> num \<Rightarrow> num" where
  "rename_num n (Var v) = (if v\<ge>n then Var (v+1) else Var v)"|
  "rename_num _ (C c) = (C c)" |
  "rename_num n (Add n1 n2) = Add (rename_num n n1) (rename_num n n2)"|
  "rename_num n (Minus n1) = Minus (rename_num n n1)"|
  "rename_num n (Mul n1 n2) = Mul (rename_num n n1) (rename_num n n2)"|
  "rename_num n (Power n1 n') = Power (rename_num n n1) n'"

fun rename_norm_num:: "nat \<Rightarrow> norm_num \<Rightarrow> norm_num" where 
  "rename_norm_num n (Pol p v) = (if v \<ge> n then Pol p (v+1) else Pol p v)"|
  "rename_norm_num _ (Const c) = Const c" | 
  "rename_norm_num n (Abnorm abn) = Abnorm (rename_num n abn)"

fun rename_qf_form:: "nat \<Rightarrow> qf_form \<Rightarrow> qf_form" where
  "rename_qf_form n (Pos nn) = Pos (rename_norm_num n nn)" | 
  "rename_qf_form n (Zero nn) = Zero (rename_norm_num n nn)"  | 
  "rename_qf_form n (Neg qf) = Neg (rename_qf_form n qf)" | 
  "rename_qf_form n (Conj qf1 qf2) = Conj (rename_qf_form n qf1) (rename_qf_form n qf2)" | 
  "rename_qf_form n (Disj qf1 qf2) = Disj (rename_qf_form n qf1) (rename_qf_form n qf2)" | 
  "rename_qf_form _ T = T" | 
  "rename_qf_form _ F = F"

fun rename::"nat \<Rightarrow> norm_form \<Rightarrow> norm_form" where
  "rename n (AllQ nf) = AllQ (rename (n+1) nf)"|
  "rename n (ExQ nf) = ExQ (rename (n+1) nf)" |
  "rename n (QF qf) = QF (rename_qf_form n qf)"

primrec qf_size :: "qf_form\<Rightarrow> nat"
where
  "qf_size (Pos norm_num) = 1"
| "qf_size (Zero norm_num) = 1 "
| "qf_size (Neg qf) = 1 + qf_size qf"
| "qf_size (Conj p q) = 1 + qf_size p + qf_size q"
| "qf_size (Disj p q) = 1 + qf_size p + qf_size q"
| "qf_size T = 0"
| "qf_size F = 0"

primrec nf_size :: "norm_form \<Rightarrow> nat"
where
  "nf_size (QF qf) = 1"
| "nf_size (ExQ nf) = 1 + nf_size nf"
| "nf_size (AllQ nf) = 1 + nf_size nf"

primrec nf_prod_size:: "norm_form \<times> norm_form \<Rightarrow> nat" where
  "nf_prod_size (p1,p2) = (nf_size (p1)) + (nf_size (p2)) "

lemma [measure_function]: "is_measure nf_prod_size" ..

lemma [simp]: "nf_size (rename n v) = nf_size v"  
  by (induct v arbitrary:n) auto

fun combine_conj::"norm_form \<Rightarrow> norm_form \<Rightarrow> norm_form" where 
  "combine_conj (QF qf1) (QF qf2) = QF (Conj qf1 qf2)"|
  "combine_conj (AllQ nf1) (AllQ nf2) = AllQ (combine_conj nf1 nf2)"|
  "combine_conj (AllQ nf1) nf2 = AllQ (combine_conj nf1 (rename 0 nf2))"|
  "combine_conj nf1 (AllQ nf2) = AllQ (combine_conj (rename 0 nf1) nf2)"|
  "combine_conj (ExQ nf1) nf2 = ExQ (combine_conj nf1 (rename 0 nf2))"|
  "combine_conj nf1 (ExQ nf2) = ExQ (combine_conj (rename 0 nf1) nf2)"

fun combine_disj::"norm_form \<Rightarrow> norm_form \<Rightarrow> norm_form" where 
  "combine_disj (QF qf1) (QF qf2) = QF (Disj qf1 qf2)"|
  "combine_disj (ExQ nf1) (ExQ nf2) = ExQ (combine_disj nf1 nf2)"|
  "combine_disj (AllQ nf1) nf2 = AllQ (combine_disj nf1 (rename 0 nf2))"|
  "combine_disj nf1 (AllQ nf2) = AllQ (combine_disj (rename 0 nf1) nf2)"|
  "combine_disj (ExQ nf1) nf2 = ExQ (combine_disj nf1 (rename 0 nf2))"|
  "combine_disj nf1 (ExQ nf2) = ExQ (combine_disj (rename 0 nf1) nf2)"

fun neg_nf:: "norm_form \<Rightarrow> norm_form " where
  "neg_nf (QF qf) = QF (Neg qf)"|
  "neg_nf (AllQ nf) = ExQ (neg_nf nf)"|
  "neg_nf (ExQ nf) = AllQ (neg_nf nf)"

fun normalize:: "form \<Rightarrow> norm_form" where
  "normalize (Lt num1 num2) 
    =  (QF o Pos) (add_norm_num  (normalize_num num2) (minus_norm_num (normalize_num num1)))"|
  "normalize (Eq num1 num2) 
    =  (QF o Zero) (add_norm_num  (normalize_num num1) (minus_norm_num(normalize_num num2)))"|
  "normalize (Ge num1 num2) 
    = (QF o Neg o Pos) ((add_norm_num  (normalize_num num2) (minus_norm_num (normalize_num num1))))" |
  "normalize (NEq num1 num2) 
    = (QF o Neg o Zero) ((add_norm_num  (normalize_num num1) (minus_norm_num (normalize_num num2))))"|
  "normalize (form.Conj f1 f2) = (combine_conj (normalize f1) (normalize f2))" |
  "normalize (form.Disj f1 f2) = combine_disj (normalize f1) (normalize f2)"|
  "normalize (form.Neg form) = neg_nf (normalize form)"|
  "normalize form.T = QF T"|
  "normalize form.F = QF F"|
  "normalize (form.ExQ form) = ExQ (normalize form)"|
  "normalize (form.AllQ form) = AllQ (normalize form)"

fun qf_form_interp:: "qf_form \<Rightarrow> real list \<Rightarrow> bool" where 
  "qf_form_interp (Pos norm_num) vs = (norm_num_interp norm_num vs > 0)"|
  "qf_form_interp (Zero norm_num) vs = (norm_num_interp norm_num vs = 0)"|
  "qf_form_interp (Neg qf_form) vs = (\<not> qf_form_interp qf_form vs)" |
  "qf_form_interp (Conj qf_form1 norm_form2) vs = (qf_form_interp qf_form1 vs
   \<and> qf_form_interp norm_form2 vs)"|
  "qf_form_interp (Disj qf_form1 qf_form2) vs = (qf_form_interp qf_form1 vs
   \<or> qf_form_interp qf_form2 vs)"|
  "qf_form_interp T vs = True"|
  "qf_form_interp F vs = False"

fun norm_form_interp:: "norm_form \<Rightarrow>real list \<Rightarrow> bool" where
  "norm_form_interp (QF qf) vs = qf_form_interp qf vs"|
  "norm_form_interp (ExQ norm_form) vs = (\<exists>x. norm_form_interp norm_form (x#vs))"|
  "norm_form_interp (AllQ norm_form) vs = (\<forall>x. norm_form_interp norm_form (x#vs))"
  
declare norm_form_interp.simps(1)[code]

(*
lemma qf_form_pos_code[code]:"qf_form_interp (Pos (Pol p v)) vs = (sgn_at p (vs!v) = 1)"
  "qf_form_interp (Pos (Const c)) vs = (c>0)"
  unfolding sgn_at_def  by (auto simp add:sgn_1_pos)

lemma qf_form_zero_code[code]:"qf_form_interp (Zero (Pol p v)) vs = (sgn_at p (vs!v) = 0)"
  "qf_form_interp (Zero (Const c)) vs = (c=0)"
  unfolding sgn_at_def  by (auto simp add:sgn_0_0)

declare qf_form_interp.simps(3-6) [code]
*)

lemma rename_num:
  "length vs'=n \<Longrightarrow> num_interp (rename_num n num) (vs'@v#vs) = num_interp num (vs'@vs)"
by (induct num arbitrary: n vs vs' v ,auto simp add:nth_append)
 
lemma rename_norm_num:
   "length vs'=n \<Longrightarrow> 
   norm_num_interp (rename_norm_num n norm_num) (vs'@ v # vs) = norm_num_interp norm_num (vs'@vs)"
by (induct norm_num arbitrary:n vs vs' v,auto simp add:rename_num nth_append)

lemma rename_qf_form:
  "length vs' = n \<Longrightarrow> qf_form_interp (rename_qf_form n qf) (vs'@v # vs) = qf_form_interp qf (vs'@vs)"
apply (induct qf)
by (auto simp add:rename_norm_num)

lemma rename:
  "length vs'=n \<Longrightarrow> norm_form_interp (rename n nf) (vs'@v # vs) = norm_form_interp nf (vs'@vs)"
apply (induct nf arbitrary:n vs' vs v)
apply (auto simp add:rename_qf_form  )
by (metis append_Cons length_Cons)+

lemma rename_inst:
  " norm_form_interp (rename (Suc 0) nf) (x # v # vs) = norm_form_interp nf (x # vs)"
using rename[of "[x]" 1,simplified] .

lemma combine_conj_correct:
  "norm_form_interp (combine_conj nf1 nf2) vs \<longleftrightarrow> norm_form_interp nf1 vs \<and> norm_form_interp nf2 vs"
apply (induct arbitrary:vs rule:combine_conj.induct )
by (auto simp add:rename_qf_form[of Nil 0,simplified] rename_inst HOL.all_conj_distrib[symmetric])

lemma combine_disj_correct:
  "norm_form_interp (combine_disj nf1 nf2) vs \<longleftrightarrow> norm_form_interp nf1 vs \<or> norm_form_interp nf2 vs"
apply (induct arbitrary:vs rule:combine_disj.induct)
by (auto simp add:rename_inst rename_qf_form[of Nil 0,simplified] rename[of Nil 0,simplified] 
  ex_disj_distrib[symmetric])

lemma neg_nf_correct:
  "norm_form_interp (neg_nf nf) vs \<longleftrightarrow> \<not> norm_form_interp nf vs"
apply (induct arbitrary:vs rule:neg_nf.induct)
by auto

lemma norm_form_correct:" norm_form_interp (normalize form) vs = form_interp form vs" 
apply (induct form arbitrary:vs rule:normalize.induct)
apply (auto simp add:norm_minus norm_add normalize_num_correct combine_conj_correct 
  combine_disj_correct neg_nf_correct)
done

datatype norm_num2 = Pol "int poly" nat | Const real | Abnorm num
datatype qf_form2 =  Pos norm_num2 | Zero norm_num2 | Neg qf_form2 
    | Conj qf_form2 qf_form2 | Disj qf_form2 qf_form2 | T | F
datatype norm_form2 = QF qf_form2 | ExQ norm_form2 | AllQ norm_form2

definition int_poly::"real poly \<Rightarrow> int poly" where
  "int_poly p = undefined"

fun normalize_num2:: "norm_num \<Rightarrow> norm_num2" where 
  "normalize_num2 (norm_num.Pol p v) = 
    (if all_coeffs_rat p then Pol (clear_de_real p) v 
    else Abnorm (cancel_normalize_num(norm_num.Pol p v)))" |
  "normalize_num2 (norm_num.Const c) = Const c" |
  "normalize_num2 (norm_num.Abnorm num) = Abnorm num"

fun normalize_qf_form2:: "qf_form \<Rightarrow> qf_form2" where
  "normalize_qf_form2 (qf_form.Pos norm_num) = Pos (normalize_num2 norm_num)"|
  "normalize_qf_form2 (qf_form.Zero norm_num) = Zero (normalize_num2 norm_num)"|
  "normalize_qf_form2 (qf_form.Neg qf_form) = Neg (normalize_qf_form2 qf_form)"|
  "normalize_qf_form2 (qf_form.Conj qf_form qf_form') 
      = Conj (normalize_qf_form2 qf_form) (normalize_qf_form2 qf_form')"|
  "normalize_qf_form2 (qf_form.Disj qf_form qf_form') 
      = Disj (normalize_qf_form2 qf_form) (normalize_qf_form2 qf_form')"|
  "normalize_qf_form2 qf_form.T = T"|
  "normalize_qf_form2 qf_form.F = F"

fun normalize2 :: "norm_form \<Rightarrow> norm_form2" where
  "normalize2 (norm_form.QF qf_form) = QF (normalize_qf_form2 qf_form)"|
  "normalize2 (norm_form.ExQ norm_form) = ExQ (normalize2 norm_form)"|
  "normalize2 (norm_form.AllQ norm_form) = AllQ (normalize2 norm_form)"
  
fun norm_num2_interp :: "norm_num2 \<Rightarrow> real list \<Rightarrow> real" where
  "norm_num2_interp (Pol p v) vs = poly (of_int_poly p) (vs!v)"|
  "norm_num2_interp (Const c) vs = c"|
  "norm_num2_interp (Abnorm num) vs = num_interp num vs"

fun qf_form2_interp:: "qf_form2 \<Rightarrow> real list \<Rightarrow> bool" where 
  "qf_form2_interp (Pos norm_num) vs = (norm_num2_interp norm_num vs > 0)"|
  "qf_form2_interp (Zero norm_num) vs = (norm_num2_interp norm_num vs = 0)"|
  "qf_form2_interp (Neg qf_form) vs = (\<not> qf_form2_interp qf_form vs)" |
  "qf_form2_interp (Conj qf_form1 norm_form2) vs = (qf_form2_interp qf_form1 vs
   \<and> qf_form2_interp norm_form2 vs)"|
  "qf_form2_interp (Disj qf_form1 qf_form2) vs = (qf_form2_interp qf_form1 vs
   \<or> qf_form2_interp qf_form2 vs)"|
  "qf_form2_interp T vs = True"|
  "qf_form2_interp F vs = False"          

fun norm_form2_interp:: "norm_form2 \<Rightarrow>real list \<Rightarrow> bool" where
  "norm_form2_interp (QF qf) vs = qf_form2_interp qf vs"|
  "norm_form2_interp (ExQ norm_form) vs = (\<exists>x. norm_form2_interp norm_form (x#vs))"|
  "norm_form2_interp (AllQ norm_form) vs = (\<forall>x. norm_form2_interp norm_form (x#vs))"

declare [[code drop:norm_form2_interp]]


(*
lemma int_poly_smult:
  fixes p::"real poly"
  assumes "\<forall>r\<in>set(coeffs p). r\<in>\<rat>"
  shows "of_int_poly (clear_de_real p) = 
    smult (of_int (de_lcm (map_poly rat_of_real p))) p"
proof -
  let ?sc="of_int (de_lcm (map_poly rat_of_real p))"
  have "of_int_poly (clear_de_real p) = smult ?sc (map_poly rat_of_real p)"
    by (simp add:clear_de_real)
  then have "of_int_poly (int_poly p) = of_rat_poly (smult ?sc (map_poly rat_of_real p))"
    using of_rat_poly_of_int_poly_eq by metis
  also have "... = smult ?sc (of_rat_poly (map_poly rat_of_real p))"
    by auto
  also have "... = smult ?sc ((map_poly (of_rat o rat_of_real) p))"
    unfolding of_rat_poly_def by (subst map_poly_map_poly,auto)
  also have "... = smult ?sc p"
    proof -
      have "map_poly (of_rat o rat_of_real) p = p" using assms
        apply (induct p)
        by (auto simp add:map_poly_pCons rat_of_real_inv)
      thus ?thesis by auto
    qed
  finally show ?thesis .
qed 
*)

lemma normalize_qf_form2_correct:
    "qf_form2_interp (normalize_qf_form2 norm_form) vs = qf_form_interp norm_form vs" 
proof -
  have "(0 < norm_num2_interp (normalize_num2 norm_num) vs) = (0 < norm_num_interp norm_num vs)"
      for norm_num 
    apply (induct norm_num rule:normalize_num2.induct)
    apply (auto simp del:cancel_normalize_num.simps simp add:cancel_norm clear_de_real)
    by (meson de_lcm_pos of_int_0_less_iff zero_less_mult_pos)
  moreover have "(0 = norm_num2_interp (normalize_num2 norm_num) vs) = (0 = norm_num_interp norm_num vs)"
      for norm_num 
    apply (induct norm_num rule:normalize_num2.induct)
    apply (auto simp del:cancel_normalize_num.simps simp add:cancel_norm clear_de_real)
    using de_lcm_pos by (metis less_irrefl)
  ultimately show ?thesis  
    apply (induct norm_form rule:normalize_qf_form2.induct)
    by auto
qed

lemma norm_form2_correct:" norm_form2_interp (normalize2 (normalize form)) vs = form_interp form vs" 
proof -
  have "norm_form2_interp (normalize2 norm_form) vs = norm_form_interp norm_form vs"
    for norm_form 
    apply (induct norm_form arbitrary:vs rule:normalize2.induct)
    by (auto simp add:normalize_qf_form2_correct)
  thus ?thesis using norm_form_correct by auto
qed


section \<open>Efficient normalisation\<close>




(*
ML \<open>
val term_of_nat = HOLogic.mk_number \<^typ>\<open>nat\<close> o @{code integer_of_nat};

val term_of_int = HOLogic.mk_number \<^typ>\<open>int\<close> o @{code integer_of_int};

fun term_of_pexpr (@{code PExpr1} x) = \<^term>\<open>PExpr1\<close> $ term_of_pexpr1 x
  | term_of_pexpr (@{code PExpr2} x) = \<^term>\<open>PExpr2\<close> $ term_of_pexpr2 x
and term_of_pexpr1 (@{code PCnst} k) = \<^term>\<open>PCnst\<close> $ term_of_int k
  | term_of_pexpr1 (@{code PVar} n) = \<^term>\<open>PVar\<close> $ term_of_nat n
  | term_of_pexpr1 (@{code PAdd} (x, y)) = \<^term>\<open>PAdd\<close> $ term_of_pexpr x $ term_of_pexpr y
  | term_of_pexpr1 (@{code PSub} (x, y)) = \<^term>\<open>PSub\<close> $ term_of_pexpr x $ term_of_pexpr y
  | term_of_pexpr1 (@{code PNeg} x) = \<^term>\<open>PNeg\<close> $ term_of_pexpr x
and term_of_pexpr2 (@{code PMul} (x, y)) = \<^term>\<open>PMul\<close> $ term_of_pexpr x $ term_of_pexpr y
  | term_of_pexpr2 (@{code PPow} (x, n)) = \<^term>\<open>PPow\<close> $ term_of_pexpr x $ term_of_nat n

fun term_of_result (x, (y, zs)) =
  HOLogic.mk_prod (term_of_pexpr x, HOLogic.mk_prod
    (term_of_pexpr y, HOLogic.mk_list \<^typ>\<open>pexpr\<close> (map term_of_pexpr zs)));

local

fun fnorm (ctxt, ct, t) = Thm.mk_binop \<^cterm>\<open>Pure.eq :: pexpr \<times> pexpr \<times> pexpr list \<Rightarrow> pexpr \<times> pexpr \<times> pexpr list \<Rightarrow> prop\<close>
  ct (Thm.cterm_of ctxt t);

val (_, raw_fnorm_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>fnorm\<close>, fnorm)));

fun fnorm_oracle ctxt ct t = raw_fnorm_oracle (ctxt, ct, t);

in

val cv = @{computation_conv "pexpr \<times> pexpr \<times> pexpr list"
  terms: fnorm nat_of_integer Code_Target_Nat.natural
    "0::nat" "1::nat" "2::nat" "3::nat"
    "0::int" "1::int" "2::int" "3::int" "-1::int"
  datatypes: fexpr int integer num}
  (fn ctxt => fn result => fn ct => fnorm_oracle ctxt ct (term_of_result result))

end
\<close>
val nat_of_integer = @{code nat} o @{code int_of_integer};
*)


(*
ML_val \<open>
fun real_of_Float (@{code Float} (m, e)) =
    real_of_man_exp (@{code integer_of_int} m) (@{code integer_of_int} e)

fun term_of_int i = (HOLogic.mk_number @{typ int} (@{code integer_of_int} i))

fun term_of_Float (@{code Float} (m, e)) = @{term Float} $ term_of_int m $ term_of_int e

\<close>
*)

(*
ML_val \<open>
HOLogic.mk_number
\<close>

ML \<open>
  local

  fun int_of_nat @{code "0 :: nat"} = 0
    | int_of_nat (@{code Suc} n) = int_of_nat n + 1;

  in

  val comp_nat = @{computation nat terms:
    "plus :: nat \<Rightarrow> nat \<Rightarrow> nat" "times :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "sum_list :: nat list \<Rightarrow> nat" "prod_list :: nat list \<Rightarrow> nat"
    datatypes: nat "nat list"}
    (fn post => post o HOLogic.mk_nat o int_of_nat o the);

  end
\<close>

ML_val \<open>
  comp_nat \<^context> \<^term>\<open>prod_list [Suc 0, Suc (Suc 0)] * Suc (Suc 0)\<close>
\<close>

typ integer

term normalize2
thm norm_form2.simps

typ norm_form2 typ qf_form2
thm norm_form2.case

thm qf_form2.case

term norm_form2.QF
*)


(*
datatype num = C real | Add num num | Minus num | Mul num num | Var nat | Power num nat
datatype norm_num = Pol "real poly" nat | Const real | Abnorm num
datatype norm_num2 = Pol "int poly" nat | Const real | Abnorm num
datatype qf_form2 =  Pos norm_num2 | Zero norm_num2 | Neg qf_form2 
    | Conj qf_form2 qf_form2 | Disj qf_form2 qf_form2 | T | F
datatype norm_form2 = QF qf_form2 | ExQ norm_form2 | AllQ norm_form2
*)

(*
typ norm_num2

find_consts norm_num2

ML_val \<open>
@{code Pol}
\<close>

ML \<open>
  local

  fun raw_dvd (b, ct) = Thm.mk_binop \<^cterm>\<open>Pure.eq :: bool \<Rightarrow> bool \<Rightarrow> prop\<close>
    ct (if b then \<^cterm>\<open>True\<close> else \<^cterm>\<open>False\<close>);

  val (_, dvd_oracle) = Context.>>> (Context.map_theory_result
    (Thm.add_oracle (\<^binding>\<open>dvd\<close>, raw_dvd)));

  in

  val conv_dvd = @{computation_conv bool terms:
    "Rings.dvd :: int \<Rightarrow> int \<Rightarrow> bool"
    "plus :: int \<Rightarrow> int \<Rightarrow> int"
    "minus :: int \<Rightarrow> int \<Rightarrow> int"
    "times :: int \<Rightarrow> int \<Rightarrow> int"
    "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
  } (K (curry dvd_oracle))

  end
\<close>
*)

(*
fun pol (ctxt, ct, t) = Thm.mk_binop \<^cterm>\<open>Pure.eq :: pol \<Rightarrow> pol \<Rightarrow> prop\<close>
  ct (Thm.cterm_of ctxt t);

val (_, raw_pol_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>pnsubstl\<close>, pol)));

fun pol_oracle ctxt ct t = raw_pol_oracle (ctxt, ct, t);
*)

ML \<open>

fun raw_normalize2 (ctxt, ct,t) = Thm.mk_binop \<^cterm>\<open>Pure.eq :: norm_form2 \<Rightarrow> norm_form2 \<Rightarrow> prop\<close>
  ct (Thm.cterm_of ctxt t);

val (_, normalize2_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>normalize2\<close>, raw_normalize2)));
\<close>


ML_val \<open>
@{term "[:1::int,2:]"}
\<close>

definition "coeffs_int = (coeffs :: _ \<Rightarrow> int list)"
definition "coeffs_real = (coeffs :: _ \<Rightarrow> real list)" 

ML \<open>
fun mk_rat a b = @{const "Rat.Fract"} $ (HOLogic.mk_number @{typ int} a) 
                  $ (HOLogic.mk_number @{typ int} b);
fun rat_of_rat x = (case @{code quotient_of} x of (x1,x2) 
        => mk_rat (@{code integer_of_int} x1) (@{code integer_of_int} x2)
      );
fun real_of_real (@{code Ratreal} x) = @{const "Ratreal"} $ (rat_of_rat x) 

fun nat_of_nat x = @{code integer_of_nat} x |> HOLogic.mk_nat

(*TODO: more efficient while avoiding 'poly_of_list'?*)
fun poly_of_poly_int x = 
        @{term "poly_of_list :: int list \<Rightarrow> _"} $ (
          (map (fn y => HOLogic.mk_number @{typ int} (@{code integer_of_int} y)) 
             (@{code coeffs_int} x))
        |> HOLogic.mk_list @{typ "int"}
        )

fun poly_of_poly_real x = 
        @{term "poly_of_list :: real list \<Rightarrow> _"} $ (
          (map real_of_real (@{code coeffs_real} x))
        |> HOLogic.mk_list @{typ "real"}
        )

fun num_of_num (@{code C} x) = @{term C} $ real_of_real x
  | num_of_num (@{code Add} (nm1,nm2)) 
      = @{const Add} $ num_of_num nm1 $ num_of_num nm2
  | num_of_num (@{code Minus} nm1) 
      = @{const Minus} $ num_of_num nm1 
  | num_of_num (@{code Mul} (nm1,nm2)) 
      = @{const Mul} $ num_of_num nm1 $ num_of_num nm2
  | num_of_num (@{code Var} n) 
      = @{const Var} $ nat_of_nat n 
  | num_of_num (@{code Power} (nm1,n)) 
      = @{const Power} $ num_of_num nm1 $ nat_of_nat n

fun norm_num_of_norm_num (@{code norm_num.Pol} (p, n)) = 
        @{const norm_num.Pol} $ (poly_of_poly_real p) $ (nat_of_nat n)
  | norm_num_of_norm_num (@{code norm_num.Const} x) = 
        @{const norm_num.Const} $ (real_of_real x)
  | norm_num_of_norm_num (@{code norm_num.Abnorm} x) = 
        @{const norm_num.Abnorm} $ (num_of_num x)

fun norm_num2_of_norm_num2 (@{code norm_num2.Pol} (p, n)) = 
        @{const norm_num2.Pol} $ (poly_of_poly_int p) $ (nat_of_nat n)
  | norm_num2_of_norm_num2 (@{code norm_num2.Const} x) = 
        @{const norm_num2.Const} $ (real_of_real x)
  | norm_num2_of_norm_num2 (@{code norm_num2.Abnorm} x) = 
        @{const norm_num2.Abnorm} $ (num_of_num x)

fun qf_form2_of_qf_form2 (@{code Pos} nm) = 
        @{const Pos} $ (norm_num2_of_norm_num2 nm)
  | qf_form2_of_qf_form2 (@{code Zero} nm) = 
        @{const Zero} $ (norm_num2_of_norm_num2 nm)
  | qf_form2_of_qf_form2 (@{code Neg} qf) = 
        @{const Neg} $ (qf_form2_of_qf_form2 qf)
  | qf_form2_of_qf_form2 (@{code Conj} (qf1,qf2)) =
        @{const Conj} $ (qf_form2_of_qf_form2 qf1) $ (qf_form2_of_qf_form2 qf2)
  | qf_form2_of_qf_form2 (@{code Disj} (qf1,qf2)) =
        @{const Disj} $ (qf_form2_of_qf_form2 qf1) $ (qf_form2_of_qf_form2 qf2)
  | qf_form2_of_qf_form2 (@{code T}) = @{const T}
  | qf_form2_of_qf_form2 (@{code F}) = @{const F}

fun norm_form2_of_norm_form2 (@{code QF} qf) =
        @{const QF} $ (qf_form2_of_qf_form2 qf)
  | norm_form2_of_norm_form2 (@{code ExQ} nf) =
        @{const ExQ} $ (norm_form2_of_norm_form2 nf)
  | norm_form2_of_norm_form2 (@{code AllQ} nf) =
        @{const AllQ} $ (norm_form2_of_norm_form2 nf)
  

val comp_norm_conv = @{computation_conv norm_form2 
    terms:
      normalize_num2
      normalize2
      normalize

  
      Ratreal

      "Rat.Fract :: int \<Rightarrow> int \<Rightarrow> rat"

      (*int*)
      "0::int"
      "1::int"
      rat_of_int

      (*nat*)
      "0::nat"
      "1::nat"
      "Suc"
      nat_of_num

      (*real*)
      "0::real"
      "1::real"
      "(/) :: _ \<Rightarrow> _ \<Rightarrow> real"

      (*poly*)
    "times::int poly \<Rightarrow> _" 
    "pCons :: int \<Rightarrow> _" 
    "pCons :: real \<Rightarrow> _"
    "smult::int \<Rightarrow> _"
    "HOL.equal ::int poly \<Rightarrow> _" 
    "0 :: int poly"
    "0 :: real poly"
    "poly_of_list :: _ \<Rightarrow> int poly"

    datatypes: norm_form2 qf_form2 qf_form form norm_form norm_num norm_num2 
      Univ_RCF_Reification.num nat rat int 
      Num.num "int list"
    } (fn ctxt => fn p => fn ct => normalize2_oracle (ctxt, ct, (norm_form2_of_norm_form2 p)))
\<close>


ML \<open>
fun check_shape ctrm = (case Thm.term_of ctrm of
        \<^term>\<open>HOL.Trueprop\<close> $ 
          (Const (\<^const_name>\<open>norm_form2_interp\<close>, _) $ t $ _)
           => true
        |_ => false)

val efficient_norm_tac' = 
      Subgoal.FOCUS (fn {context = ctxt, concl = goal, ...}
         => let val _ = @{assert} (check_shape goal);
                val trm_to_norm = goal |> Thm.dest_arg |> Thm.dest_arg1;
                val rw_conv = Conv.rewr_conv (comp_norm_conv ctxt trm_to_norm)
            in 
                HEADGOAL (CONVERSION (Conv.arg_conv (Conv.arg1_conv rw_conv)))
                
            end )

fun efficient_norm_tac ctxt = 
        efficient_norm_tac' ctxt
      THEN'
        simp_tac (Raw_Simplifier.clear_simpset ctxt  
          addsimps @{thms poly_of_list_def Poly.simps})

\<close>     

(*
ML_val \<open>
THEN';
simp_tac;
put_simpset;
addsimprocs;
Raw_Simplifier.clear_simpset
\<close>



ML_val \<open>
val conv1 = comp_norm_conv \<^context> @{cterm "normalize2
       (normalize
         (form.AllQ
           (Ge (Add (Add (Mul (Power (Var 0) 2) (C (1 / 2))) (Minus (Var 0)))
                 (Mul (C 1) (C (1 / 2))))
             (C 0))))"}
\<close>




(*
ML_val \<open>
  comp_norm \<^context> \<^term>\<open>Pol [:1::int,2:] (1::nat)\<close> |> Thm.cterm_of @{context} 
\<close>
*)



lemma example_2:
    "\<forall>x::real. x^2/2 - x + 1/2 \<ge>0 "
  apply (tactic \<open>
     (Reflection.default_reflection_tac 
      @{context}   
      @{thms norm_form2_correct} 
      @{thms num_interp_eqs form_interp.simps} 
      NONE) 1
  \<close>)
 apply (tactic \<open>
   efficient_norm_tac @{context} 1
    \<close>)
  apply (simp only:poly_of_list_def Poly.simps)

  find_theorems poly_of_list


  thm poly_of_list_def

*)

end