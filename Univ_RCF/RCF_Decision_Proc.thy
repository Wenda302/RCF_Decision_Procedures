(* 
    Author:     Wenda Li, University of Cambridge
*)

theory RCF_Decision_Proc
imports 
  Complex_Main 
  "HOL-Library.Reflection"  
  "../Real_Algebraic_Numbers/RealAlg_Imp"
  "~~/src/HOL/Library/Code_Target_Numeral"
begin

lemma list_Cons_induct[case_names Nil Cons CCons]:
  "\<lbrakk>P [];\<And>x. P [x];\<And>x1 x2 xs. P (x2#xs) \<Longrightarrow> P (x1 #x2 # xs)\<rbrakk> \<Longrightarrow> P xs"
apply (induct xs,simp)
by (case_tac xs,auto)


section{*strict_sorted*}

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

section{*Parse formulas (stratification)*}

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

lemma qf_form_pos_code[code]:"qf_form_interp (Pos (Pol p v)) vs = (sgn_at p (vs!v) = 1)"
  "qf_form_interp (Pos (Const c)) vs = (c>0)"
  unfolding sgn_at_def  by (auto simp add:sgn_1_pos)

lemma qf_form_zero_code[code]:"qf_form_interp (Zero (Pol p v)) vs = (sgn_at p (vs!v) = 0)"
  "qf_form_interp (Zero (Const c)) vs = (c=0)"
  unfolding sgn_at_def  by (auto simp add:sgn_0_0)

declare qf_form_interp.simps(3-6) [code]

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

fun normalize_num2:: "norm_num \<Rightarrow> norm_num2" where 
  "normalize_num2 (norm_num.Pol p v) = (if (\<forall>r\<in>set(coeffs p). r\<in>Rats) then Pol (int_poly p) v 
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

declare norm_form2_interp.simps(1)[code]

lemma int_poly_smult:
  fixes p::"real poly"
  assumes "\<forall>r\<in>set(coeffs p). r\<in>\<rat>"
  shows "of_int_poly (int_poly p) = 
    smult (of_int (de_lcm (map_poly rat_of_real p))) p"
proof -
  let ?sc="of_int (de_lcm (map_poly rat_of_real p))"
  have "of_int_poly (int_poly p) = smult ?sc (map_poly rat_of_real p)"
    unfolding int_poly_def by (simp add:clear_de)
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

lemma normalize_qf_form2_correct:
    "qf_form2_interp (normalize_qf_form2 norm_form) vs = qf_form_interp norm_form vs" 
proof -
  have "(0 < norm_num2_interp (normalize_num2 norm_num) vs) = (0 < norm_num_interp norm_num vs)"
      for norm_num 
    apply (induct norm_num rule:normalize_num2.induct)
    apply (auto simp del:cancel_normalize_num.simps simp add:cancel_norm int_poly_smult)
    by (metis de_lcm_pos mult.commute of_int_0_less_iff zero_less_mult_pos2)
  moreover have "(0 = norm_num2_interp (normalize_num2 norm_num) vs) = (0 = norm_num_interp norm_num vs)"
      for norm_num 
    apply (induct norm_num rule:normalize_num2.induct)
    apply (auto simp del:cancel_normalize_num.simps simp add:cancel_norm int_poly_smult)
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

section \<open>Decision procedure\<close>

(*representation of real algebraic numbers*)
datatype alg_float = Arep "int poly" float float  
                   | Flt float \<comment>\<open>a small optimization when the number is dyadic\<close>

fun extractPols_num:: "norm_num2 \<Rightarrow> (float poly) set option" where
  "extractPols_num (Pol p v) = (if v=0 then Some {of_int_poly p} else None)" |
  "extractPols_num (Const c) =  Some {}" |
  "extractPols_num (Abnorm v) = None"

fun extractPols:: "qf_form2 \<Rightarrow> (float poly) set option" where
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

definition mid::"float \<Rightarrow> float \<Rightarrow> float" where
  "mid a b = (a+b)*Float 1 (- 1)"

lemma mid_ordering_intros:
  "a<b \<Longrightarrow> real_of_float a < real_of_float b"
  "\<lbrakk>a<b;b<c \<or> b=c\<rbrakk>\<Longrightarrow>mid a b < c"
  "\<lbrakk>a<b;c<a \<or> c=a\<rbrakk>\<Longrightarrow>c < mid a b "
  unfolding mid_def using powr_neg_one by auto

fun mk_samples_aux :: "alg_float list \<Rightarrow> alg_float list" where
  "mk_samples_aux []  = []"|
  "mk_samples_aux [x] = 
    (case x of
      Arep p lb ub \<Rightarrow> [Arep p lb ub] |
      Flt r \<Rightarrow>[Flt r])"|
  "mk_samples_aux (x1#x2#xs)  = 
    (case (x1,x2) of 
      (Arep p1 lb1 ub1,Arep p2 lb2 ub2) \<Rightarrow> (Arep p1 lb1 ub1) # (Flt (mid ub1 lb2)) # mk_samples_aux (x2#xs)|
      (Flt r1,Arep p2 lb2 ub2) \<Rightarrow> Flt r1 # (Flt (mid r1 lb2)) # mk_samples_aux (x2#xs)|
      (Arep p1 lb1 ub1,Flt r2) \<Rightarrow> (Arep p1 lb1 ub1)#(Flt (mid ub1 r2))# mk_samples_aux (x2#xs)|
      (Flt r1,Flt r2) \<Rightarrow> Flt r1 # (Flt (mid r1 r2)) # mk_samples_aux (x2#xs))"

definition mk_samples:: "alg_float list \<Rightarrow> alg_float list" where
  "mk_samples xs = (if xs=[] then [Flt 0] else ( let
     fst_s = (case (hd xs) of
       Arep _ lb1 _ \<Rightarrow> Flt (lb1-1)|
       Flt r1 \<Rightarrow> Flt (r1 - 1));
     last_s = (case (last xs) of
       Arep _ _ ub2 \<Rightarrow> Flt (ub2+1) |
       Flt r2 \<Rightarrow> Flt (r2+1))
   in  [fst_s]@mk_samples_aux xs@[last_s]))"

lemma mk_samples_neq_nil:"mk_samples xs\<noteq>[]" 
  by (metis (no_types, lifting) Nil_is_append_conv mk_samples_def not_Cons_self2)

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


fun ordered_reps:: "alg_float list \<Rightarrow> bool" where
  "ordered_reps [] = True" |
  "ordered_reps [_] = True" |
  "ordered_reps (x1#x2#xs) = (let 
     x1' = (case x1 of
       Arep _ _ ub1 \<Rightarrow>  ub1|
       Flt r1 \<Rightarrow> r1 );
     x2' = (case x2 of
       Arep _ lb2 _ \<Rightarrow>  lb2 |
       Flt r2 \<Rightarrow> r2)
    in x1'< x2' \<and> ordered_reps (x2#xs))"

fun of_alg_float:: "alg_float \<Rightarrow> real" where
  "of_alg_float (Arep p lb ub) = Alg p lb ub"|
  "of_alg_float (Flt f) = real_of_float f"

definition valid_list::"alg_float list \<Rightarrow> bool" where
  "valid_list vs = list_all (\<lambda>x. case x of Arep p lb ub \<Rightarrow> valid_alg p lb ub | _ \<Rightarrow> True) vs"

lemma valid_list_mk_samples: "valid_list vs \<Longrightarrow> valid_list (mk_samples vs)"
proof (induct vs rule:list_Cons_induct)
  case Nil
  thus ?case unfolding mk_samples_def valid_list_def by auto
next
  case (Cons x)
  thus ?case unfolding mk_samples_def valid_list_def 
    by (auto split:alg_float.splits)
next
  case (CCons x1 x2 xs)
  hence "valid_list (mk_samples (x2 # xs))" unfolding valid_list_def by auto
  hence "valid_list (tl (mk_samples (x2 # xs)))"
    unfolding mk_samples_def by (simp add: valid_list_def)
  thus ?case using CCons.prems unfolding valid_list_def
    by (auto simp add:mk_samples_Cons split:alg_float.splits)
qed

lemma alg_ordering_intros:
  "\<lbrakk>valid_alg p1 lb1 ub1;valid_alg p2 lb2 ub2;ub1<lb2\<rbrakk> \<Longrightarrow> Alg p1 lb1 ub1 < Alg p2 lb2 ub2"
  "\<lbrakk>valid_alg p lb ub;lb'<real_of_float lb \<or> lb' = real_of_float lb\<rbrakk> \<Longrightarrow> lb' < Alg p lb ub "
  "\<lbrakk>valid_alg p lb ub;real_of_float ub < ub' \<or> real_of_float ub = ub'\<rbrakk> \<Longrightarrow> Alg p lb ub<ub'"
subgoal by (meson alg_bound_and_root(1) alg_bound_and_root(2) less_float.rep_eq less_trans)
subgoal using alg_bound_and_root(1) less_trans by blast
subgoal using alg_bound_and_root(2) less_trans by blast
done  

lemma strict_sorted_algs:
  fixes root_reps:: "alg_float list"
  defines "algs\<equiv>(map of_alg_float root_reps)"
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
  moreover have "x1<x2" using CCons
    by (auto split:alg_float.splits intro!:alg_ordering_intros simp add:valid_list_def)
  ultimately show ?case by simp
qed

lemma strict_sorted_algs_mk_samples:
  fixes root_reps:: "alg_float list"
  defines "samples\<equiv> (map of_alg_float (mk_samples root_reps))" 
  assumes order:"ordered_reps root_reps" 
    and valid:"valid_list root_reps"
  shows "strict_sorted samples" 
proof -
  let ?isv="\<lambda>x. case x of Arep p lb ub \<Rightarrow> valid_alg p lb ub | _ \<Rightarrow> True"
  have "ordered_reps (mk_samples root_reps)"
    using order valid
    proof (induct root_reps rule:list_Cons_induct) 
      case Nil
      thus ?case unfolding mk_samples_def by auto
    next
      case (Cons x1)
      thus ?case unfolding mk_samples_def by (auto split:alg_float.splits)
    next
      case (CCons x1 x2 xs)
      let ?x1="case x1 of Arep p lb ub \<Rightarrow> ub | Flt r \<Rightarrow> r"
      let ?x2="case x2 of Arep p lb ub \<Rightarrow> lb | Flt r \<Rightarrow> r"
      define ys where "ys\<equiv>tl (tl (mk_samples (x2 # xs)))"
      have "?x1<?x2" using CCons.prems(1) by auto
      moreover have "ordered_reps (mk_samples (x2 # xs))" 
        using CCons by (auto simp add:valid_list_def)
      then have "ordered_reps (x2#ys)" unfolding ys_def
        unfolding mk_samples_def
        apply (cases xs)
        by (auto split:alg_float.splits)
      moreover have  "tl (mk_samples (x2 # xs)) = x2#ys"
        unfolding ys_def mk_samples_def
        apply (cases xs)
        by (auto split:alg_float.splits) 
      ultimately show ?case 
        by (auto simp add: mk_samples_Cons split: alg_float.splits intro!:mid_ordering_intros)
    qed
  moreover have "list_all ?isv (mk_samples root_reps)" using valid
    proof (induct root_reps rule:list_Cons_induct) 
      case Nil
      thus ?case unfolding mk_samples_def by auto
    next
      case (Cons x1)
      thus ?case unfolding mk_samples_def 
        by (auto split:alg_float.splits simp add:valid_list_def)
    next
      case (CCons x1 x2 xs)
      let ?v="case_alg_float valid_alg (\<lambda>float. True)"
      have "list_all ?v (mk_samples (x2 # xs))" 
        using CCons by (auto simp add:valid_list_def)
      then have "list_all ?v (tl (mk_samples (x2 # xs)))" by (simp add: mk_samples_def)
      moreover have "?v x1" "?v x2" 
        using CCons.prems by (auto simp add:valid_list_def)
      ultimately show ?case 
        by (auto simp add: mk_samples_Cons split: alg_float.splits )
    qed
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
  fixes root_reps:: "alg_float list"
  defines "samples\<equiv>map of_alg_float (mk_samples root_reps)" 
      and "decomps\<equiv>decomp (map of_alg_float root_reps)"
  assumes "ordered_reps root_reps" "valid_list root_reps"
  shows "are_samples samples decomps \<and> distinct decomps" using assms
proof (induct root_reps arbitrary:samples decomps rule:list_Cons_induct)
  case Nil
  show ?case unfolding mk_samples_def decomp_def by simp
next
  case (Cons x)
  thus ?case unfolding mk_samples_def decomp_def valid_list_def
    apply (simp split:alg_float.splits add:not_eq_sets)
    using alg_bound_and_root(1) alg_bound_and_root(2) by fastforce
next
  case (CCons x1 x2 xs)
  then have "are_samples (map of_alg_float (mk_samples (x2 # xs))) (decomp (map of_alg_float (x2 # xs))) \<and>
      distinct (decomp (map of_alg_float (x2 # xs)))" 
    unfolding valid_list_def by auto
  then have "are_samples (map of_alg_float (tl (mk_samples (x2 # xs))))
     (tl (decomp (map of_alg_float (x2 # xs))))" 
     by (metis are_samples.elims(2) decomp_neq_Nil list.sel(3) map_tl)
  then have "are_samples (map of_alg_float (mk_samples (x1 # x2 # xs)))
     (decomp (map of_alg_float (x1 # x2 # xs)))"
     using mk_samples_Cons decomp_Cons CCons.prems 
     apply (auto split:alg_float.splits)
     by (auto intro!:alg_ordering_intros mid_ordering_intros simp add:valid_list_def)
  moreover have "distinct (decomp (map of_alg_float (x1#x2 # xs)))"
    using decomp_distinct  strict_sorted_algs[OF CCons.prems]
    by auto
  ultimately show ?case by auto
qed

lemma qf_form_interp_cong:
  assumes "Some pols = extractPols qf_form"
          "\<forall>p\<in>pols. sgn_at (of_float_poly p) x1 = sgn_at (of_float_poly p) x2"
  shows "qf_form2_interp qf_form (x1#vs) = qf_form2_interp qf_form (x2#vs)"
    using assms
proof (induct  arbitrary: x1 x2 pols rule:qf_form2_interp.induct ) print_cases
  case (1 norm_num vs) 
  thus ?case 
    by (case_tac norm_num,auto simp add:sgn_at_def Real.sgn_real_def split: if_splits)
next
  case (2 norm_num vs)
  thus ?case by (case_tac norm_num,auto simp add:sgn_at_def Real.sgn_real_def split: if_splits)
next
  case (3 qf_form vs)
  hence "qf_form2_interp qf_form (x1 # vs) = qf_form2_interp qf_form (x2 # vs)" by auto
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
  shows "sgn_at p x1=sgn_at p x2"
proof -
  have "sgn_at p x1\<noteq>0" "sgn_at p x2\<noteq>0" unfolding sgn_at_def sgn_0_0 using assms  by auto
  moreover have "sgn_at p x1=1 \<Longrightarrow> sgn_at p x2 = -1 \<Longrightarrow> False" 
    unfolding sgn_at_def sgn_1_pos sgn_1_neg
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
  moreover have "sgn_at p x1=-1 \<Longrightarrow> sgn_at p x2 = 1 \<Longrightarrow> False" 
    unfolding sgn_at_def sgn_1_pos sgn_1_neg
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
  ultimately show "sgn_at p x1 = sgn_at p x2" unfolding sgn_at_def by (metis sgn_if)
qed

lemma decomp_by_roots_base:
  fixes roots:: "real list" and p::"real poly"
  assumes "{r. poly p r=0} \<subseteq> set points" "strict_sorted points" 
  shows  "\<forall>d\<in>set (decomp points). \<forall>y1\<in>d.\<forall>y2\<in>d. sgn_at p y1 = sgn_at p y2" using assms
proof (induct points arbitrary:p)
  case Nil
  thus ?case unfolding decomp_def 
    by (simp add:no_root_imp_same_sgn[of "UNIV::real set",simplified])    
next
  case (Cons x1 xs) thm no_root_imp_same_sgn[of "{..<x1}",simplified]
  have "p=0 \<Longrightarrow> ?case" unfolding sgn_at_def by simp
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
      have "\<forall>d\<in>set (tl (decomp xs)). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn_at p y1 = sgn_at p y2"
        proof (cases  "poly p x1=0")
          case False
          have "\<forall>d\<in>set (decomp xs). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn_at p y1 = sgn_at p y2"
            using Cons `poly p x1\<noteq>0` strict_sorted_Cons by auto
          thus ?thesis by (meson decomp_neq_Nil list.set_sel(2))
        next
          case True
          define x1_p where "x1_p\<equiv>[:-x1,1:]^(order x1 p)"
          have "order x1 p\<noteq>0" using True order_root `p \<noteq> 0` by auto
          obtain p' where p:"p=p' * x1_p" and not_dvd: "\<not> [:-x1,1:] dvd p'" unfolding x1_p_def 
            by (metis `p\<noteq>0` mult.commute order_decomp)
          have "\<forall>d\<in>set (tl (decomp xs)). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn_at p' y1 = sgn_at p' y2"
            proof -
              have "{x. poly x1_p x=0} = {x1}" 
                unfolding x1_p_def using PolyMisc.poly_power_n_eq `order x1 p\<noteq>0` by auto
              moreover have "poly p' x1\<noteq>0" using not_dvd by (metis poly_eq_0_iff_dvd)
              moreover have "x1\<notin>set xs" using Cons.prems(2) strict_sorted_Cons by auto
              ultimately have  "{r. poly p' r = 0} \<subseteq> set xs "
                using Cons.prems(1) unfolding p by auto
              hence "\<forall>d\<in>set (decomp xs). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn_at p' y1 = sgn_at p' y2" 
                by (elim Cons.hyps,metis Cons.prems(2) strict_sorted_Cons)
              thus ?thesis by (metis decomp_neq_Nil list.set_sel(2))
            qed
          moreover have "\<forall>d\<in>set (tl (decomp xs)). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn_at x1_p y1 = sgn_at x1_p y2"
            proof (rule+)
              fix d y1 y2 assume d:"d \<in> set (tl(decomp xs))" and y1:  "y1 \<in> d" and y2: "y2 \<in> d"
              have "\<Union>(set (tl (decomp (x2 # xs')))) = {x2..}" 
                using Cons.prems(2) union_decomp_tl strict_sorted_sorted unfolding xs 
                using strict_sorted_Cons by blast
              hence "x2\<le>y1" and "x2\<le>y2" using d y1 y2 unfolding xs by auto
              moreover have "\<forall>x\<in>{x2..}. poly x1_p x \<noteq> 0" unfolding x1_p_def 
                using PolyMisc.poly_power_n_eq[OF `order x1 p\<noteq>0`,of x1] `x2>x1` by auto
              ultimately show "sgn_at x1_p y1 = sgn_at x1_p y2"
                using no_root_imp_same_sgn[of "{x2..}" x1_p y1 y2,simplified] by auto
            qed
          ultimately show ?thesis 
            unfolding  sgn_at_def by (metis p sgn_mult poly_mult)
        qed
      moreover have "\<forall>y1\<in>{..<x1}. \<forall>y2\<in>{..<x1}. sgn_at p y1 = sgn_at p y2"
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
          ultimately show "sgn_at p y1 = sgn_at p y2"
            using no_root_imp_same_sgn[of "{..<x1}" p y1 y2,simplified] by auto
        qed
      moreover have "\<forall>y1\<in>{x1<..<x2}. \<forall>y2\<in>{x1<..<x2}. sgn_at p y1 = sgn_at p y2"
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
          thus "sgn_at p y1 = sgn_at p y2" 
            using y1 y2  no_root_imp_same_sgn[of "{x1<..<x2}" p y1 y2,simplified] by auto
        qed
      ultimately show ?case unfolding xs decomp_Cons by (simp (no_asm))
    qed
  ultimately show ?case by linarith
qed
     

lemma decomp_by_roots:
  fixes roots:: "real list" and pols::"float poly set"
  assumes roots:"{r. \<exists>p\<in>pols. p\<noteq>0 \<and> poly (of_float_poly p) r=0} \<subseteq> set roots " and 
          sorted:"strict_sorted roots"
  shows  "\<forall>p\<in>pols. \<forall>d\<in>set (decomp roots). \<forall>x1\<in>d.\<forall>x2\<in>d. sgn_at (of_float_poly p) x1 = sgn_at (of_float_poly p) x2" 
proof (rule ccontr)
  assume "\<not> (\<forall>p\<in>pols.\<forall>d\<in>set (decomp roots). \<forall>x1\<in>d. \<forall>x2\<in>d. sgn_at (of_float_poly p) x1 
    = sgn_at (of_float_poly p) x2)"
  then obtain d x1 x2 p where "p\<in>pols" and 
    d:"d\<in>set (decomp roots)" and x1:"x1\<in>d" and x2:"x2\<in>d" and 
    sgn_diff:"sgn_at (of_float_poly p) x1 \<noteq> sgn_at (of_float_poly p) x2" 
    by auto
  have "p\<noteq>0" using sgn_diff unfolding sgn_at_def by auto
  moreover have "{x. p\<noteq>0 \<and> poly (of_float_poly p) x=0} \<subseteq> set roots" using `p\<in>pols` roots by auto
  ultimately have "\<forall>d\<in>set (decomp roots). \<forall>y1\<in>d. \<forall>y2\<in>d. sgn_at (of_float_poly p) y1 
      = sgn_at (of_float_poly p) y2"
    using decomp_by_roots_base[of "of_float_poly p" roots,OF _ sorted]  by blast
  thus False using d x1 x2 sgn_diff by fast
qed 

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

lemma contain_all_roots:
  fixes algrats::"alg_float list" and pols::"float poly set"
  defines "points\<equiv>map of_alg_float algrats"
  assumes valid: "valid_list algrats" and
        all_roots:"contain_all_roots algrats pols" and
        ordered:"ordered_reps algrats"
  shows "{r. \<exists>p\<in>pols. p\<noteq>0\<and>poly (of_float_poly p) r=0} \<subseteq> set points" 
proof 
  fix x assume "x \<in> {r. \<exists>p\<in>pols. p \<noteq> 0 \<and> poly (of_float_poly p) r = 0}"
  then obtain pol where "pol\<in>pols" "pol\<noteq>0" and "poly (of_float_poly pol) x=0" by auto
  define pol' where "pol'\<equiv>of_float_poly pol"
  have "pol'\<noteq>0" "poly pol' x=0" 
    using \<open>pol\<noteq>0\<close> \<open>poly (of_float_poly pol) x=0\<close> unfolding pol'_def by auto
  have card_eq:"card {r\<in>set points. poly pol' r =0} = card {x. poly pol' x=0} " 
    proof -
      define sgn_at_pol where "sgn_at_pol\<equiv>\<lambda>p lb ub.  sgn_at_core pol (of_int_poly p) lb ub"
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
      also have "... = changes_R_spmods pol (pderiv pol)"
        using changes_spmods_smods(2)[of pol "pderiv pol"] of_float_poly_pderiv  
        unfolding pol'_def by auto     
      also have "... = (sum_list (map (\<lambda>x. case x of 
          Arep p lb ub \<Rightarrow> if (sgn_at_pol p lb ub) = 0 then 1 else 0 
          | Flt r \<Rightarrow> if poly pol r = 0 then 1 else 0) algrats))"
        using all_roots[unfolded contain_all_roots_def,rule_format
          ,OF `pol\<in>pols` `pol\<noteq>0`] 
        unfolding sgn_at_pol_def sgn_at_alg_float_core_def 
        by (auto split:alg_float.splits simp add:Let_def if_splits intro:arg_cong)
      also have "... = (sum_list (map (\<lambda>x. case x of 
          Arep p lb ub \<Rightarrow> if (sgn_at pol' (Alg p lb ub)) = 0 then 1 else 0 
          | Flt r \<Rightarrow> if sgn_at pol' (real_of_float r) = 0 then 1 else 0) algrats))"
        proof -
          have "(poly pol r= 0) = (sgn_at pol' (real_of_float r) =0)" for r
            unfolding sgn_at_def pol'_def
            by (simp add: of_float_poly_poly real_of_float_eq sgn_zero_iff)
          moreover have "\<And>p lb ub. valid_alg p lb ub  
              \<Longrightarrow> of_int (sgn_at_pol p lb ub) = sgn_at pol' (Alg p lb ub)"
            unfolding sgn_at_pol_def pol'_def
            apply (subst sgn_at_core)
            by (auto simp add:Let_def pol'_def sgn_at_def sign_def)
          ultimately show ?thesis 
            using valid[unfolded valid_list_def list_all_iff]
            apply (intro list.map_cong0[THEN arg_cong])
            apply (subst of_int_eq_0_iff[symmetric,where 'a=real])
            by (auto split:alg_float.splits simp del:of_int_eq_0_iff )
        qed
      also have "... = sum_list (map (\<lambda>r. if sgn_at pol' r=0 then 1 else 0) points)"
        unfolding points_def 
        by (induct algrats,auto split: alg_float.splits)
      also have "... = of_nat (card {r\<in>set points. sgn_at pol' r =0})"
        apply (subst sum_list_distinct_conv_sum_set[OF \<open>distinct points\<close>])
        apply (subst sum.mono_neutral_right[OF finite_set,
                  of "{r \<in> set points. sgn_at pol' r = 0}" points])
        by auto
      finally have "int (card {x. poly pol' x = 0}) = 
        int (card {r \<in> set points. sgn_at pol' r = 0})" .
      then show ?thesis using int_int_eq  
        by (auto simp add:sgn_at_def sgn_zero_iff)
    qed
  moreover have "finite {x. poly pol' x=0}" 
    using `pol'\<noteq>0` by (metis poly_roots_finite)
  ultimately have " {r\<in>set points. poly pol' r =0} =  {x. poly pol' x=0}"
    by (elim Finite_Set.card_subset_eq[rotated 2]) auto
  thus "x \<in> set points" using \<open>poly pol' x=0\<close> by auto 
qed

lemma allQ_subst:
  fixes root_reps:: "alg_float list"
  defines "samples\<equiv>map of_alg_float (mk_samples root_reps)"
  assumes pols:"Some pols = extractPols qf_form" and  
          ordered:"ordered_reps root_reps" and 
          all_roots:"contain_all_roots root_reps pols" and
          valid: "valid_list root_reps"
  shows "norm_form2_interp (AllQ (QF qf_form)) vs 
    = (\<forall>x \<in> (set samples). norm_form2_interp (QF qf_form) (x#vs)) " (is "?L= ?R")
proof -
  define decomps where "decomps\<equiv>decomp (map of_alg_float root_reps)" 
  define P where "P\<equiv>\<lambda>x. norm_form2_interp (QF qf_form) (x # vs)"
  define val where "val\<equiv>\<lambda>x. case x of Arep p lb ub \<Rightarrow> valid_alg p lb ub | Flt x \<Rightarrow> True"
  have "finite (set decomps)" using finite_decomp unfolding decomps_def .
  have "are_samples samples decomps" and "strict_sorted (map of_alg_float root_reps)" 
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
    using \<open>strict_sorted (map of_alg_float root_reps)\<close> contain_all_roots[THEN decomp_by_roots,
      OF valid all_roots ordered ,folded  samples_def decomps_def] 
      qf_form_interp_cong[OF pols,of _ _ vs]
    unfolding P_def 
    by (metis norm_form2_interp.simps(1))
  moreover have "(\<Union>(set decomps) = \<real>)" 
    using union_decomp \<open>strict_sorted (map of_alg_float root_reps)\<close> 
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

fun qf_form2_interp_core:: "qf_form2 \<Rightarrow> alg_float list \<Rightarrow> bool" where 
  "qf_form2_interp_core (Pos (Pol p v)) vs = (sgn_at_alg_float_core (of_int_poly p) (vs!v) = 1)"|
  "qf_form2_interp_core (Zero (Pol p v)) vs = (sgn_at_alg_float_core (of_int_poly p) (vs!v) = 0)"|
  "qf_form2_interp_core (Neg qf_form) vs= (\<not> qf_form2_interp_core qf_form vs)"|
  "qf_form2_interp_core (Disj qf_form1 qf_form2) vs
      = (qf_form2_interp_core qf_form1 vs \<or> qf_form2_interp_core qf_form2 vs)"|
  "qf_form2_interp_core (Conj qf_form1 qf_form2) vs
      = (qf_form2_interp_core qf_form1 vs \<and> qf_form2_interp_core qf_form2 vs)"|
  "qf_form2_interp_core form vs= qf_form2_interp form (map of_alg_float vs)"

lemma qf_form2_interp_core:
  assumes "valid_list vs" "var_bound form (length vs)" 
  shows "qf_form2_interp form (map of_alg_float vs) = qf_form2_interp_core form vs" 
  using assms 
apply (induct form arbitrary:vs )
subgoal for num vs unfolding valid_list_def
  apply (cases num)
  by (auto split:alg_float.splits if_splits simp add: sgn_at_alg_float_core_def sgn_at_core 
    list_all_length of_float_poly_poly Let_def sign_def)
subgoal for num vs unfolding valid_list_def
  apply (cases num)
  apply (auto split:alg_float.splits if_splits simp add: sgn_at_alg_float_core_def sgn_at_core 
    list_all_length of_float_poly_poly Let_def sign_def)
  apply (metis of_float_int_poly of_float_poly_poly zero_float.rep_eq)
  by (simp add: of_float_poly_poly real_of_float_eq)
by auto

lemma allQ_intro:
  fixes root_reps:: "alg_float list"
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
  ultimately show "qf_form2_interp qf_form [of_alg_float x]"
    apply (subst qf_form2_interp_core[of "[x]",simplified,OF _ assms(5)])
    by auto
qed

definition check_qf_form_samples::"alg_float list \<Rightarrow> qf_form2 \<Rightarrow> bool" where
  "check_qf_form_samples ss fm = (\<forall>x \<in> (set ss). qf_form2_interp_core fm [x])"

lemma allQ_intro_code[unfolded Let_def]:
  fixes root_reps:: "alg_float list"
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
  fixes x::"alg_float"
  assumes "valid_list [x]" "var_bound form (Suc 0)" "qf_form2_interp_core form ([x])"
  shows "norm_form2_interp (ExQ (QF form)) []" 
apply simp
apply (intro exI[where x="of_alg_float x"])
using qf_form2_interp_core[OF assms(1),simplified,OF assms(2)] assms(3)
by auto

lemma ExQ_intro_code[unfolded Let_def]:
  fixes x::"alg_float"
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

(*
definition float_of_rat::"rat \<Rightarrow> float" where
  "float_of_rat r = (let (n,d) = quotient_of r in Float n (- bitlen d + 1))"
*)

definition float_of_rat_l::"rat \<Rightarrow> float" where
  "float_of_rat_l r = (let (n,d) = quotient_of r in lapprox_rat 10 n d)"

definition float_of_rat_r::"rat \<Rightarrow> float" where
  "float_of_rat_r r = (let (n,d) = quotient_of r in rapprox_rat 10 n d)"

definition rat_to_alg::"rat \<Rightarrow> alg_float" where
  "rat_to_alg r = (
      if r=0 then 
        Flt 0 
      else (
        let
          (r1,r2) = quotient_of r;
          lb = lapprox_rat 5 r1 r2;
          ub =  rapprox_rat 5 r1 r2
        in
          if lb=ub then Flt lb else Arep [:-r1,r2:] lb ub
      ))"  

definition alg_rat_aux_conv::"alg_rat_aux \<Rightarrow> alg_float" where
  "alg_rat_aux_conv = (\<lambda>x. case x of 
      ALG p lb ub \<Rightarrow> Arep p (float_of_rat_l lb) (float_of_rat_r ub)
     |RAT r \<Rightarrow> rat_to_alg r) "

definition alg_rat_list_conv::"alg_rat_aux list \<Rightarrow> alg_float list" where
  "alg_rat_list_conv = map alg_rat_aux_conv " 

(*
declare [[ML_source_trace]] -- \<open>For debug purposes\<close>
*)

lemma [code_computation_unfold]:
  "numeral x = rat_of_int (Code_Target_Int.positive x)"
  "numeral x = real_of_int (Code_Target_Int.positive x)"
  by simp_all


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
       "(=)::alg_float\<Rightarrow>alg_float\<Rightarrow>bool"

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

      (*real*)
      "0::real" "1::real"
      "uminus :: real \<Rightarrow> _"
      "(/) :: real \<Rightarrow> _"
      
      (*list*)
      "Cons :: alg_float \<Rightarrow> _" "Nil :: alg_float list"
      "list_all (\<lambda>x. qf_form2_interp_core fm [x])"

      (*set*)
      "{}::float poly set"
      "insert :: float poly \<Rightarrow> _"

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
      RCF_Decision_Proc.qf_form2.Disj
      RCF_Decision_Proc.qf_form2.Conj
      RCF_Decision_Proc.qf_form2.Zero
      RCF_Decision_Proc.qf_form2.Neg
      RCF_Decision_Proc.qf_form2.Pos
      RCF_Decision_Proc.norm_num2.Pol
      RCF_Decision_Proc.ordered_reps
      RCF_Decision_Proc.check_qf_form_samples

      (*misc*)
      Code_Target_Nat.natural
      Code_Target_Int.positive
      Code_Target_Int.negative
      Code_Numeral.positive
      Code_Numeral.negative
  
     datatypes:Num.num bool alg_float alg_rat_aux float real "alg_rat_aux list"
  };
\<close>

SML_import \<open>val println = Output.writeln\<close>
SML_import \<open>val zz_gcd = Integer.gcd\<close>
SML_import \<open>val zz_lcm = Integer.lcm\<close>

SML_file "rat.sml"
SML_file "Algebra.sig"
SML_file "Algebra.sml"
SML_file "Mathematica.sml"

SML_export \<open>val execute_MathKernel_print = Mathematica.execute_and_print \<close>

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
(*
lemma example_2:
    "\<forall>x::real. x^2/2 - x + 1/2 \<ge>0 "
  apply (tactic \<open>
  (   (Reflection.default_reflection_tac 
      @{context}   
      @{thms norm_form2_correct} 
      @{thms num_interp_eqs form_interp.simps} 
      NONE)
    THEN' 
        (simp_tac (@{context} delsimps @{thms norm_form2_interp.simps} 
        addsimps @{thms power_numeral_even power_numeral_odd})) ) 1 
  \<close>)
  apply (tactic \<open>
    resolve0_tac [(infer_instantiate' @{context}
        [NONE,NONE,SOME (Thm.cterm_of @{context} (@{term alg_rat_list_conv} 
        $ @{term "[RAT (-2),ALG [:-2,0,1:] (-3/2) (-1), ALG [:-2,0,1:] 1 2]"}))] @{thm allQ_intro_code})]
    1
    THEN 
      simp_tac @{context} 1
    \<close>)
apply (tactic \<open>
    (CONVERSION (rcf_holds @{context}) 1 )
  THEN 
    resolve0_tac [TrueI] 1\<close>
)
*)


  
end
