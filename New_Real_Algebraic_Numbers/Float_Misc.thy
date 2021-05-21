theory Float_Misc imports 
  Main
  "HOL-Library.Float"
  "Affine_Arithmetic.Float_Real"
begin

definition rat_of_float::"float \<Rightarrow> rat" where 
  "rat_of_float f = (let e=exponent f;m=mantissa f in 
    if e\<ge>0 then rat_of_int(m*2^nat e) else Fract m (2^nat (- e)))"

lemma real_of_rat_of_float[simp]:
  "real_of_rat (rat_of_float f) = real_of_float f"
  unfolding rat_of_float_def 
  by (auto simp add:Let_def mantissa_exponent of_rat_mult of_rat_power of_rat_divide 
    powr_real_of_int field_simps of_rat_rat)

lemma rat_of_float_of_int[simp]:
  "rat_of_float (float_of_int x) = rat_of_int x"
  by (metis of_rat_eq_iff of_rat_of_int_eq real_of_float_of_int_eq real_of_rat_of_float)

lemma rat_of_float_0[simp]: "rat_of_float 0 = 0"
  using rat_of_float_def by auto

lemma rat_of_float_1[simp]: "rat_of_float 1 = 1"
  by (simp add: exponent_1 mantissa_1 rat_of_float_def)

lemma rat_of_float_add: "rat_of_float (x + y) = rat_of_float x + rat_of_float y"
proof -
  have "real_of_rat (rat_of_float (x + y)) = real_of_rat (rat_of_float x + rat_of_float y)"
    by (simp add: of_rat_add)
  then show ?thesis using of_rat_eq_iff by blast
qed

lemma rat_of_float_mult: "rat_of_float (x * y) = rat_of_float x * rat_of_float y"
proof -
  have "real_of_rat (rat_of_float (x * y)) = real_of_rat (rat_of_float x * rat_of_float y)"
    by (simp add: of_rat_mult)
  then show ?thesis using of_rat_eq_iff by blast
qed

end