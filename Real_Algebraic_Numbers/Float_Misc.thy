theory Float_Misc imports 
  Main
  "~~/src/HOL/Library/Float"
begin

definition rat_of_float::"float \<Rightarrow> rat" where 
  "rat_of_float f = (let e=exponent f;m=mantissa f in 
    if e\<ge>0 then rat_of_int(m*2^nat e) else Fract m (2^nat (- e)))"

lemma real_of_rat_of_float[simp]:
  "real_of_rat (rat_of_float f) = real_of_float f"
  unfolding rat_of_float_def 
  by (auto simp add:Let_def mantissa_exponent of_rat_mult of_rat_power of_rat_divide 
    powr_real_of_int field_simps of_rat_rat)

end