theory Second
  imports Complex_Main 
begin

text \<open>
  Second task :
  
  https://www.imo-official.org/problems/IMO2009SL.pdf , problem A2
------------------------------------------------------------------      
  Let a, b, c be positive real numbers such that 1/a + 1/b + 1/c = a + b + c. Prove that:
 
          1                   1                     1           3
    --------------   +  --------------   +   --------------  \<le> ---
    (2a + b + c)^2      (2b + c + a)^2       (2c + a + b)^2     16
------------------------------------------------------------------
  Idea for solving :
    
    - using AM_GM_2 and inequality_1  we can transform left side to : 
      1/2 * expression
    
    - expression = fraction_1 * fraction_2 * fraction_3. Using lemmas
      L1, L2, L3 in LF we get that expression \<le> 3/8 and then we have
      left side \<le> 1/2 * 3/8 = 3/16
\<close>


(* AM–GM inequality for two numbers *)
lemma AM_GM_2 [simp]:
  fixes x y :: real
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "(x + y)/ 2 \<ge> sqrt(x*y)"
  using assms
  using arith_geo_mean_sqrt 
  by blast

(* Inequality used in first part 
    (left side transformation)   *)
lemma inequality_1 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "1/((2*x + y + z)^2) \<le>  1/(4*(x + y)*(x + z))"
proof-

  have "2 * sqrt ((x + y)*(x + z)) \<le> (x + y) + (x + z)"
    using AM_GM_2 [of "x + y" "x + z"]
    using assms(1) assms(2) assms(3) 
    by simp
  also have "... = 2*x + y + z"
    by simp
  finally have 1 : "2 * sqrt ((x + y)*(x + z)) \<le> 2*x + y + z"
    by simp

  have "(2*x + y + z)^2 \<ge> (2*sqrt((x + y)*(x + z)))^2"
    using assms(1) assms(2) assms(3)
    using 1
    by (smt (verit, ccfv_SIG) power_mono real_sqrt_ge_0_iff zero_le_mult_iff)
  then have "(2*x + y + z)^2 \<ge> 4*(x + y)*(x + z)"
    using assms(1) assms(2) assms(3)
    by (simp add: distrib_right)
  then have "1/((2*x + y + z)^2) \<le>  1/(4*(x + y)*(x + z))"
    using assms
    by (smt frac_le mult_pos_pos)
  then show ?thesis
    .
qed

(* This inequality will be used in lemma L1
       (before using, we must prove it)     *)
lemma inequality_L1 [simp]:
  fixes x y z :: real
  assumes  "x > 0" "y>0" "z > 0"
  shows "x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y \<ge> 6*x*y*z"
proof-

  have "z*(x - y)^2 + x*(y - z)^2 + y*(z - x)^2 \<ge> 0"
    using assms(1) assms(2) assms(3)
    by simp
  then have "z*(x^2 - 2*x*y + y^2) + x*(y^2 - 2*y*z + z^2) + y*(z^2 - 2*z*x + x^2) \<ge> 0"
    by (simp add: diff_add_eq power2_diff)
  then have "z*x^2 - z*2*x*y + z*y^2 + x*(y^2 - 2*y*z + z^2) + y*(z^2 - 2*z*x + x^2) \<ge> 0"
    by (simp add: diff_le_eq distrib_left right_diff_distrib')
  then have "z*x^2 - z*2*x*y + z*y^2 + x*y^2 - x*2*y*z + x*z^2 + y*(z^2 - 2*z*x + x^2) \<ge> 0"
    by (simp add: diff_le_eq distrib_left right_diff_distrib') 
  then have "z*x^2 - z*2*x*y + z*y^2 + x*y^2 - x*2*y*z + x*z^2 + y*z^2 - y*2*z*x + y*x^2 \<ge> 0"
    by (simp add: diff_le_eq distrib_left right_diff_distrib') 
  then have "x^2*z - 2*x*y*z + y^2*z + y^2*x - 2*x*y*z + z^2*x + z^2*y - 2*x*y*z + x^2*y \<ge> 0"
    by (simp add: mult.commute)
  then have "x^2*z + y^2*z + y^2*x + z^2*x + z^2*y + x^2*y - 6*x*y*z \<ge> 0"
    by simp
  then show ?thesis
    by simp
qed

(* Key lemma used in final lemma LF *)
lemma L1 [simp]:
 fixes x y z :: real
 assumes  "x > 0" "y>0" "z > 0"
 assumes "x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y \<ge> 6*x*y*z"
 shows "((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x)) \<le> 9/8"
proof-

  have "x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y \<ge> 6*x*y*z"
    using assms(4)
    by simp
  then have "(9-8)*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) \<ge> (24-18)*(x*y*z)"
    by simp
  then have "9*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) - 8 *(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) 
          \<ge> 24*x*y*z - 18*x*y*z"
    by (simp add: mult.commute mult.left_commute)
  then have "9*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) + 18*x*y*z \<ge> 24*x*y*z + 8 *(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y)"
    by simp
  then have "9*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) + 18*x*y*z \<ge> 24*x*y*z + 8*x^2*y + 8*x^2*z + 8*y^2*x + 8*y^2*z + 8*z^2*x + 8*z^2*y"
    by simp
  then have "9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 18*x*y*z \<ge> 24*x*y*z + 8*x^2*y + 8*x^2*z + 8*y^2*x + 8*y^2*z + 8*z^2*x + 8*z^2*y"
    by simp
  then have "9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 18*x*y*z \<ge>  8*x^2*y + 8*x*y*z + 8*x^2*z + 8*y^2*x + 8*y^2*z + 8*x*y*z + 8*x*y*z + 8*z^2*x + 8*z^2*y"
    by simp
  then have "9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 18*x*y*z \<ge> (8*x + 8*y + 8*z)*(x*y + y*z + z*x)"
    by (simp add: add.commute add.left_commute distrib_left mult.commute mult.left_commute power2_eq_square)
  then have "9*x*y*z + 9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 9*x*y*z \<ge> (8*x + 8*y + 8*z)*(x*y + y*z + z*x)"
    by simp
  then have "(9*x + 9*y)*(y*z + y*x + z^2 + z*x) \<ge> (8*x + 8*y + 8*z)*(x*y + y*z + z*x)"
    by (simp add: add.commute add.left_commute distrib_left mult.commute mult.left_commute power2_eq_square)
  then have * : " 9*(x + y)*(y + z)*(z + x) \<ge> 8*(x + y + z)*(x*y + y*z + z*x)"
    by (simp add: add.left_commute distrib_left left_diff_distrib mult.commute mult.left_commute right_diff_distrib power2_eq_square)

  have ** : "(x + y)*(y + z)*(z + x)>0"
    using assms(1) assms(2) assms(3)
    by simp

  have "9*(x + y)*(y + z)*(z + x) \<ge> 8*(x + y + z)*(x*y + y*z + z*x)"
    using *
    using assms(1) assms(2) assms(3)
    by blast
  then have "9/8 * (x + y)*(y + z)*(z + x) \<ge> (x + y + z)*(x*y + y*z + z*x)"
    by linarith
  then have "9/8 * (x + y)*(y + z)*(z + x) \<ge> (x + y + z)*(x*y + y*z + z*x)*((x + y)*(y + z)*(z + x))/((x + y)*(y + z)*(z + x))"
    using assms(1) assms(2) assms(3)
    by simp
  then have "9/8 * ((x + y)*(y + z)*(z + x)) \<ge> ((x + y + z)*(x*y + y*z + z*x)/((x + y)*(y + z)*(z + x)))*(x + y)*(y + z)*(z + x)"
    by (metis (mono_tags, hide_lams) mult.assoc times_divide_eq_left)
  then show "9/8 \<ge> ((x + y + z)*(x*y + y*z + z*x)/((x + y)*(y + z)*(z + x)))"
    using **
    by (metis (no_types, hide_lams) ab_semigroup_mult_class.mult_ac(1) mult_le_cancel_right)
qed

(* Key lemma used in final lemma LF *)
lemma L2 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  assumes "1/x + 1/y + 1/z = x + y + z"
  shows "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) \<le> 1"
proof-
  from assms(4)
  have "x*y*z * (1/x + 1/y + 1/z) = x*y*z * (x + y + z)"
    by simp
  then have "x*y*z*(1/x) + x*y*z*(1/y) + x*y*z*(1/z)  = x*y*z * (x + y + z)"
    by (simp add: distrib_left)
  then have "y*z + x*z + x*y = x*y*z * (x + y + z)"
    using assms(1) assms(2) assms(3)
    by simp
  then have * : "x*y + y*z + z*x = x*y*z * (x + y + z)"
    using assms(1) assms(2) assms(3)
    by (simp add: mult.commute)

  have "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) \<le> 1"
    using *
    by simp
  then show ?thesis
    .
qed

(* This inequality will help us form inequality_L3 *)
lemma inequality_2 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "x^2*y^2 + x^2*z^2 \<ge> 2*x^2*y*z"
proof-
  have "(x^2*y^2 + x^2*z^2)/2 \<ge> sqrt(x^2*y^2 * x^2*z^2)"
    using AM_GM_2[of "x^2*y^2" "x^2*z^2"]
    using assms
    by (simp add: mult.assoc)
  then have "(x^2*y^2 + x^2*z^2) \<ge> 2*sqrt(x^2*y^2 * x^2*z^2)"
    by simp
  then have "(x^2*y^2 + x^2*z^2) \<ge> 2*sqrt(x^4*y^2*z^2)"
    by (smt mult.assoc mult.commute numeral_Bit0 power_add)
  then have "x^2*y^2 + x^2*z^2 \<ge> 2* (root 2 (x^4*y^2*z^2))"
    by (simp add: sqrt_def)
  then have "x^2*y^2 + x^2*z^2 \<ge> 2* (x^2*y*z)"
    by (smt assms(2) assms(3) numeral_Bit0 power2_eq_square power_add real_root_mult real_sqrt_abs sqrt_def zero_le_power2)
  then show ?thesis
    by simp
qed

(* This inequality will be used in lemma L3
       (before using, we must prove it)     *)
lemma inequality_L3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> x^2*y*z + x*y^2*z + x*y*z^2"
proof-
  have 1: "y^2*x^2 + y^2*z^2 \<ge> 2*y^2*x*z"
    using assms
    by simp

  have 2: "x^2*y^2  + x^2*z^2 \<ge> 2*x^2*y*z"
    using assms
    by simp

  have 3: "z^2*y^2 + z^2*x^2 \<ge> 2*z^2*y*x"
    using assms
    by simp

  have "y^2*x^2 + y^2*z^2 + x^2*y^2  + x^2*z^2 + z^2*y^2 + z^2*x^2 \<ge>  2*y^2*x*z +  2*x^2*y*z + 2*z^2*y*x"
    using 1 2 3 assms
    by linarith
  then have "2*(y^2*x^2 + y^2*z^2 + x^2*z^2) \<ge> 2 * (y^2*x*z + x^2*y*z + z^2*y*x)"
    using assms
    by (simp add: mult.commute)
  then show ?thesis
    by (simp add: mult.commute)
qed

(* Key lemma used in final lemma LF *)
lemma L3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> x^2*y*z + x*y^2*z + x*y*z^2"
  shows "(x*y*z*(x + y + z))/((x*y + y*z + z*x)^2) \<le> 1/3"
proof-

  from assms(4)
  have "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> x*y*z * (x + y + z)"
    by (simp add: \<open>x\<^sup>2 * y * z + x * y\<^sup>2 * z + x * y * z\<^sup>2 \<le> x\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2 + z\<^sup>2 * x\<^sup>2\<close> add.assoc add.commute add.left_commute add_diff_eq diff_add_eq diff_diff_add diff_diff_eq2 distrib_left mult.commute mult.left_commute power_mult_distrib right_diff_distrib' power2_eq_square)
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> (3-2) * (x*y*z * (x + y + z))"
    by simp
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> 3*x*y*z * (x + y + z) - 2*x*y*z * (x + y + z) "
    by simp
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 + 2*x*y*z * (x + y + z) \<ge> 3*x*y*z * (x + y + z)"
    by simp
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 + 2*x^2*y*z + 2*x*y^2*z + 2*x*y*z^2 \<ge> 3*x*y*z * (x + y + z)"
    by (simp add: distrib_right mult.commute power2_eq_square)
  then have * : "(x*y + y*z + z*x)^2 \<ge> 3*x*y*z * (x + y + z)"
    by (simp add: add.left_commute distrib_left left_diff_distrib mult.commute mult.left_commute right_diff_distrib power2_eq_square)

  have "(x*y + y*z + z*x)^2 \<ge> 3*x*y*z * (x + y + z)"
    using assms(1) assms(2) assms(3)  
    using *
    by simp
  then have ** : "1/(x*y + y*z + z*x)^2 \<le> 1/(3*x*y*z * (x + y + z))"
    using assms(1) assms(2) assms(3)
    by (smt frac_le mult_pos_pos)

  have "(x*y*z*(x + y + z))/((x*y + y*z + z*x)^2) \<le> x*y*z*(x + y + z) * (1/(x*y + y*z + z*x)^2)"
    by simp
  also have "... \<le> x*y*z*(x + y + z) * (1/(3*x*y*z * (x + y + z)))"
    using **
    by (meson add_nonneg_nonneg assms(1) assms(2) assms(3) less_imp_le mult_left_mono mult_nonneg_nonneg)
  also have "... \<le> x*y*z*(x + y + z)/(3*x*y*z * (x + y + z))"
    by simp
  also have "... \<le> 1/3"
    using assms(1) assms(2) assms(3)
    by simp
  finally show ?thesis
    .
qed

(*        Final lemma 
  (showing that expression \<le> 3/8) *)
lemma LF:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  assumes "1/x + 1/y + 1/z = x + y + z"
  shows "(((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x))) * ((x*y + y*z + z*x)/(x*y*z*(x + y + z))) * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2)) \<le> 3/8"
proof-

  have 11 : "((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 1 : "((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x)) \<le> 9/8"
    using assms(1) assms(2) assms(3)
    using L1
    by simp

  have 22 : "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 2 : "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) \<le> 1"
    using assms(1) assms(2) assms(3) assms(4)
    using L2
    by simp

  have 33 : "((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff zero_less_power)

  have 3 : "((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2)) \<le> 1/3"
    using assms(1) assms(2) assms(3)
    using L3
    by simp

  have " (((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x))) * ((x*y + y*z + z*x)/(x*y*z*(x + y + z))) * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2))
       \<le> 9/8 * ((x*y + y*z + z*x)/(x*y*z*(x + y + z))) * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2))"
    using 1 22 33
    by (metis mult_le_cancel_right mult_less_0_iff not_square_less_zero)
  also have " ...  \<le> 9/8 * 1 * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2))"
    using 1 11 2 33
    by (metis add_mono_thms_linordered_semiring(1) le_add_same_cancel1 less_imp_le mult_le_cancel_right mult_left_mono not_less)
  also have " ... \<le> 9/8 * 1 * 1/3"
    using 3 11 22 33
    using assms(1) assms(2) assms(3)
    by simp
  finally show ?thesis
    by simp
qed

(* Simple inequality *)
lemma inequality_3:
  fixes x :: real
  assumes "x > 0" "x \<le> 3/8"
  shows "1/2 * x \<le> 1/2 * 3/8"
  using assms
  by simp

(* Proof *)
lemma Final :
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" 
  assumes "1/a + 1/b + 1/c = a + b + c"
  shows " (1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 3/16"
proof-
  
  have 1 : "1/((2*a + b + c)^2) \<le> 1/(4*(a + b)*(a + c))"
    using assms(1) assms(2) assms(3)
    using inequality_1
    by simp

  have 2 : "1/((2*b + c + a)^2) \<le> 1/(4*(b + c)*(b + a))"
    using assms(1) assms(2) assms(3)
    using inequality_1
    by simp

  have 3 : "1/((2*c + a + b)^2) \<le> 1/(4*(c + a)*(c + b))"
    using assms(1) assms(2) assms(3)
    using inequality_1
    by simp


  have "(1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 
      1/(4*(a + b)*(a + c)) + 1/(4*(b + c)*(b + a)) + 1/(4*(c + a)*(c + b))"
    using 1 2 3
    by simp
  also have " ... = (b + c)/(4*(a + b)*(a + c)*(b + c)) + (a + c)/(4*(b + c)*(b + a)*(a + c)) + (a + b)/(4*(c + a)*(c + b)*(a + b))"
    using assms(1) assms(2) assms(3)
    by simp
  also have "... = (b + c + c + a + a + b)/(4*(a + b)*(b + c)*(c + a))"
    using assms(1) assms(2) assms(3)
    by (metis (mono_tags, hide_lams) add.commute add.left_commute add_divide_distrib mult.commute mult.left_commute)
  also have "... = (2*(a + b + c))/(4*(a + b)*(b + c)*(c + a))"
    by simp
  also have "... = (2/4)*((a + b + c)/((a + b)*(b + c)*(c + a)))"
    proof -
      have "\<forall>r ra rb. (ra::real) * (rb / r) = rb * ra / r"
        by auto
      then show ?thesis
        by (metis (no_types) divide_divide_eq_left)
    qed
  also have "... = (1/2)*((a + b + c)/((a + b)*(b + c)*(c + a)))"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a))"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * 1"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * (a*b*c) / (a*b*c) "
    using assms(1) assms(2) assms(3)
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * (a*b*c) / (a*b*c) * (a + b + c) / (a + b + c)"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * (a*b*c) / (a*b*c) * (a + b + c) / (a + b + c) * ((a*b + b*c + c*a)^2) / ((a*b + b*c + c*a)^2) "
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos nonzero_mult_div_cancel_right zero_less_power)
  also have "... = (((a + b + c)*(a*b + b*c + c*a))/(2*(a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    by (simp add: power2_eq_square)
  also have  "... = 1/2*(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    by simp
  finally have start : "(1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 
        1/2*(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a+b+c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    by simp


  have 11 : "((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 22 : "(a*b + b*c + c*a)/(a*b*c*(a + b + c)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 33 : "((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff zero_less_power)


  have * : "(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a+b+c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) > 0"
    using assms(1) assms(2) assms(3)
    using 11 22 33
    using zero_less_mult_iff 
    by blast
     
  have ** : "(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) \<le> 3/8"
    using assms(1) assms(2) assms(3) assms(4)
    using LF
    by simp

    
  have finish : "1/2* (((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) \<le>
        1/2 * 3/8"
    using *
    using **
    using inequality_3[of "(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"]
    by auto

  have "(1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 
          1/2*(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    using start
    by simp
  also have "... \<le> 1/2 * 3/8"
    using finish
    by simp
  finally show ?thesis
    by simp
qed


end