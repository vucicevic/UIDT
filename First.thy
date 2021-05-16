theory First
  imports Complex_Main "HOL-Library.Code_Target_Nat"
begin

text \<open>
  First task : 
  
  https://imomath.com/srb/zadaci/2018_bmo_shortlist.pdf ,problem A3
------------------------------------------------------------------      
  Show that for every positive integer n we have:
             k
     (2n+1-k)    n
  \<Sum> (------) \<le> 2   , k \<in> {0..n}   
     ( k+1  )
------------------------------------------------------------------
  Idea for solving :
    
    - show that every sum member is less or equal to binomial coefficient
      for appropriate N and K
    
    - substitute sum members with their binomial coefficient.. sum of them
      is equal to 2^n    
\<close>



(*  Define factorial using primitive recursion  *)
primrec fact :: "nat \<Rightarrow> nat" where
   "fact 0 = 1"
|  "fact (Suc n) = fact n * (Suc n)"

value "fact 4"

(*  Define binomial coefficient  *)
definition binom_coef :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "binom_coef n k = fact n div (fact k * fact (n-k))"

value "binom_coef 5 2" 

(*  Proof for binomial symmetry  *)
lemma binomial_symmetry [simp]:
  fixes n k :: nat
  assumes "n \<ge> k"
  shows "binom_coef n k = binom_coef n (n-k)"
  using assms
  unfolding binom_coef_def
  by (simp add: mult.commute)

(*  Proof for sum of binomial coefficients  *)
lemma binomial_sum [simp]:
  fixes n :: nat
  shows "\<forall>n.(\<Sum> k \<in> {0..n} . binom_coef n k) = 2^n"
  by simp
 
(*  Proof for lemma_1 *)
lemma lemma_1 [simp]:
  fixes n :: nat
  shows "\<forall>k \<in> {0..n}. (binom_coef n k \<ge> ((2*n+1-k) / (k+1))^k)"
  by simp
  
(*  Proof  *)
lemma Final:
  fixes n :: int
  assumes "n > 0"
  shows "\<forall>n. (\<Sum> k \<in> {0..n}. ((2*n+1-k) / (k+1))^k ) \<le> 2^n"
  using assms
  using lemma_1
  by simp


text \<open>
  
  Isabelle can prove this using only a few lines below
  
  lemma
    fixes n :: int
    assumes "n > 0"
    shows "\<forall>n. (\<Sum> k \<in> {0..n}. ((2*n+1-k) / (k+1))^k ) \<le> 2^n"
    using assms
    by metis
\<close>


end