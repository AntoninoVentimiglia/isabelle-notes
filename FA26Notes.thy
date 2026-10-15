theory FA26Notes
  imports
    "HOL-Computational_Algebra.Polynomial_Factorial"
begin
section "Lecture 1: Basics"
  (*
Comments.
Value commands - allows you to evaluate an expression
Everything in Isabelle has a type
*)

value "1::nat" (* natural *)
value "1::int" (* integer *)
value "1::rat" (* rational *)
value "1::real" (* real *)
value "(1::nat) + 2"
value "(6::rat) / 2" \<comment> \<open>type inference\<close>
value "[1::nat, 2, 3]"
value "[1, 2, 3, 4, 5]::rat list"
value "drop 2 [1::nat, 2, 3, 4, 5]" \<comment> \<open>suffix\<close>
value "take 3 [1::nat, 2, 3, 4, 5]" \<comment> \<open>prefix\<close>
value "[1::nat, 2, 3, 4, 5] ! 0"
value "[1::nat, 2, 3, 4, 5] ! 3"
value "rev [1::nat, 2, 3, 4, 5]"
value "3 # [1, 2, 3::nat]"
value "Cons 3 [1, 2, 3::nat]"
value "[3, 2, 1] @ [1, 2, 3::nat]"

(* value "sqrt (4::real)" cannot be solved *)
lemma sqrt4: "sqrt (4::real) = 2"
  (*try0*) (*get rid of try0 once you find a proof*)
  by simp  (*THIS IS THE PROOF*)
    (* if a natural number x is greater than 1, then x^2 is greater than x *)
lemma x_squared_greater_than_itself:
  fixes x::"nat"
  assumes "x > 1"
  shows "x^2 > x"
    (* try0 cannot find a proof *)
    (* sledgehammer *)
  by (metis assms one_less_numeral_iff power_one_right
      power_strict_increasing_iff semiring_norm(76))
lemma numerical_inequality:
  shows "sqrt 2 + sqrt 18 < sqrt 40"
proof-
  have lhs: "(sqrt 2 + sqrt 18)^2 = 32" (*sledgehammer can't solve it*)
  proof-
    have foil: "(sqrt 2 + sqrt 18)^2 = 20 + 2(sqrt 2)(sqrt 18)"
      by (simp add: power2_sum)
    have sqrts: "(sqrt 2)(sqrt 18) = sqrt 36"
      by (metis real_sqrt_mult numeral_Bit0_eq_double)
    have sqrt_36: "sqrt 36 = 6"
      by simp
    have simplify: "20 + 2((sqrt 2)(sqrt 18)) = 32"
      unfolding sqrts sqrt_36
      by simp
    show ?thesis
      using foil simplify
      by simp
  qed
  have rhs: "(sqrt 40)^2 = 40"
    by simp
  have sg: "(sqrt 2 + sqrt 18)^2 < (sqrt 40)^2" (*state a subgoal*)
    unfolding lhs rhs
    by simp
  show ?thesis
    using sg
    by (metis sg real_less_rsqrt power2_eq_square real_sqrt_mult_self abs_numeral)
qed
(* proof sketch
suffices: 20 + 12 < 40 yes
suffices: 20 + 2(sqrt 2)(sqrt 18) < 40
suffices: (sqrt 2 + sqrt 18)^2 < (sqrt 40)^2
want to show: sqrt 2 + sqrt 18 < sqrt 40
*)
lemma rational_algebra:
  fixes x::"real"
  assumes "x \<noteq> 1 \<and> x \<noteq> -1" 
  shows "1/(1-x) + 1/(1+x) = 2/(1-x^2)"
proof-
(* proof sketch
1/(1-x) = (1+x)/((1-x)(1+x)) = (1+x)/(1-x^2)
1/(1+x) = (1-x)/((1-x)(1+x)) = (1-x)/(1-x^2)
sum: (1+x)/(1-x^2) + (1-x)/(1-x^2) = 2/(1-x^2)
*)
  have diff_sq: "(1-x)*(1+x) = 1-x^2"
    by algebra
  have "1/(1-x) = (1+x)/((1-x)*(1+x))"
    using assms by auto
  (*continue here *)
  have sum1: "1/(1-x) = (1+x)/(1-x^2)"
    sorry
  have sum2: "1/(1+x) = (1-x)/(1-x^2)"
    sorry
  show ?thesis
    unfolding sum1 sum2 by algebra
qed

\<comment> \<open>convince yourself that something is right before you try to convince Isabelle\<close>

section "Lecture 2"

lemma case_splitting_example:
  fixes x y::"real"
  assumes xy: "x * y = 1"
  shows "x + y \<noteq> 0"
proof-
(* Proof sketch 
  3 exhaustive cases 
  - x > 0
    so y > 0 as well, since + * + = +
    so x + y > 0
    so x + y \<noteq> 0
  - x = 0
    impossible 
    contradiction
    prove false (false \<Rightarrow> anything) is always true
    from false prove anything, including original statement
  - x < 0
    so y < 0 as well, since - * - = +
    so x + y < 0
    so x + y \<noteq> 0
*)
  {
    assume x_pos: "x > 0" (* if x > 0 *)
    have y_pos: "y > 0"
      using xy x_pos
      by (metis zero_less_mult_pos zero_less_one)
    have sum_pos: "x + y > 0"
      using x_pos y_pos
      by simp
    then have ?thesis (* same as "have ?thesis using sum_pos" *)
      by fastforce
    } moreover { 
      assume x_zero: "x = 0" (* else if x = 0 *)
      have "False" \<comment> \<open>contradiction\<close>
        using x_zero xy by fastforce
      have ?thesis
        using x_zero xy by force
    } moreover {
      assume x_neg: "x < 0" (* else if x < 0 *)
      have y_neg: "y < 0"
        using xy x_neg 
        by (metis not_less_iff_gr_or_eq zero_less_mult_iff zero_less_one)
      have sum_neg: "x + y < 0"
        using x_neg y_neg
        by argo
      then have ?thesis
        by force
    }
    ultimately show ?thesis
      by linarith
qed

(* definitions and functions *)

definition append_list::"'a list \<Rightarrow> 'a list" (* 'a = arbitrary type *)
  where "append_list L = L @ L"

value "append_list [0::nat, 1, 2]" (* 'a = nat *)
value "append_list [0::int, 1, 2]" (* 'a = int *)
value "append_list [0::rat, 1, 2]" (* 'a = rat *)

definition append_three_times::"'a list \<Rightarrow> 'a list"
  where "append_three_times L = (L @ L) @ L"

value "append_three_times [0::nat, 1, 2]"
value "append_three_times [0::int, 1, 2]"
value "append_three_times [0::rat, 1, 2]"

value "length [0::nat, 1, 2, 3, 4]"

lemma length_append_three_times:
  fixes L::"'a list"
  shows "length (append_three_times L) = 3 * length L"
proof-
  show ?thesis
    unfolding append_three_times_def (*access a definition with *_def *)
    by force
qed

(*functions*)

fun list_add_one::"nat list \<Rightarrow> nat list" where
  "list_add_one [] = []"
|  "list_add_one (head # Tail) = (head+1) # (list_add_one Tail)"

(*
list_add_one [1,2,3]
= list_add_one(1 # [2,3])
= (1+1) # (list_add_one [2,3])
= (1+1) # (list_add_one 2 # [3])
= (2) # ((2+1) # (list_add_one [3]))
= (2) # ((2+1) # (list_add_one 3 # []))
= (2) # (3 # ((3+1) # (list_add_one [])) 
= 2 # (3 # (4 # []))
= [2,3,4]
*)

value "list_add_one [1,2,3]"

fun list_add_one_map::"nat list \<Rightarrow> nat list" where
  "list_add_one_map L = map (\<lambda>x. x + 1) L" (*\lambda*) (*(\<lambda>x. x + 1) = add one to any input x*)

(* map f L applies the function f to ALL elements of L*)

value "list_add_one_map [1,2,3]"
value "list_add_one_map [2,3,4]"

lemma same_functions:
  fixes L::"nat list"
  shows "list_add_one L = list_add_one_map L"
proof(induct L)
  case Nil (* base case with L = []*)
  then show ?case 
    by simp
next
  case (Cons h T) (* inductive case with L = head # Tail *)
  then show ?case 
    by force
qed


end