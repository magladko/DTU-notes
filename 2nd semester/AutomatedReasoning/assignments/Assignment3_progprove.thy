theory Assignment3_progprove imports Main begin

section \<open>Exercise 2.10\<close>

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 0" |
  "nodes (Node l r) = (Suc (nodes l) + (nodes r))"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

theorem explode_size: "nodes (explode n t) = 2^n * ((nodes t) + 1) - 1"
  apply(induction n arbitrary: t)
  apply(simp)
  by (simp add: algebra_simps)

section \<open>Exercise 2.11\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x" |
  "eval (Const a) x = a" |
  "eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
  "eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] x = 0" |
  "evalp (a # xs) x = a + x * evalp xs x"

fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addp xs [] = xs" |
  "addp [] ys = ys" |
  "addp (x # xs) (y # ys) = (x + y) # (addp xs ys)"

fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"multp [] _ = []" |
"multp (x # xs) ys = addp (map (\<lambda>y. x * y) ys) (0 # multp xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where

  "coeffs (Const c) = [c]" |
  "coeffs Var = [0, 1]" |
  "coeffs (Add e1 e2) = addp (coeffs e1) (coeffs e2)" |
  "coeffs (Mult e1 e2) = multp (coeffs e1) (coeffs e2)"

lemma add_evalp: "evalp (addp xs ys) x = evalp xs x + evalp ys x"
  apply(induction ys arbitrary: xs)
   apply simp
  apply(case_tac xs)
   apply simp_all
  by (simp add: algebra_simps)

lemma evalp_map_mult: "evalp (map (\<lambda>y. a * y) ys) x = a * evalp ys x"
  apply(induction ys)
   apply simp_all
  by (simp add: algebra_simps)

lemma mult_evalp: "evalp (multp xs ys) x = evalp xs x * evalp ys x"  
  apply(induction xs)
   apply simp_all
  apply(subst add_evalp)
  apply simp
  apply(subst evalp_map_mult)
  by (simp add: algebra_simps)

theorem coeffs_preserve: "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
     apply(auto)
  using add_evalp
   apply presburger
  using mult_evalp
  by simp

section \<open>Exercise 3.3\<close>

inductive star :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow>'a \<Rightarrow>'a \<Rightarrow> bool" for r where 
refl: "star r x x" | 
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl': "star' r x x" | 
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(assumption)
  apply(metis step)
  done

theorem star1: "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(rule refl)
  using refl step star_trans
  by meson

lemma l1_star2: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  using refl' step'
   apply meson
  using refl' step'
  by meson

theorem star2: "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(rule refl')
  using l1_star2
  by meson

section \<open>Exercise 3.4\<close>

inductive iter :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl_i: "iter r n x x" |
step_i: "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (Suc n) x z"

lemma l1_star_iter: "iter r n y z \<Longrightarrow> r x y \<Longrightarrow> \<exists>n. iter r n x z"
  apply(induction rule: iter.induct)
  using refl_i step_i
   apply meson
  using refl_i step_i
  by meson

theorem star_iter: "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply(induction rule: star.induct)
  using refl_i step_i
   apply meson
  using l1_star_iter
  by meson

end