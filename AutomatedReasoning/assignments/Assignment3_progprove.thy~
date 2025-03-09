theory Assignment3_progprove imports Main begin

(* Exercise 2.10 *)

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

(* Exercise 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const a) x = a" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp_rev :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp_rev [] x = 0" |
"evalp_rev (a # xs) x = a * (x ^ (length xs)) + evalp_rev xs x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp xs x = evalp_rev (rev xs) x"

(* fun simplify :: "exp \<Rightarrow> exp" where *)
(* "simplify Var = Var" | *)
(* "simplify (Const a) = Const a" | *)
(* "simplify (Const a) = Const a" | *)

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = []" |
"coeffs (Const a) = [a]" |
(* "coeffs (Add (Const a) (Const b)) = coeffs (Const (a + b))" | *)
"coeffs (Add e1 e2) = []" |
(* "coeffs (Mult (Const a) (Const b)) = coeffs (Const (a * b))" | *)
"coeffs (Mult e1 e2) = []"

theorem coeffs_preserve: "evalp (coeffs e) x = eval e x"
  oops

(* Exercise 3.3 *)

(* Exercise 3.4 *)

end