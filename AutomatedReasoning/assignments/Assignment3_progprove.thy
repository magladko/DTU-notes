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

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] x = 0" |
  "evalp (a # xs) x = a + x * evalp xs x"

fun deriv :: "exp \<Rightarrow> exp" where
  "deriv (Const _) = Const 0" |
  "deriv Var = Const 1" |
  "deriv (Add e1 e2) = Add (deriv e1) (deriv e2)" | (* (f+g)' = f' + g' *)
  "deriv (Mult e1 e2) = Add (Mult (deriv e1) e2) (Mult e1 (deriv e2))" (* (f*g)' = f'*g + f*g' *)

fun is_zero :: "exp \<Rightarrow> bool" where
  "is_zero (Const r) = (r = 0)" |
  "is_zero Var = False" |
  "is_zero (Add e1 e2) = (is_zero e1 \<and> is_zero e2)" |
  "is_zero (Mult e1 e2) = (is_zero e1 \<or> is_zero e2)"

fun degree :: "exp \<Rightarrow> nat" where
  "degree (Const _) = 0" |
  "degree Var = 1" |
  "degree (Add e1 e2) = max (degree e1) (degree e2)" |
  "degree (Mult e1 e2) = (if is_zero e1 \<or> is_zero e2 then 0 else degree e1 + degree e2)"

(* (expression, degree, counter) \<Rightarrow> coefficient list *)
fun coeffs_rec :: "exp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list" where
  "coeffs_rec e 0 f = [(eval e 0) div fact f]" |
  "coeffs_rec e d f = ((eval e 0) div (fact f)) # (coeffs_rec (deriv e) (d-1) (Suc f))"

fun coeffs :: "exp \<Rightarrow> int list" where
  (*"coeffs e = map (\<lambda>i. (eval (iterate i deriv e) 0 div (fact i))) [0..<Suc (degree e)]"*)
  "coeffs e = coeffs_rec e (degree e) 0"

(* test *)
value "coeffs (Add (Const 2)
       (Add (Mult (Const 2) Var) 
            (Add (Mult (Const 0) (Mult Var Var)) 
                 ((Mult (Const 0) (Mult (Mult Var Var) Var))))))"
value "coeffs (Mult (Add (Mult Var (Const 2)) (Const 1)) (Const 2))"

lemma exp_is_zero [simp]: "is_zero e \<Longrightarrow> eval e x = 0"
  apply(induction e arbitrary: x)
  by auto

lemma sum: "evalp (coeffs_rec (Add e1 e2) (max (degree e1) (degree e2)) 0) x = 
            evalp (coeffs_rec e1 (degree e1) 0) x + evalp (coeffs_rec e2 (degree e2) 0) x"
  apply(induction e1 arbitrary: x e2)
     (*apply(induction e2 arbitrary: x)*)
     (*apply(induction e2)*)
  apply(simp_all)
     (*apply(auto)*)
  oops

theorem coeffs_preserve: "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
  (*apply(simp_all)*)
  (*apply(induction e rule: coeffs.induct)*)
     apply(auto)
  oops

(* Exercise 3.3 *)

inductive star :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow>'a \<Rightarrow>'a \<Rightarrow> bool" for r where 
refl: "star r x x" | 
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl': "star' r x x" | 
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(assumption)
  by(metis step)

(*
\<And>x y za.       r x y \<Longrightarrow>  star  r y za                   \<Longrightarrow> (star  r za z  \<Longrightarrow> star r y z) \<Longrightarrow> star  r za z \<Longrightarrow> star  r x z
\<And>x y za. star' r x y \<Longrightarrow> (star' r y z  \<Longrightarrow>  star' r x z) \<Longrightarrow>        r y  za                 \<Longrightarrow> star' r za z \<Longrightarrow> star' r x z
*)

lemma star'_trans: "star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(assumption)
  
  (*apply(auto)*)

  oops
  (*by(metis step)*)

theorem star1: "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
  oops

theorem star2: "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
  oops

(* Exercise 3.4 *)

end