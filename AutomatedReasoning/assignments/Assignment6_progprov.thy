theory Assignment6_progprov imports Main begin

section \<open>3.5\<close>

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S_empty: "S []" |
S_wrap: "S w \<Longrightarrow> S (a # w @ [b])" |
S_con: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_empty: "T []" |
T_case: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ [a] @ w2 @ [b])"

lemma T_S: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(rule S.S_empty)
  by (simp add: S_con S_wrap)

lemma t_con: "T w2 \<Longrightarrow> T w1 \<Longrightarrow> T (w1 @ w2)"
  apply(induction w2 arbitrary: w1 rule: T.induct)
   apply simp_all
  by (metis T_case append.left_neutral append_Cons append_assoc)

lemma S_T: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
    apply(rule T.T_empty)
  using T_case T_empty apply fastforce
  apply(rule t_con)
  apply blast
  by blast

lemma "S w = T w"
  using S_T T_S by blast

section \<open>4.7\<close>

(* define recursive fn - check
induction on assumption
 *)
fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0 [] = False"


lemma "balanced n w = S (replicate n a @ w )"
  sorry


end