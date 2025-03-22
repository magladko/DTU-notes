theory Assignment4_progprove imports Main begin

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

lemma t_con: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ w2)"
  (*apply(induction rule: T.induct)*)
  apply(induction w1 arbitrary: w2 rule: T.induct)
   apply simp_all
  
  sorry

lemma S_T: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
    apply(rule T.T_empty)
  using T_case T_empty apply fastforce
  apply(rule t_con)
  apply blast
  by blast

lemma "S w = T w"
  using S_T T_S by blast

end