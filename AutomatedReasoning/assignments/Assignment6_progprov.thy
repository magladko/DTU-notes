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
"balanced 0 [] = True" |
"balanced n (a # w) = balanced (n+1) w" |
"balanced (Suc n) (b # w) = balanced (n) w" |
"balanced n w = False"


lemma BSrep: "balanced n w \<Longrightarrow> S (replicate n a @ w)"
proof (induct n w rule: balanced.induct)
  case 1
  then show ?case
    using S_empty by auto
next
  case (2 n w)
  then show ?case
    by (simp add: replicate_app_Cons_same)
next
  case (3 n w)
  then show ?case sorry
next
  case ("4_1" v)
  then show ?case sorry
next
  case ("4_2" va)
  then show ?case sorry
qed

(*balanced used like S and reversed*)
(*insert a,b into a balanced word \<rightarrow> balanced word*)
(* a#w@[b] = u@v \<rightarrow> if u is not empty, then starts with a; if v is not empty it ends with b*)
(* w@w' = u@v \<rightarrow> split before/after *)

lemma SrepB: "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induct \<open>replicate n a @ w\<close> arbitrary: n w rule: balanced.induct)
  case 1
  then show ?case by simp
next
  case (2 n w)
  then show ?case sorry
next
  case (3 n w)
  then show ?case sorry
next
  case ("4_1" v)
  then show ?case sorry
next
  case ("4_2" va)
  then show ?case sorry
qed

lemma "balanced n w = S (replicate n a @ w)"
proof -
  show ?thesis using SrepB BSrep
    by blast
qed

end