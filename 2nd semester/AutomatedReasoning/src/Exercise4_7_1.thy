theory Assignment6_3 imports Main begin

(* Excercise 3.5 *)

datatype alpha = a | b | c | d
inductive S:: "alpha list \<Rightarrow> bool" where
s0: "S [] " |
s1: "S w \<Longrightarrow> S (a # w @ [b])" |
s2: "S v \<Longrightarrow> S w \<Longrightarrow> S (v @ w) "

inductive T::"alpha list \<Rightarrow> bool" where
t0: "T [] " |
t1: "T v \<Longrightarrow> T w \<Longrightarrow> T (v @ [a] @ w @ [b])"

(* Excercise 4.7 *)

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 w = S w" |
  "balanced (Suc n) w = balanced n (a # w @ [b])"

theorem balanced_correct: "balanced n w = S (replicate n a @ w @ replicate n b)"
proof (induction n arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have IH: "balanced n (a # w @ [b]) = S (replicate n a @ (a # w @ [b]) @ replicate n b)" by simp
  have "balanced (Suc n) w = balanced n (a # w @ [b])" by simp
  moreover have "... = S (replicate n a @ (a # w @ [b]) @ replicate n b)" using IH by simp
  moreover have "... = S ((replicate n a @ [a]) @ w @ ([b] @ replicate n b))" by simp
  moreover have "... = S (replicate (Suc n) a @ w @ replicate (Suc n) b)"
    by (simp add: replicate_app_Cons_same) 
  ultimately show ?case
    by blast
qed
                                     

end