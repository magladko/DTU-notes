theory Assignment_5_progprov imports Main begin

section \<open>4.3\<close>

inductive ev :: "nat \<Rightarrow> bool" where 
ev0: "ev 0" | 
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

lemma assumes a: "ev (Suc(Suc n))" shows "ev n"
  using assms 
proof cases
  case evSS
  then show ?thesis .
qed
(*by cases <- also only with this*)

section \<open>4.4\<close>

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume \<open>ev (Suc (Suc (Suc 0)))\<close>
  then show False
  proof cases
    case evSS
    then show False
      by cases
  qed
qed

(* also works, but first is better
lemma assumes a: "ev n" shows "\<not> ev (Suc (Suc (Suc 0)))"
  using assms
proof cases
  case ev0
  then show ?thesis
    by (metis Suc_inject Suc_neq_Zero ev.simps)
next
  case (evSS n)
  then show ?thesis
    by (metis Zero_neq_Suc ev.cases nat.inject)
qed
*)

section \<open>4.5\<close>

inductive star :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow>'a \<Rightarrow>'a \<Rightarrow> bool" for r where 
refl: "star r x x" | 
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl_i: "iter r n x x" |
step_i: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma assumes a: "iter r n x y" shows "star r x y"
  using assms
proof (induct n x y rule: iter.induct)
  case (refl_i n x)
  then show ?case by (rule refl)
next
  case (step_i n x y z)
  show ?case using step_i(1, 3) by (rule step)
qed

end