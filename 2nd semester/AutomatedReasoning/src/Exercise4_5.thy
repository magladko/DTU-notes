theory Exercise4_5 imports Main begin

inductive star :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow>'a \<Rightarrow>'a \<Rightarrow> bool" for r where 
refl: "star r x x" | 
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow>'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl_i: "iter r n x x" |
step_i: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"
(*Changed from the following for easier proof:*)
(*step_i: "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (Suc n) x z"*)

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