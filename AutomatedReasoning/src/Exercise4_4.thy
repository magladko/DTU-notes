theory Exercise4_4 imports Main begin

inductive ev :: "nat \<Rightarrow> bool" where 
ev0: "ev 0" | 
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

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

end