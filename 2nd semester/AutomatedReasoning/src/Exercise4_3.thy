theory Exercise4_3 imports Main begin

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

end