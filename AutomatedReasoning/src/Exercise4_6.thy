theory Exercise4_6 imports Main begin

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (a # xs) = {a} \<union> (elems xs)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  then show ?case
qed

  (*sorry*)

end