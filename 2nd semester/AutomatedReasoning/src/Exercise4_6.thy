theory Exercise4_6 imports Main begin

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (a # xs) = {a} \<union> (elems xs)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  show ?case
  proof (cases \<open>x = a\<close>)
    case True
    then show ?thesis
      by fastforce
  next
    case False
    then show ?thesis
      by (metis (no_types, opaque_lifting) Cons.IH Cons.prems Cons_eq_append_conv Un_iff elems.simps(2)
          singletonD)
  qed
qed


end