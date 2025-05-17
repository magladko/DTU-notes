theory Prog_Prove_Solutions_2 imports Main begin

section \<open>Exercise 4.1\<close>

lemma assumes T: \<open>\<forall>x y. T x y \<or> T y x\<close>
  and A: \<open>\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y\<close>
  and TA: \<open>\<forall>x y. T x y \<longrightarrow> A x y\<close>
  and \<open>A x y\<close>
shows \<open>T x y\<close>
proof (rule ccontr)
  assume *: \<open>\<not> T x y\<close>
  with T have \<open>T y x\<close>
    by blast
  with TA have \<open>A y x\<close>
    by blast
  with A assms(4) have \<open>x = y\<close>
    by blast
  with \<open>T y x\<close> have \<open>T x y\<close>
    by blast
  with * show False
    ..
qed

section \<open>Exercise 4.2\<close>

lemma \<open>\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)\<close>
proof -
  let ?k = \<open>(length xs + 1) div 2\<close>
  have \<open>?k = length (take ?k xs) \<and> (?k = length (drop ?k xs) \<or> ?k = length (drop ?k xs) + 1)\<close>
    by force
  with append_take_drop_id show ?thesis
    by metis
qed

section \<open>Exercise 4.6\<close>

fun elems :: \<open>'a list \<Rightarrow> 'a set\<close> where
  \<open>elems [] = {}\<close> |
  \<open>elems (x # xs) = {x} \<union> elems xs\<close>

lemma \<open>x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys\<close>
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  show ?case
  proof (cases \<open>a = x\<close>)
    case True
    then show ?thesis
      by force
  next
    case False
    then show ?thesis
      using Cons Cons_eq_appendI by force
  qed
qed

end
