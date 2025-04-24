theory Assignment_5 imports Main begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

  Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
  such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

\<close>

fun dummy :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>dummy n = (n * Suc n) div 2\<close>

fun smart :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>smart k m = (if k \<ge> m then m else smart (Suc k) (m - Suc k))\<close>

lemma \<open>smart 0 (dummy k + m) = smart k m\<close>
proof (induct k arbitrary: m)
  case 0
  show ?case
    by auto
next
  case (Suc k)
  have \<open>dummy (Suc k) = dummy k + Suc k\<close>
    by simp
  have \<open>smart 0 (dummy k + (Suc k + m)) = smart k (Suc k + m)\<close>
    using Suc .
  have \<open>smart 0 (dummy k + (Suc k + m)) = smart (Suc k) m\<close>
    using Suc
    by (metis diff_add_inverse le_imp_less_Suc not_add_less1 smart.simps)
  then have \<open>smart 0 (dummy k + Suc k + m) = smart (Suc k) m\<close>
    using add.assoc by metis
  with \<open>dummy (Suc k) = dummy k + Suc k\<close> show ?case
    by metis
qed


text \<open>

  Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
  such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

\<close>

lemma \<open>\<exists>a \<in> set x. p a \<Longrightarrow> \<exists>a y z. p a \<and> x = y @ a # z \<and> \<not> (\<exists>a \<in> set y. p a)\<close>
proof (induct x)
  case Nil
  then show ?case
    by auto
next
  case (Cons a x)
  then show ?case
  proof cases
    assume \<open>p a\<close>
    then have \<open>p a \<and> a # x = a # x \<and> \<not> (\<exists>a \<in> set []. p a)\<close>
      by simp
    then show ?thesis
      by blast
  next
    assume \<open>\<not> p a\<close>
    then show ?thesis
      using Cons append_Cons set_ConsD by metis
  qed
qed

text \<open>

  Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
  such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

\<close>

lemma \<open>map f x = map g y \<longrightarrow> length x = length y\<close>
proof
  assume \<open>map f x = map g y\<close>
  then show \<open>length x = length y\<close>
  proof (induct y arbitrary: x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a y)
    then obtain a' x' where *: \<open>x = a' # x'\<close>
      by auto
    with Cons have \<open>map f x' = map g y\<close>
      by simp
    with Cons have \<open>length x' = length y\<close>
      by simp
    with Cons show ?case
      by (simp add: "*")
  qed
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
