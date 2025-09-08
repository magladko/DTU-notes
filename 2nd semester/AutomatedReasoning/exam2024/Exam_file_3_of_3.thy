theory Exam_file_3_of_3 imports Main begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>


text \<open>

Question 1 of 3:

Using the usual operators # for list construction and \<in> for set membership, define a recursive
function eliminate :: \<open>nat set \<Rightarrow> nat list \<Rightarrow> nat list\<close> that returns the list where all elements
that are members of the set have been eliminated (the remaining elements must be in the same order)
and prove \<open>eliminate {2, 4, 6, 8} [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1] = [1, 3, 5, 5, 3, 1]\<close> and
\<open>eliminate A (x @ y) = eliminate A x @ eliminate A y\<close>.

\<close>

fun eliminate :: \<open>nat set \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
"eliminate xset [] = []" |
"eliminate xset (a # ylist) = (if a \<in> xset then (eliminate xset ylist) else (a # (eliminate xset ylist)))"


lemma \<open>eliminate {2, 4, 6, 8} [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1] = [1, 3, 5, 5, 3, 1]\<close>
  by simp

lemma \<open>eliminate A (x @ y) = eliminate A x @ eliminate A y\<close>
proof (induction x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    by auto
qed

text \<open>

Question 2 of 3:

Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

The function smart must not be altered.
\<close>

primrec smart :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>smart p [] = []\<close> |
  \<open>smart p (a # x) = (if p a then a # smart p x else smart p x)\<close>

lemma \<open>smart p l = a # x \<Longrightarrow> \<exists>v w. l = v @ a # w \<and> \<not> (\<exists>a \<in> set v. p a) \<and> p a \<and> x = smart p w\<close>
proof (induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
  proof cases
    assume \<open>p a\<close>
    then show ?thesis
      using Cons by force
  next
    assume \<open>\<not> p a\<close>
    then show ?thesis
      using Cons Cons_eq_appendI set_ConsD smart.simps(2) by metis
  qed
qed

text \<open>

Question 3 of 3:

Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

The function smart must not be altered (it must be the same as in the previous question).

\<close>

lemma \<open>(smart p l = l \<longleftrightarrow> (\<forall>a \<in> set l. p a)) \<and> (smart p l = [] \<longleftrightarrow> (\<forall>a \<in> set l. \<not> p a))\<close>
proof (induct l)
  case Nil
  show ?case
    by simp
next
  case (Cons a l)
  moreover have \<open>length (smart p l) \<le> length l\<close>
    by (induct l) simp_all
  then show ?case
    by (simp add: calculation impossible_Cons)
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
