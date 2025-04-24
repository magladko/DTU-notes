theory Sample_Exam_file_3_of_3 imports Main begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>


text \<open>

Question 1 of 4:

The predefined function sum_list :: \<open>nat list \<Rightarrow> nat\<close> returns the sum of the numbers in a list.

Using the usual operator +, define a recursive function inc_list :: \<open>nat list \<Rightarrow> nat list\<close> that
adds 1 (one) to each number in the list and prove \<open>sum_list (inc_list l) = sum_list l + length l\<close>
(the predefined function length takes a list and returns the length of the list).

\<close>

fun inc_list :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>inc_list [] = []\<close> |
  \<open>inc_list (a # xs) = (a + 1) # inc_list xs\<close>

lemma \<open>sum_list (inc_list l) = sum_list l + length l\<close>
proof (induction l)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a l)
  then show ?case
    by simp
qed


datatype T = Leaf | Node T nat nat nat

fun T_to_nat_list :: \<open>T \<Rightarrow> nat list\<close> where
  \<open>T_to_nat_list Leaf = []\<close> |
  \<open>T_to_nat_list (Node t a b c) = a # b # c # T_to_nat_list t\<close>

text \<open>

Question 2 of 4:

The datatype and function defined above must not be changed.

The function sum_list is explained in Question 1.

Using the usual operator +, define a recursive function T_to_nat :: \<open>T \<Rightarrow> nat\<close> that returns the
sum of the numbers in the term of type T and prove \<open>sum_list (T_to_nat_list t) = T_to_nat t\<close>
(in the definition of T_to_nat it is not allowed to use T_to_nat_list).

\<close>


text \<open>

Question 3 of 4:

Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

The function dummy and the lemma dummy_lemma must not be altered.

\<close>

fun dummy :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>dummy [] = []\<close> |
  \<open>dummy [x] = [x]\<close> |
  \<open>dummy (x # y # xs) = (if x = y then dummy (x # xs) else x # dummy (y # xs))\<close>

lemma dummy_lemma: \<open>x # tl (dummy (x # xs)) = dummy (x # xs)\<close>
  by (induct xs rule: dummy.induct) auto

lemma \<open>dummy (xs @ x # xs') = dummy (xs @ [x]) @ tl (dummy (x # xs'))\<close>
  \<proof>

(*

proof (induct x)
  case 1
  show ?case
    by simp
next
  show ?case
    by (simp add: dummy_lemma)
next
  case 1
  show ?case
    by -
qed

*)


text \<open>

Question 4 of 4:

Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

The function smart must not be altered.

\<close>

fun smart :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>smart [] = []\<close> |
  \<open>smart (x # xs) = smart xs @ [x]\<close>

lemma \<open>smart xs = smart ys \<Longrightarrow> xs = ys\<close>
  \<proof>

(*

proof (induct xs)
  case Nil
  show ?case
    using smart.cases smart.simps snoc_eq_iff_butlast by metis
qed

*)

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
