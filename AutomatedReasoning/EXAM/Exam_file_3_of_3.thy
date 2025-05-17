theory Exam_file_3_of_3 imports Main begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>


text \<open>

Question 1 of 4:

Using only the constructors 0 and Suc and no arithmetical operators, define a recursive function
triple :: \<open>nat \<Rightarrow> nat\<close> and prove \<open>triple n = 3 * n\<close>.

\<close>

fun triple :: \<open>nat \<Rightarrow> nat\<close> where
"triple 0 = 0" |
"triple (Suc n) = (Suc (Suc (Suc (triple n))))"

lemma \<open>triple n = 3 * n\<close>
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case by simp
qed

text \<open>

Question 2 of 4:

Using the usual operators + and -, define two recursive functions add65536 :: \<open>int list \<Rightarrow> int list\<close>
and sub65536 :: \<open>int list \<Rightarrow> int list\<close> that adds 65536 to each integer and subtracts 65536 from each
integer, respectively, and prove \<open>sub65536 (add65536 xs) = xs \<and> add65536 (sub65536 xs) = xs\<close>.

\<close>

fun add65536 :: \<open>int list \<Rightarrow> int list\<close> where
"add65536 [] = []" |
"add65536 (x # xs) = [x + 65536] @ (add65536 xs)"

fun sub65536 :: \<open>int list \<Rightarrow> int list\<close> where
"sub65536 [] = []" |
"sub65536 (x # xs) = [x - 65536] @ (sub65536 xs)"

lemma \<open>sub65536 (add65536 xs) = xs \<and> add65536 (sub65536 xs) = xs\<close>
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed


text \<open>

Question 3 of 4:

Using the usual operators # for list construction and \<in> for set membership, define a recursive
function eliminate :: \<open>nat set \<Rightarrow> nat list \<Rightarrow> nat list\<close> that returns the list where all elements
that are not members of the set have been eliminated (the remaining elements must be in the same
order) and prove \<open>eliminate {1, 3, 5} [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1] = [1, 3, 5, 5, 3, 1]\<close> and
\<open>eliminate A (x @ y) = eliminate A x @ eliminate A y\<close>.

\<close>

fun eliminate :: \<open>nat set \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
"eliminate xset [] = []" |
"eliminate xset (a # ylist) = (if a \<in> xset 
                               then (a # (eliminate xset ylist)) 
                               else (eliminate xset ylist))"

lemma \<open>eliminate {1, 3, 5} [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1] = [1, 3, 5, 5, 3, 1]\<close>
  by simp

lemma \<open>eliminate A (x @ y) = eliminate A x @ eliminate A y\<close>
proof (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case by auto
qed

text \<open>

Question 4 of 4:

Replace \<proof> with the "proof ... qed" lines in the following comment and correct the errors
such that the structured proof is a proper proof in Isabelle/HOL (do not alter the lemma text).

The function smart must not be altered.

\<close>

definition smart :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> bool\<close> where \<open>smart n l = (length l + 41 > n + 42)\<close>

lemma \<open>smart n l = (\<exists>x xs. l = x # xs \<and> n < length xs)\<close>
proof
  have *: \<open>smart n l = ((Suc n) < length l)\<close>
    by (simp add: smart_def)
  then show \<open>smart n l \<Longrightarrow> \<exists>x xs. l = x # xs \<and> n < length xs\<close>
    using Suc_le_length_iff less_eq_Suc_le
    by auto
  from * show \<open>\<exists>x xs. l = x # xs \<and> n < length xs \<Longrightarrow> smart n l\<close> by auto
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
