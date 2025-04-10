theory Exam_file_2_of_3 imports Pure_HOL begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Replace the "oops" with a full proof using Isabelle/Isar and Pure_HOL (do not use MiniCalc).

\<close>

proposition \<open>p \<longrightarrow> \<not> (p \<and> \<not> q) \<longrightarrow> q\<close>
  oops

proposition \<open>(\<forall>x. p x \<and> q x) \<longrightarrow> (\<exists>x. q x \<or> r x)\<close>
  oops

proposition \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
  oops

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
