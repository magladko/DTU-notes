theory Sample_Exam_file_1_of_3 imports MiniCalc begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Use MiniCalc to prove the following formulas and include all "Copy Result to Clipboard" lines.

\<close>

proposition \<open>(p \<longrightarrow> \<not> p) \<longrightarrow> \<not> p\<close>
  oops

proposition \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close>
  oops

proposition \<open>\<not> (\<exists>x. p (f x)) \<longrightarrow> (\<forall>x. \<not> p (f x))\<close>
  oops

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
