theory Exam_file_2_of_3 imports Pure_HOL begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Replace the "oops" with a full proof using Isabelle/Isar and Pure_HOL (do not use MiniCalc).

\<close>

proposition \<open>p \<longrightarrow> \<not> (p \<and> \<not> q) \<longrightarrow> q\<close>
proof
  assume \<open>p\<close>
  show \<open>\<not> (p \<and> \<not> q) \<longrightarrow> q\<close>
  proof
    assume \<open>\<not> (p \<and> \<not> q)\<close>
    show \<open>q\<close>
    proof (rule ccontr)
      assume \<open>\<not> q\<close>
      from \<open>p\<close> and this have \<open>p \<and> \<not> q\<close> ..
      from \<open>\<not> (p \<and> \<not> q)\<close> and \<open>p \<and> \<not> q\<close>  show \<open>\<bottom>\<close> ..
    qed
  qed
qed

proposition \<open>(\<forall>x. p x \<and> q x) \<longrightarrow> (\<exists>x. q x \<or> r x)\<close>
proof
  assume *: \<open>\<forall>x. p x \<and> q x\<close>
  show \<open>\<exists>x. q x \<or> r x\<close>
  proof
    fix c
    show \<open>q c \<or> r c\<close>
    proof (rule Dis_I1)
      from * have \<open>p c \<and> q c\<close> ..
      then show \<open>q c\<close> ..
    qed
  qed
qed

proposition \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
proof -
  have \<open>q \<or> \<not> q\<close> by (rule LEM)
  then show \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
  proof
    assume \<open>q\<close>
    show \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
    proof (rule Dis_I1)
      show \<open>p (f a b c) \<longrightarrow> q\<close>
      proof
        assume \<open>p (f a b c)\<close>
        from \<open>q\<close> show \<open>q\<close> .
      qed
    qed
  next
    assume \<open>\<not> q\<close>
    show \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
    proof
      show \<open>q \<longrightarrow> (\<exists>x. \<forall>y. r x y)\<close>
      proof
        assume \<open>q\<close>
        from \<open>\<not> q\<close> and this have \<open>\<bottom>\<close> ..
        then show \<open>\<exists>x. \<forall>y. r x y\<close> ..
      qed
    qed
  qed
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
 