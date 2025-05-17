theory Exam_file_2_of_3 imports Pure_HOL begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Replace the "oops" with a full proof using Isabelle/Isar and Pure_HOL (do not use MiniCalc).

\<close>

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> (\<not> p \<longrightarrow> q) \<longrightarrow> q\<close>
proof
  assume \<open>p \<longrightarrow> q\<close>
  show \<open>(\<not> p \<longrightarrow> q) \<longrightarrow> q\<close>
  proof
    assume \<open>\<not> p \<longrightarrow> q\<close>
    have \<open>p \<or> \<not> p\<close> by (rule LEM)
    then show \<open>q\<close>
    proof
        assume \<open>p\<close>
        from \<open>p \<longrightarrow> q\<close> and this show \<open>q\<close> ..
      next 
        assume \<open>\<not> p\<close>
        from \<open>\<not> p \<longrightarrow> q\<close> and this show \<open>q\<close> ..
      qed
  qed
qed

proposition \<open>(\<forall>x. p x) \<and> q a \<longrightarrow> p a \<and> (\<exists>x. q x)\<close>
proof
  assume *: \<open>(\<forall>x. p x) \<and> q a\<close>
  then have \<open>q a\<close> ..
  from * have \<open>\<forall>x. p x\<close> ..
  then have \<open>p a\<close> ..
  show \<open>p a \<and> (\<exists>x. q x)\<close>
  proof
    from \<open>p a\<close> show \<open>p a\<close> .
  next
    from \<open>q a\<close> show \<open>\<exists>x. q x\<close> ..
  qed
qed

proposition \<open>(\<exists>x. \<forall>y. p x y) \<longrightarrow> (\<exists>x. p x a \<or> q a x)\<close>
proof
  assume \<open>\<exists>x. \<forall>y. p x y\<close>
  from \<open>\<exists>x. \<forall>y. p x y\<close> obtain c where \<open>\<forall>y. p c y\<close> ..
  show \<open>\<exists>x. p x a \<or> q a x\<close>
  proof
    show \<open>p c a \<or> q a c\<close>
    proof (rule Dis_I1)
      from \<open>\<forall>y. p c y\<close> show \<open>p c a\<close> ..
    qed
  qed
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
