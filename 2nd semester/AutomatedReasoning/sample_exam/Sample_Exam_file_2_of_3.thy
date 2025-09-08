theory Sample_Exam_file_2_of_3 imports Pure_HOL begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Replace the "oops" with a full proof using Isabelle/Isar and Pure_HOL (do not use MiniCalc).

\<close>

proposition \<open>(p \<longrightarrow> \<not> p) \<longrightarrow> \<not> p\<close>
proof
  assume \<open>p \<longrightarrow> \<not> p\<close>
  show \<open>\<not> p\<close>
  proof
    assume \<open>p\<close>
    from \<open>p \<longrightarrow> \<not> p\<close> and \<open>p\<close> have \<open>\<not> p\<close> ..
    from \<open>\<not>p\<close> and \<open>p\<close> show \<open>\<bottom>\<close> ..
  qed
qed

(*1st version*)
proposition \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close>
proof -
  have \<open>(\<forall>x. p x) \<or> \<not>(\<forall>x. p x)\<close> by (rule LEM)
  then show \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close>
  proof
    assume \<open>\<forall>x. p x\<close>
    then have \<open>p a \<longrightarrow> (\<forall>x. p x)\<close> for a by (rule Imp_I)
    then show \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close> ..
  next 
    assume \<open>\<not>(\<forall>x. p x)\<close>
    have \<open>\<exists>x. \<not> p x\<close>
    proof (rule ccontr)
      assume \<open>\<not> (\<exists>x. \<not> p x)\<close>
      have \<open>\<forall>x. p x\<close>
      proof
        fix x
        show \<open>p x\<close>
        proof (rule ccontr)
          assume \<open>\<not> p x\<close>
          then have \<open>\<exists>x. \<not> p x\<close> ..
          with \<open>\<not> (\<exists>x. \<not> p x)\<close> show \<bottom> ..
        qed
      qed
      with \<open>\<not> (\<forall>x. p x)\<close> show \<bottom> ..
    qed
    then obtain c where \<open>\<not> p c\<close> ..
    have \<open>p c \<longrightarrow> (\<forall>x. p x)\<close> 
    proof
      assume \<open>p c\<close>
      with \<open>\<not> p c\<close> show \<open>(\<forall>x. p x)\<close> ..
    qed
    then show \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close> ..
  qed
qed

(*2nd version*)
proposition \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close>
proof (rule ccontr)
  assume *: \<open>\<not> (\<exists>x. p x \<longrightarrow> (\<forall>x. p x))\<close>
  have \<open>\<forall>x. p x\<close>
  proof
    fix c
    show \<open>p c\<close>
    proof (rule ccontr)
      assume \<open>\<not> p c\<close>
      have \<open>p c \<longrightarrow> (\<forall>x. p x)\<close>
      proof
        assume \<open>p c\<close>
        from \<open>\<not> p c\<close> and this have \<open>\<bottom>\<close> ..
        then show \<open>\<forall>x. p x\<close> ..
      qed
      then have \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close> ..
      from * and this show \<open>\<bottom>\<close> ..
    qed
  qed
  then have \<open>p c \<longrightarrow> (\<forall>x. p x)\<close> for c by (rule Imp_I)
  then have \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close> ..
  from * and this show \<open>\<bottom>\<close> ..
qed

proposition \<open>\<not> (\<exists>x. p (f x)) \<longrightarrow> (\<forall>x. \<not> p (f x))\<close>
proof
  assume \<open>\<not> (\<exists>x. p (f x))\<close>
  show \<open>\<forall>x. \<not> p (f x)\<close>
  proof
    fix c
    show \<open>\<not> p (f c)\<close>
    proof
      assume \<open>p (f c)\<close>
      then have \<open>\<exists>x. p (f x)\<close> ..
      from \<open>\<not> (\<exists>x. p (f x))\<close> and this show \<open>\<bottom>\<close> ..
    qed
  qed
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

end
