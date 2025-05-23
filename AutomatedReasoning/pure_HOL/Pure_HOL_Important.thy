theory Pure_HOL_Important imports Pure_HOL begin

proposition \<open>\<exists>x. \<forall>y. p x \<longrightarrow> p y\<close>
proof -
  have \<open>(\<forall>x. p x) \<or> \<not> (\<forall>x. p x)\<close>
    by (rule LEM)
  then show \<open>\<exists>x. \<forall>y. p x \<longrightarrow> p y\<close>
  proof
    assume \<open>\<forall>x. p x\<close>
    then have \<open>p c\<close> for c ..
    then have \<open>q \<longrightarrow> p c\<close> for c q by (rule Imp_I)
    then have \<open>\<forall>y. q \<longrightarrow> p y\<close> for q ..
    then show \<open>\<exists>x. \<forall>y. p x \<longrightarrow> p y\<close> ..
  next
    assume \<open>\<not> (\<forall>x. p x)\<close>
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
    have \<open>p c \<longrightarrow> q\<close> for q
    proof
      assume \<open>p c\<close>
      with \<open>\<not> p c\<close> show q ..
    qed
    then have \<open>\<forall>y. p c \<longrightarrow> p y\<close> ..
    then show \<open>\<exists>x. \<forall>y. p x \<longrightarrow> p y\<close> ..
  qed
qed

end
