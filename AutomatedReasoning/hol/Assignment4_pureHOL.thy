theory Assignment4_pureHOL imports Pure_HOL begin

section "Formula 1"

proposition \<open>(\<not> p \<longrightarrow> p) \<longrightarrow> (p \<longrightarrow> \<not> p) \<longrightarrow> q\<close>
proof
  assume \<open>\<not> p \<longrightarrow> p\<close>
  show \<open>(p \<longrightarrow> \<not> p) \<longrightarrow> q\<close>
  proof
    assume \<open>p \<longrightarrow> \<not> p\<close>
    show \<open>q\<close>
    proof -
      have \<open>p\<close>
      proof (rule classical)
        assume \<open>\<not> p\<close>
        with \<open>\<not> p \<longrightarrow> p\<close> show \<open>p\<close> ..
      qed
      with \<open>p \<longrightarrow> \<not> p\<close> have \<open>\<not> p\<close> ..
      from this and \<open>p\<close> have \<open>\<bottom>\<close> ..
      thus \<open>q\<close> ..
    qed
  qed
qed

section "Formula 2"

proposition "(\<forall>x. p x) \<longrightarrow> p a \<and> p (f a)"
proof
  assume \<open>\<forall>x. p x\<close>
  show \<open>p a \<and> p (f a)\<close>
  proof
    from \<open>\<forall>x. p x\<close> show \<open>p a\<close> ..
    from \<open>\<forall>x. p x\<close> show \<open>p (f a)\<close> ..
  qed
qed

section "Formula 3"

proposition "(\<exists>x. \<forall>y. r x y) \<longrightarrow> (\<forall>y. \<exists>x. r x y)"
proof
  assume \<open>\<exists>x. \<forall>y. r x y\<close>
  then obtain c where \<open>\<forall>y. r c y\<close> ..
  show \<open>\<forall>y. \<exists>x. r x y\<close>
  proof
    fix d
    show \<open>\<exists>x. r x d\<close>
    proof
      from \<open>\<forall>y. r c y\<close> show \<open>r c d\<close> ..
    qed
  qed
qed

end