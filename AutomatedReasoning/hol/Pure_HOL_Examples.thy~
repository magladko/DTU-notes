theory Pure_HOL_Examples imports Pure_HOL begin

proposition \<open>(\<forall>x. p x) \<longrightarrow> p a\<close>
proof
  assume \<open>\<forall>x. p x\<close>
  then show \<open>p a\<close> ..
qed

proposition \<open>\<forall>x. p x \<longrightarrow> p x\<close>
proof
  fix c
  show \<open>p c \<longrightarrow> p c\<close> ..
qed

proposition \<open>(\<forall>x. r x x) \<longrightarrow> (\<forall>x. \<exists>y. r x y)\<close>
proof
  assume \<open>\<forall>x. r x x\<close>
  show \<open>\<forall>x. \<exists>y. r x y\<close>
  proof
    fix c
    show \<open>\<exists>y. r c y\<close>
    proof
      from \<open>\<forall>x. r x x\<close> show \<open>r c c\<close> ..
    qed
  qed
qed

proposition \<open>(\<forall>x. r x x) \<longrightarrow> (\<forall>x. \<exists>y. r x y)\<close>
proof
  assume \<open>\<forall>x. r x x\<close>
  show \<open>\<forall>x. \<exists>y. r x y\<close>
  proof
    fix c
    from \<open>\<forall>x. r x x\<close> have \<open>r c c\<close> ..
    then show \<open>\<exists>y. r c y\<close> ..
  qed
qed

proposition \<open>(\<forall>x. \<not> p x) \<longrightarrow> \<not> (\<exists>x. p x)\<close>
proof
  assume \<open>\<forall>x. \<not> p x\<close>
  show \<open>\<not> (\<exists>x. p x)\<close>
  proof
    assume \<open>\<exists>x. p x\<close>
    then obtain c where \<open>p c\<close> ..
    from \<open>\<forall>x. \<not> p x\<close> have \<open>\<not> p c\<close> ..
    from \<open>\<not> p c\<close> and \<open>p c\<close> show \<open>\<bottom>\<close> ..
  qed
qed

proposition \<open>(\<forall>x. \<not> p x) \<longrightarrow> \<not> (\<exists>x. p x)\<close>
proof
  assume \<open>\<forall>x. \<not> p x\<close>
  show \<open>\<not> (\<exists>x. p x)\<close>
  proof
    assume \<open>\<exists>x. p x\<close>
    then obtain c where \<open>p c\<close> ..
    from \<open>\<forall>x. \<not> p x\<close> have \<open>\<not> p c\<close> ..
    from this and \<open>p c\<close> show \<open>\<bottom>\<close> ..
  qed
qed

end
