theory Pure_HOL_Exercises imports Pure_HOL begin

(* Solutions must be entered directly in this file by replacing the "oops" with a proper proof *)

proposition \<open>(p \<longrightarrow> q) \<and> p \<longrightarrow> q\<close>
proof
  assume 0: \<open>(p \<longrightarrow> q) \<and> p\<close>
  then have 1: \<open>p \<longrightarrow> q\<close> ..
  from 0 have \<open>p\<close> ..
  from 1 and this show \<open>q\<close> ..
qed

proposition \<open>\<not> (\<exists>x. p x) \<longrightarrow> (\<forall>x. \<not> p x)\<close>
proof
  assume \<open>\<not>(\<exists>x. p x)\<close>
  show \<open>(\<forall>x. \<not> p x)\<close>
  proof
    fix c
    show \<open>\<not> p c\<close>
    proof
      assume \<open>p c\<close>
      then have \<open>\<exists>x. p x\<close> ..
      from \<open>\<not>(\<exists>x. p x)\<close> and this show \<open>\<bottom>\<close> ..
    qed
  qed
qed

proposition \<open>(\<forall>x. p x \<longrightarrow> (\<exists>y. q y)) \<longrightarrow> (\<forall>y. \<not> q y) \<longrightarrow> (\<forall>x. \<not> p x)\<close>
proof
  assume \<open>\<forall>x. p x \<longrightarrow> (\<exists>y. q y)\<close>
  show \<open>(\<forall>y. \<not> q y) \<longrightarrow> (\<forall>x. \<not> p x)\<close>
  proof
    assume \<open>\<forall>y. \<not> q y\<close>
    show \<open>\<forall>x. \<not> p x\<close>
    proof
      fix c
      show \<open>\<not> p c\<close>
      proof
        assume \<open>p c\<close>
        from \<open>\<forall>x. p x \<longrightarrow> (\<exists>y. q y)\<close> have \<open>(p c) \<longrightarrow> (\<exists>y. q y)\<close> ..
        from this and \<open>p c\<close> have \<open>\<exists>y. q y\<close> ..
        then obtain d where \<open>q d\<close> ..
        from \<open>\<forall>y. \<not> q y\<close> have \<open>\<not> q d\<close> ..
        from this and \<open>q d\<close> show \<open>\<bottom>\<close> ..
      qed
    qed
  qed
qed

end
