theory Assignment3_Pure_I imports Pure_I begin

proposition \<open>\<not> q \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> \<not> p\<close>
proof
  assume \<open>\<not> q\<close>
  show \<open>(p \<longrightarrow> q) \<longrightarrow> \<not> p\<close>
  proof
    assume \<open>p \<longrightarrow> q\<close>
    show \<open>\<not> p\<close>
    proof (rule Neg_I)
      assume \<open>p\<close>
      from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> have \<open>q\<close> ..
      from \<open>\<not> q\<close> and \<open>q\<close> show \<open>\<bottom>\<close> by (rule Neg_E)
    qed
  qed
qed

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> \<not> q \<longrightarrow> \<not> p\<close>
proof
  assume \<open>p \<longrightarrow> q\<close>
  show \<open>\<not> q \<longrightarrow> \<not> p\<close>
  proof
    assume \<open>\<not> q\<close>
    show \<open>\<not> p\<close>
    proof
      assume \<open>p\<close>
      from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> have \<open>q\<close> ..
      from \<open>\<not> q\<close> and \<open>q\<close> show \<open>\<bottom>\<close> ..
    qed
  qed
qed

end