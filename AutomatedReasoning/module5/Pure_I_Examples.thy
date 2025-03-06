theory Pure_I_Examples imports Pure_I begin

proposition \<open>p \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  show \<open>p\<close> by fact
qed

proposition \<open>p \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  from \<open>p\<close> show \<open>p\<close> by -
qed

proposition \<open>p \<longrightarrow> p\<close>
proof
  assume *: \<open>p\<close>
  from * show \<open>p\<close> .
qed

proposition \<open>p \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  from this show \<open>p\<close> .
qed

proposition \<open>p \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  then show \<open>p\<close> .
qed

proposition \<open>p \<and> q \<longrightarrow> p\<close>
proof
  assume \<open>p \<and> q\<close>
  then show \<open>p\<close> ..
qed

end
