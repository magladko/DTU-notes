theory Pure_I_Exercises_Solutions imports Pure_I begin

proposition \<open>p \<and> q \<longrightarrow> q\<close>
proof
  assume \<open>p \<and> q\<close>
  then show \<open>q\<close> ..
qed

proposition \<open>p \<longrightarrow> q \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  show \<open>q \<longrightarrow> p\<close>
  proof
    show \<open>p\<close> by fact
  qed
qed

proposition \<open>(p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> p \<longrightarrow> r\<close>
proof
  assume \<open>p \<longrightarrow> q \<longrightarrow> r\<close>
  show \<open>(p \<longrightarrow> q) \<longrightarrow> p \<longrightarrow> r\<close>
  proof
    assume \<open>p \<longrightarrow> q\<close>
    show \<open>p \<longrightarrow> r\<close>
    proof
      assume \<open>p\<close>
      from \<open>p \<longrightarrow> q \<longrightarrow> r\<close> and \<open>p\<close> have \<open>q \<longrightarrow> r\<close> ..
      from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> have \<open>q\<close> ..
      from \<open>q \<longrightarrow> r\<close> and \<open>q\<close> show \<open>r\<close> ..
    qed
  qed
qed

end
