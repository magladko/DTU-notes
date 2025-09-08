theory Pure_C_Exercises imports Pure_C begin

(* Solutions must be entered directly in this file by replacing the "oops" with a proper proof *)

proposition \<open>p \<longrightarrow> \<not> \<not> p\<close>
proof
  assume \<open>p\<close>
  show \<open>\<not> \<not> p\<close>
  proof 
    assume \<open>\<not> p\<close>
    from this and \<open>p\<close> show \<open>\<bottom>\<close> ..
  qed
qed

proposition \<open>\<not> \<not> p \<longrightarrow> p\<close>
proof 
  assume \<open>\<not> \<not> p\<close>
  show \<open>p\<close>
  proof (rule classical)
    assume \<open>\<not> p\<close>
    from \<open>\<not> \<not> p\<close> and \<open>\<not> p\<close> have \<open>\<bottom>\<close> ..
    thus \<open>p\<close> ..
  qed
qed

proposition \<open>(\<not> p \<longrightarrow> \<bottom>) \<longrightarrow> p\<close>
proof
  assume \<open>\<not> p \<longrightarrow> \<bottom>\<close>
  then show \<open>p\<close> by (rule Boole)
qed

proposition \<open>(\<not> p \<longrightarrow> p) \<longrightarrow> p\<close>
proof 
  assume \<open>\<not> p \<longrightarrow> p\<close>
  show \<open>p\<close>
  proof (rule classical)
    assume \<open>\<not> p\<close>
    from \<open>\<not> p \<longrightarrow> p\<close> and \<open>\<not> p\<close> show \<open>p\<close> ..
  qed
qed

proposition \<open>((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p\<close>
proof
  assume \<open>(p \<longrightarrow> q) \<longrightarrow> p\<close>
  show \<open>p\<close>
  proof (rule Imp_C)
    assume \<open>p \<longrightarrow> q\<close>
    from \<open>(p \<longrightarrow> q) \<longrightarrow> p\<close> and this show \<open>p\<close> ..
  qed
qed

end
