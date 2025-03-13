theory Pure_I_Exercises_Propositional imports Pure_I begin

(* Solutions must be entered directly in this file by replacing the "oops" with a proper proof *)

(* The crucial test: Please change Pure_I to Main and uncomment the following notation command *)

(* notation False (\<open>\<bottom>\<close>) and True (\<open>\<top>\<close>) *)

proposition \<open>p \<longrightarrow> \<top>\<close>
proof
  show \<open>\<top>\<close> ..
qed

proposition \<open>(\<top> \<longrightarrow> p) \<longrightarrow> p\<close>
proof
  assume \<open>\<top> \<longrightarrow> p\<close>
  have \<open>\<top>\<close> ..
  from \<open>\<top> \<longrightarrow> p\<close> and \<open>\<top>\<close> show \<open>p\<close> ..
qed

proposition \<open>\<top> \<longrightarrow> p \<longrightarrow> p\<close>
proof
  assume \<open>\<top>\<close>
  show \<open>p \<longrightarrow> p\<close> ..
qed

proposition \<open>p \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> q\<close>
proof
  assume \<open>p\<close>
  show \<open>(p \<longrightarrow> q) \<longrightarrow> q\<close>
  proof
    assume \<open>p \<longrightarrow> q\<close>
    from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> show \<open>q\<close> ..
  qed
qed

proposition \<open>p \<and> (p \<longrightarrow> q) \<longrightarrow> q\<close>
proof
  assume \<open>p \<and> (p \<longrightarrow> q)\<close>
  from \<open>p \<and> (p \<longrightarrow> q)\<close> have \<open>p\<close> ..
  from \<open>p \<and> (p \<longrightarrow> q)\<close> have \<open>p \<longrightarrow> q\<close> ..
  from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> show \<open>q\<close> ..
qed

end
