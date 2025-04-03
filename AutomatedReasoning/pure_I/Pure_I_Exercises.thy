theory Pure_I_Exercises imports Pure_I begin

(* Solutions must be entered directly in this file by replacing the "oops" with a proper proof *)

(* The crucial test: Please change Pure_I to Main and uncomment the following notation command *)

(* notation False (\<open>\<bottom>\<close>) and True (\<open>\<top>\<close>) *)

proposition \<open>p \<and> q \<longrightarrow> q\<close>
proof
  assume \<open>p \<and> q\<close>
  then show \<open>q\<close> ..
qed

proposition \<open>p \<longrightarrow> q \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  then show \<open>q \<longrightarrow> p\<close> ..
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
      from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> have \<open>q\<close> ..
      from \<open>p \<longrightarrow> q \<longrightarrow> r\<close> and \<open>p\<close> have \<open>q \<longrightarrow> r\<close> ..
      from \<open>q \<longrightarrow> r\<close> and \<open>q\<close> show \<open>r\<close> ..
    qed
  qed
qed


end
