theory Assignment4_pureHOL imports Pure_HOL begin

lemma "(\<not> p \<longrightarrow> p) \<longrightarrow> (p \<longrightarrow> \<not> p) \<longrightarrow> q"
proof
  assume \<open>\<not> p \<longrightarrow> p\<close>
  show \<open>(p \<longrightarrow> \<not> p) \<longrightarrow> q\<close>
  proof
    assume \<open>p \<longrightarrow> \<not> p\<close>
    show \<open>q\<close>
      sorry
  qed
qed

end