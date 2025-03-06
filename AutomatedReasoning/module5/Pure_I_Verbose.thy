theory Pure_I_Verbose imports Pure_I begin

text \<open>A result from theory Pure_I but with explicit rule names\<close>

proposition \<open>p \<longrightarrow> \<not> \<not> p\<close>
proof (rule Imp_I)
  assume \<open>p\<close>
  show \<open>\<not> \<not> p\<close>
  proof (rule Neg_I)
    assume \<open>\<not> p\<close>
    from \<open>\<not> p\<close> and \<open>p\<close> show \<open>\<bottom>\<close> by (rule Neg_E)
  qed
qed

end
