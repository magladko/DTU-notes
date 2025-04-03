theory Pure_C imports Pure begin

typedecl bool

judgment Trueprop :: \<open>bool \<Rightarrow> prop\<close> (\<open>_\<close>)

axiomatization Imp (infixr \<open>\<longrightarrow>\<close> 3) and Falsity (\<open>\<bottom>\<close>)
  where Imp_I [intro]: \<open>(p \<Longrightarrow> q) \<Longrightarrow> p \<longrightarrow> q\<close>
    and Imp_E [elim]: \<open>p \<longrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>
    and Imp_C: \<open>(p \<longrightarrow> q \<Longrightarrow> p) \<Longrightarrow> p\<close>
    and Falsity_E [elim]: \<open>\<bottom> \<Longrightarrow> p\<close>

definition Neg (\<open>\<not> _\<close> [6] 6) where \<open>\<not> p \<equiv> p \<longrightarrow> \<bottom>\<close>

theorem Neg_I [intro]: \<open>(p \<Longrightarrow> \<bottom>) \<Longrightarrow> \<not> p\<close>
  unfolding Neg_def ..

theorem Neg_E [elim]: \<open>\<not> p \<Longrightarrow> p \<Longrightarrow> q\<close>
  unfolding Neg_def
proof -
  assume \<open>p \<longrightarrow> \<bottom>\<close> and \<open>p\<close>
  then have \<open>\<bottom>\<close> ..
  then show \<open>q\<close> ..
qed

theorem classical: \<open>(\<not> p \<Longrightarrow> p) \<Longrightarrow> p\<close>
proof -
  assume \<open>\<not> p \<Longrightarrow> p\<close>
  show \<open>p\<close>
  proof (rule Imp_C)
    assume \<open>p \<longrightarrow> \<bottom>\<close>
    have \<open>\<not> p\<close>
    proof
      assume \<open>p\<close>
      with \<open>p \<longrightarrow> \<bottom>\<close> show \<open>\<bottom>\<close> ..
    qed
    with \<open>\<not> p \<Longrightarrow> p\<close> show \<open>p\<close> .
  qed
qed

theorem ccontr: \<open>(\<not> p \<Longrightarrow> \<bottom>) \<Longrightarrow> p\<close>
proof -
  assume \<open>\<not> p \<Longrightarrow> \<bottom>\<close>
  then have \<open>\<not> p \<Longrightarrow> p\<close> ..
  with classical show \<open>p\<close> .
qed

theorem Boole: \<open>\<not> p \<longrightarrow> \<bottom> \<Longrightarrow> p\<close>
proof (rule ccontr)
  assume \<open>\<not> p \<longrightarrow> \<bottom>\<close> and \<open>\<not> p\<close>
  then show \<open>\<bottom>\<close> ..
qed

end
