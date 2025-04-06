theory Assignment_5_pureHOL imports Pure_HOL begin

lemma "\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q"
proof
  assume \<open>\<not> (p \<and> q)\<close>
  show \<open>\<not> p \<or> \<not> q\<close>
  proof (*(rule Dis_I2)*)
    (*assume \<open>p \<and> q\<close>*)
    (*then have \<open>q\<close> ..*)
    (*from \<open>p \<and> q\<close> have \<open>p\<close> ..*)
    (*from \<open>\<not> (p \<and> q)\<close> and \<open>p \<and> q\<close> have \<open>\<bottom>\<close> ..*)
    show \<open>\<not> q\<close>
    proof (rule Neg_I)
      (*assume \<open>p \<and> q\<close>*)
      assume \<open>q\<close>
      
      (*from \<open>\<not> (p \<and> q)\<close> and \<open>p \<and> q\<close> have \<open>\<bottom>\<close> ..*)
    qed
  qed
next
  assume \<open>\<not> p \<or> \<not> q\<close>
  show \<open>\<not> (p \<and> q)\<close> sorry
qed

lemma "\<not> (p \<or> q) \<longleftrightarrow> \<not> p \<and> \<not> q"
  sorry

lemma "(\<forall>x. p x) \<longrightarrow> (\<exists>x. p x)"
  sorry

lemma "(\<forall>x. \<not> r x \<longrightarrow> r (f x)) \<longrightarrow> (\<exists>x. r x \<and> r (f (f x)))"
  sorry

end