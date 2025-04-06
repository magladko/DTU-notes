theory Assignment_5_pureHOL imports Pure_HOL begin

lemma "\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q"
proof
  assume \<open>\<not> (p \<and> q)\<close>
  show \<open>\<not> p \<or> \<not> q\<close>
  proof
    show \<open>\<not> q\<close>
    proof
      assume \<open>q\<close>
      (*from \<open>\<not> (p \<and> q)\<close> and \<open>q\<close> have \<open>\<not> p\<close> ..*)
      show \<open>\<bottom>\<close> sorry
      (*proof (rule Neg_E)
        show \<open>\<not> p\<close>
        proof
          assume \<open>p\<close>
          from \<open>p\<close> and \<open>q\<close> have \<open>p \<and> q\<close> ..
          from \<open>\<not> (p \<and> q)\<close> and \<open>p \<and> q\<close> show \<open>\<bottom>\<close> ..
        qed
      next
        show \<open>p\<close>
        proof (rule Con_E1)
          show \<open>p \<and> q\<close> sorry
        qed
      qed*)
    qed
    (*proof (rule Neg_E)
      show \<open>\<not> p\<close>
      proof
        assume \<open>p\<close>
      qed
    next
      show \<open>p\<close> sorry
    qed*)
  qed
  (*proof (rule Neg_E)*)
    (*assume \<open>p\<close>*)
    (*show \<open>\<not> p\<close>*)
    (*proof*)
      (*assume \<open>p\<close>*)
      
    (*qed*)
  (*next*)
    (*show \<open>p\<close> sorry*)
  (*next*)
    (*assume \<open>\<not> p\<close>*)
    (*from \<open>\<not> p\<close> have \<open>\<not> p \<or> \<not> q\<close> ..*)
    (*then show \<open>\<not> p \<or> \<not> q\<close> .*)
  (*qed*)
next
  assume \<open>\<not> p \<or> \<not> q\<close>
  show \<open>\<not> (p \<and> q)\<close>
  proof
    assume \<open>p \<and> q\<close>
    then have \<open>p\<close> ..
    from \<open>p \<and> q\<close> have \<open>q\<close> ..
    show \<open>\<bottom>\<close> sorry
  qed
qed

lemma "\<not> (p \<or> q) \<longleftrightarrow> \<not> p \<and> \<not> q"
  sorry

lemma "(\<forall>x. p x) \<longrightarrow> (\<exists>x. p x)"
  sorry

lemma "(\<forall>x. \<not> r x \<longrightarrow> r (f x)) \<longrightarrow> (\<exists>x. r x \<and> r (f (f x)))"
  sorry

end