theory Assignment_5_pureHOL imports Pure_HOL begin

lemma "\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q"
proof
  assume \<open>\<not> (p \<and> q)\<close>
  then have \<open>(p \<and> q) \<longrightarrow> \<bottom>\<close>  unfolding Neg_def .
  show \<open>\<not> p \<or> \<not> q\<close>
  proof
    show \<open>\<not> q\<close>
    proof
      assume \<open>q\<close>
      (*from \<open>(p \<and> q) \<longrightarrow> \<bottom>\<close> and \<open>q\<close> have \<open>p \<longrightarrow> \<bottom>\<close> ..*)
      (*from \<open>\<not> (p \<and> q)\<close> and \<open>q\<close> have \<open>\<not> p\<close> unfolding Neg_def*)
      
      
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
    (*from \<open>p\<close> have \<open>\<not> \<not> p\<close> .. (rule not_not)*)
    show \<open>\<bottom>\<close> sorry
  qed
qed

lemma "(\<forall>x. p x) \<longrightarrow> (\<exists>x. p x)"
proof
  assume \<open>\<forall>x. p x\<close>
  show \<open>\<exists>x. p x\<close>
  proof
    fix c
    from \<open>\<forall>x. p x\<close> show \<open>p c\<close> ..
  qed
qed

lemma "(\<forall>x. \<not> r x \<longrightarrow> r (f x)) \<longrightarrow> (\<exists>x. r x \<and> r (f (f x)))"
proof
  assume \<open>\<forall>x. \<not> r x \<longrightarrow> r (f x)\<close>
  show \<open>\<exists>x. r x \<and> r (f (f x))\<close>
  proof
    fix c
    from \<open>\<forall>x. \<not> r x \<longrightarrow> r (f x)\<close> have \<open>\<not> r c \<longrightarrow> r (f c)\<close> ..
    show \<open>r c \<and> r (f (f c))\<close> sorry
  qed
qed

end