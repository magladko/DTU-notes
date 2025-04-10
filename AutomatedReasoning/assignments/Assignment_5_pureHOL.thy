theory Assignment_5_pureHOL imports Pure_HOL begin

proposition \<open>\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q\<close>
proof
  assume \<open>\<not> (p \<and> q)\<close>
  then have \<open>(p \<and> q) \<longrightarrow> \<bottom>\<close>  unfolding Neg_def .
  show \<open>\<not> p \<or> \<not> q\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<not> p \<or> \<not> q)\<close>
    have \<open>p\<close>
    proof (rule ccontr)
      assume \<open>\<not> p\<close>
      then have \<open>\<not> p \<or> \<not> q\<close> ..
      from  \<open>\<not> (\<not> p \<or> \<not> q)\<close> and this show \<open>\<bottom>\<close> ..
    qed
    have \<open>q\<close>
    proof (rule ccontr)
      assume \<open>\<not> q\<close>
      then have \<open>\<not> p \<or> \<not> q\<close> ..
      from  \<open>\<not> (\<not> p \<or> \<not> q)\<close> and this show \<open>\<bottom>\<close> ..
    qed
    from \<open>p\<close> and \<open>q\<close> have \<open>p \<and> q\<close> ..
    from \<open>\<not> (p \<and> q)\<close> and this show \<open>\<bottom>\<close> ..
  qed
next
  assume \<open>\<not> p \<or> \<not> q\<close>
  show \<open>\<not> (p \<and> q)\<close>
  proof
    assume \<open>p \<and> q\<close>
    then have \<open>p\<close> ..
    from \<open>p \<and> q\<close> have \<open>q\<close> ..
    from \<open>\<not> p \<or> \<not> q\<close> show \<open>\<bottom>\<close>
    proof
      assume \<open>\<not> p\<close>
      from this and \<open>p\<close> show \<open>\<bottom>\<close> ..
    next
      assume \<open>\<not> q\<close>
      from this and \<open>q\<close> show \<open>\<bottom>\<close> ..
    qed
  qed
qed

proposition \<open>\<not> (p \<or> q) \<longleftrightarrow> \<not> p \<and> \<not> q\<close>
proof
  assume \<open>\<not> (p \<or> q)\<close>
  have \<open>\<not> p\<close>
  proof
    assume \<open>p\<close>
    then have \<open>p \<or> q\<close> ..
    from \<open>\<not> (p \<or> q)\<close> and this show \<open>\<bottom>\<close> ..
  qed
  have \<open>\<not> q\<close>
  proof
    assume \<open>q\<close>
    then have \<open>p \<or> q\<close> ..
    from \<open>\<not> (p \<or> q)\<close> and this show \<open>\<bottom>\<close> ..
  qed
  from \<open>\<not> p\<close> and \<open>\<not> q\<close> show \<open>\<not> p \<and> \<not> q\<close> ..
next
  assume \<open>\<not> p \<and> \<not> q\<close>
  then have \<open>\<not> p\<close> ..
  from \<open>\<not> p \<and> \<not> q\<close> have \<open>\<not> q\<close> ..
  show \<open>\<not> (p \<or> q)\<close>
  proof
    assume \<open>p \<or> q\<close>
    then show \<open>\<bottom>\<close>
    proof
      assume \<open>p\<close>
      from \<open>\<not> p\<close> and this show \<open>\<bottom>\<close> ..
    next
      assume \<open>q\<close>
      from \<open>\<not> q\<close> and this show \<open>\<bottom>\<close> ..
    qed
  qed
qed

proposition \<open>(\<forall>x. p x) \<longrightarrow> (\<exists>x. p x)\<close>
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
  have *: \<open>r x \<Longrightarrow> \<not> r (f x) \<Longrightarrow> (\<exists>x. r x \<and> r (f (f x)))\<close> for x
    sorry
  fix c
  have \<open>r c \<or> \<not> r c\<close> by (rule LEM)
  then show \<open>\<exists>x. r x \<and> r (f (f x))\<close>
  proof
    assume \<open>r c\<close>
    show \<open>\<exists>x. r x \<and> r (f (f x))\<close> 
    proof
      show \<open>r c \<and> r (f (f c))\<close>
      proof
        from \<open>r c\<close> show \<open>r c\<close> .
      next
        show \<open>r (f (f c))\<close> sorry
        (*proof (rule ccontr)
          
        qed*)
      qed
    qed
  next
    assume \<open>\<not> r c\<close>
    show \<open>\<exists>x. r x \<and> r (f (f x))\<close> sorry
  qed
qed

end