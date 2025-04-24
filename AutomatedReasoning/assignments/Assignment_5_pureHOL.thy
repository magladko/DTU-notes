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
  assume 1: \<open>\<forall>x. \<not> r x \<longrightarrow> r (f x)\<close>
  have *: \<open>r x \<Longrightarrow> \<not> r (f x) \<Longrightarrow> (\<exists>x. r x \<and> r (f (f x)))\<close> for x
  proof
    assume \<open>r x\<close> and \<open>\<not> r (f x)\<close>
    show \<open>r x \<and> r (f (f x))\<close>
    proof
      from \<open>r x\<close> show \<open>r x\<close> .
    next
      from \<open>\<forall>x. \<not> r x \<longrightarrow> r (f x)\<close> have \<open>\<not> r (f x) \<longrightarrow> r (f (f x))\<close> ..
      from \<open>\<not> r (f x) \<longrightarrow> r (f (f x))\<close> and \<open>\<not> r (f x)\<close> show \<open>r (f (f x))\<close> ..
    qed
  qed
  fix c 
  have \<open>\<exists>x. r x\<close>
  proof -
    have \<open>r c \<or> \<not> r c\<close> by (rule LEM)
    then show \<open>\<exists>x. r x\<close>
    proof
      assume \<open>r c\<close>
      then show ?thesis ..
    next
      assume \<open>\<not> r c\<close>
      from 1 have \<open>\<not> r c \<longrightarrow> r (f c)\<close> ..
      from this and \<open>\<not> r c\<close> have \<open>r (f c)\<close> ..
      then show ?thesis ..
    qed
  qed
  from \<open>\<exists>x. r x\<close> obtain x where \<open>r x\<close> ..
  have \<open>r (f x) \<or> \<not> r (f x)\<close> by (rule LEM)
  then show \<open>\<exists>x. r x \<and> r (f (f x))\<close>
  proof
    assume \<open>r (f x)\<close>
    have \<open>r (f (f x)) \<or> \<not> r (f (f x))\<close> by (rule LEM)
    then show \<open>\<exists>x. r x \<and> r (f (f x))\<close>
    proof
      assume \<open>r (f (f x))\<close>
      from \<open>r x\<close> and this have \<open>r x \<and> r (f (f x))\<close> ..
      then show ?thesis ..
    next
      assume \<open>\<not> r (f (f x))\<close>
      from 1 have \<open>\<not> r (f (f x)) \<longrightarrow> r (f (f (f x)))\<close> ..
      from this and \<open>\<not> r (f (f x))\<close> have \<open>r (f (f (f x)))\<close> ..
      from \<open>r (f x)\<close> and this have \<open>r (f x) \<and> r (f (f (f x)))\<close> ..
      then show ?thesis ..
    qed
  next
    assume \<open>\<not> r (f x)\<close>
    from * and \<open>r x\<close> and this show \<open>\<exists>x. r x \<and> r (f (f x))\<close> .
  qed
qed

end