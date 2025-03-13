theory Pure_I_Examples_Propositional imports Pure_I begin

proposition \<open>p \<longrightarrow> p\<close>
  ..

proposition \<open>\<bottom> \<longrightarrow> \<top>\<close>
proof
  show \<open>\<top>\<close> ..
qed

proposition \<open>p \<and> q \<longrightarrow> p\<close>
proof
  assume \<open>p \<and> q\<close>
  then show \<open>p\<close> ..
qed

proposition \<open>p \<and> q \<longrightarrow> q\<close>
proof
  assume \<open>p \<and> q\<close>
  then show \<open>q\<close> ..
qed

proposition \<open>p \<longrightarrow> q \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  show \<open>q \<longrightarrow> p\<close>
  proof
    from \<open>p\<close> show \<open>p\<close> .
  qed
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
      with \<open>p \<longrightarrow> q\<close> have \<open>q\<close> ..
      from \<open>p \<longrightarrow> q \<longrightarrow> r\<close> and \<open>p\<close> have \<open>q \<longrightarrow> r\<close> ..
      from this and \<open>q\<close> show \<open>r\<close> ..
    qed
  qed
qed

proposition \<open>p \<longrightarrow> \<not> \<not> p\<close>
proof
  assume \<open>p\<close>
  show \<open>\<not> \<not> p\<close>
  proof
    assume \<open>\<not> p\<close>
    from this and \<open>p\<close> show \<open>\<bottom>\<close> ..
  qed
qed

proposition \<open>(p \<longrightarrow> q) \<and> \<not> q \<longrightarrow> \<not> p\<close>
proof
  assume \<open>(p \<longrightarrow> q) \<and> \<not> q\<close>
  show \<open>\<not> p\<close>
  proof
    from \<open>(p \<longrightarrow> q) \<and> \<not> q\<close> have \<open>p \<longrightarrow> q\<close> ..
    from \<open>(p \<longrightarrow> q) \<and> \<not> q\<close> have \<open>\<not> q\<close> ..
    assume \<open>p\<close>
    with \<open>p \<longrightarrow> q\<close> have \<open>q\<close> ..
    with \<open>\<not> q\<close> show \<open>\<bottom>\<close> ..
  qed
qed

proposition \<open>(p \<longleftrightarrow> q) \<longleftrightarrow> q \<longleftrightarrow> p\<close>
proof
  assume \<open>p \<longleftrightarrow> q\<close>
  show \<open>q \<longleftrightarrow> p\<close>
  proof
    assume \<open>q\<close>
    with \<open>p \<longleftrightarrow> q\<close> show \<open>p\<close> ..
  next
    assume \<open>p\<close>
    with \<open>p \<longleftrightarrow> q\<close> show \<open>q\<close> ..
  qed
next
  assume \<open>q \<longleftrightarrow> p\<close>
  show \<open>p \<longleftrightarrow> q\<close>
  proof
    assume \<open>p\<close>
    with \<open>q \<longleftrightarrow> p\<close> show \<open>q\<close> ..
  next
    assume \<open>q\<close>
    with \<open>q \<longleftrightarrow> p\<close> show \<open>p\<close> ..
  qed
qed

end
