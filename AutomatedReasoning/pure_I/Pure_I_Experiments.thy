theory Pure_I_Experiments imports Pure_I begin

theorem (* Truth_E *) \<open>\<top> \<Longrightarrow> p \<Longrightarrow> p\<close> .

theorem (* Neg_I *) \<open>(p \<Longrightarrow> \<bottom>) \<Longrightarrow> \<not> p\<close> ..

theorem (* Neg_E *) \<open>\<not> p \<Longrightarrow> p \<Longrightarrow> \<bottom>\<close>
proof -
  assume \<open>\<not> p\<close> and \<open>p\<close>
  then show \<open>\<bottom>\<close> ..
qed

theorem (* Iff_I *) \<open>(p \<Longrightarrow> q) \<Longrightarrow> (q \<Longrightarrow> p) \<Longrightarrow> p \<longleftrightarrow> q\<close>
  unfolding Iff_def
proof
  assume \<open>p \<Longrightarrow> q\<close>
  assume \<open>q \<Longrightarrow> p\<close>
  from \<open>p \<Longrightarrow> q\<close> show \<open>p \<longrightarrow> q\<close> ..
  from \<open>q \<Longrightarrow> p\<close> show \<open>q \<longrightarrow> p\<close> ..
qed

theorem (* Iff_I *) \<open>(p \<Longrightarrow> q) \<Longrightarrow> (q \<Longrightarrow> p) \<Longrightarrow> p \<longleftrightarrow> q\<close>
  unfolding Iff_def
proof
  assume \<open>p \<Longrightarrow> q\<close>
  then show \<open>p \<longrightarrow> q\<close> ..
next
  assume \<open>q \<Longrightarrow> p\<close>
  then show \<open>q \<longrightarrow> p\<close> ..
qed

proposition \<open>\<top>\<close>
  ..

proposition \<open>\<bottom> \<longrightarrow> \<bottom>\<close>
  ..

proposition xxx: \<open>p \<longrightarrow> p\<close>
  ..

proposition \<open>\<bottom> \<longrightarrow> \<bottom>\<close>
  ..

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> p \<longrightarrow> q\<close>
  ..

proposition \<open>p \<longrightarrow> q \<longrightarrow> p\<close>
proof
  assume \<open>p\<close>
  show \<open>q \<longrightarrow> p\<close>
  proof
    assume \<open>q\<close>
    show \<open>p\<close> by fact
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
      with \<open>p \<longrightarrow> q \<longrightarrow> r\<close> have \<open>q \<longrightarrow> r\<close> ..
      assume \<open>p\<close>
      with \<open>p \<longrightarrow> q\<close> have \<open>q\<close> ..
      with \<open>q \<longrightarrow> r\<close> show \<open>r\<close> ..
    qed
  qed
qed

end
