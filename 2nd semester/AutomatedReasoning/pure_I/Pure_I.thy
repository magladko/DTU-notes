theory Pure_I imports Pure begin

typedecl bool

judgment Trueprop :: \<open>bool \<Rightarrow> prop\<close> (\<open>_\<close>)

axiomatization Imp (infixr \<open>\<longrightarrow>\<close> 3)
  where Imp_I [intro]: \<open>(p \<Longrightarrow> q) \<Longrightarrow> p \<longrightarrow> q\<close>
    and Imp_E [elim]: \<open>p \<longrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>

axiomatization Dis (infixr \<open>\<or>\<close> 4)
  where Dis_E [elim]: \<open>p \<or> q \<Longrightarrow> (p \<Longrightarrow> r) \<Longrightarrow> (q \<Longrightarrow> r) \<Longrightarrow> r\<close>
    and Dis_I1 [intro]: \<open>p \<Longrightarrow> p \<or> q\<close>
    and Dis_I2 [intro]: \<open>q \<Longrightarrow> p \<or> q\<close>

axiomatization Con (infixr \<open>\<and>\<close> 5)
  where Con_I [intro]: \<open>p \<Longrightarrow> q \<Longrightarrow> p \<and> q\<close>
    and Con_E1 [elim]: \<open>p \<and> q \<Longrightarrow> p\<close>
    and Con_E2 [elim]: \<open>p \<and> q \<Longrightarrow> q\<close>

axiomatization Falsity (\<open>\<bottom>\<close>)
  where Falsity_E [elim]: \<open>\<bottom> \<Longrightarrow> p\<close>

definition Truth (\<open>\<top>\<close>) where \<open>\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>\<close>

theorem Truth_I [intro]: \<open>\<top>\<close>
  unfolding Truth_def ..

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

definition Iff (infixr \<open>\<longleftrightarrow>\<close> 3) where \<open>p \<longleftrightarrow> q \<equiv> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>

theorem Iff_I [intro]: \<open>(p \<Longrightarrow> q) \<Longrightarrow> (q \<Longrightarrow> p) \<Longrightarrow> p \<longleftrightarrow> q\<close>
  unfolding Iff_def
proof -
  assume \<open>p \<Longrightarrow> q\<close> and \<open>q \<Longrightarrow> p\<close>
  from \<open>p \<Longrightarrow> q\<close> have \<open>p \<longrightarrow> q\<close> ..
  from \<open>q \<Longrightarrow> p\<close> have \<open>q \<longrightarrow> p\<close> ..
  from \<open>p \<longrightarrow> q\<close> and \<open>q \<longrightarrow> p\<close> show \<open>(p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close> ..
qed

theorem Iff_E1 [elim]: \<open>p \<longleftrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>
  unfolding Iff_def
proof -
  assume \<open>(p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>
  then have \<open>p \<longrightarrow> q\<close> ..
  then show \<open>p \<Longrightarrow> q\<close> ..
qed

theorem Iff_E2 [elim]: \<open>p \<longleftrightarrow> q \<Longrightarrow> q \<Longrightarrow> p\<close>
  unfolding Iff_def
proof -
  assume \<open>(p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>
  then have \<open>q \<longrightarrow> p\<close> ..
  then show \<open>q \<Longrightarrow> p\<close> ..
qed

proposition \<open>p \<longrightarrow> \<not> \<not> p\<close>
proof
  assume \<open>p\<close>
  show \<open>\<not> \<not> p\<close>
  proof
    assume \<open>\<not> p\<close>
    from \<open>\<not> p\<close> and \<open>p\<close> show \<open>\<bottom>\<close> ..
  qed
qed

proposition \<open>(p \<longrightarrow> q) \<and> \<not> q \<longrightarrow> \<not> p\<close>
proof
  assume \<open>(p \<longrightarrow> q) \<and> \<not> q\<close>
  show \<open>\<not> p\<close>
  proof
    assume \<open>p\<close>
    from \<open>(p \<longrightarrow> q) \<and> \<not> q\<close> have \<open>p \<longrightarrow> q\<close> ..
    from \<open>p \<longrightarrow> q\<close> and \<open>p\<close> have \<open>q\<close> ..
    from \<open>(p \<longrightarrow> q) \<and> \<not> q\<close> have \<open>\<not> q\<close> ..
    from \<open>\<not> q\<close> and \<open>q\<close> show \<open>\<bottom>\<close> ..
  qed
qed

proposition \<open>(p \<longleftrightarrow> q) \<longleftrightarrow> q \<longleftrightarrow> p\<close>
proof
  assume \<open>p \<longleftrightarrow> q\<close>
  show \<open>q \<longleftrightarrow> p\<close>
  proof
    from \<open>p \<longleftrightarrow> q\<close> show \<open>q \<Longrightarrow> p\<close> ..
  next
    from \<open>p \<longleftrightarrow> q\<close> show \<open>p \<Longrightarrow> q\<close> ..
  qed
next
  assume \<open>q \<longleftrightarrow> p\<close>
  show \<open>p \<longleftrightarrow> q\<close>
  proof
    from \<open>q \<longleftrightarrow> p\<close> show \<open>p \<Longrightarrow> q\<close> ..
  next
    from \<open>q \<longleftrightarrow> p\<close> show \<open>q \<Longrightarrow> p\<close> ..
  qed
qed

end
