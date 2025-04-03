theory Pure_I_Special imports Pure_I begin

(*

text \<open>For Pure only the following typedecl, judgment and axiomatization from Pure_I are necessary\<close>

typedecl bool

judgment Trueprop :: \<open>bool \<Rightarrow> prop\<close> (\<open>_\<close>)

axiomatization Imp (infixr \<open>\<longrightarrow>\<close> 3)
  where Imp_I [intro]: \<open>(p \<Longrightarrow> q) \<Longrightarrow> p \<longrightarrow> q\<close>
    and Imp_E [elim]: \<open>p \<longrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>

*)

axiomatization Uni :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>\<forall>\<close> 3)
  where Uni_I [intro]: \<open>(\<And>x. p x) \<Longrightarrow> \<forall>x. p x\<close>
    and Uni_E [elim]: \<open>\<forall>x. p x \<Longrightarrow> p c\<close>

definition Exi:: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>\<exists>\<close> 3)
  where \<open>\<exists>x. p x \<equiv> \<forall>q. (\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close>

lemma Exi_I [intro]: \<open>p c \<Longrightarrow> \<exists>x. p x\<close>
proof (unfold Exi_def)
  assume \<open>p c\<close>
  show \<open>\<forall>q. (\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close>
  proof
    fix q
    show \<open>(\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close>
    proof
      assume \<open>\<forall>x. p x \<longrightarrow> q\<close>
      then have \<open>p c \<longrightarrow> q\<close> ..
      from this and \<open>p c\<close> show q ..
    qed
  qed
qed

lemma Exi_E [elim]: \<open>\<exists>x. p x \<Longrightarrow> (\<And>x. p x \<Longrightarrow> q) \<Longrightarrow> q\<close>
proof (unfold Exi_def)
  assume \<open>\<forall>q. (\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close> and \<open>\<And>x. p x \<Longrightarrow> q\<close>
  from \<open>\<forall>q. (\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close> have \<open>(\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close> ..
  have \<open>\<forall>x. p x \<longrightarrow> q\<close>
  proof
    fix x
    from \<open>\<And>x. p x \<Longrightarrow> q\<close> show \<open>p x \<longrightarrow> q\<close> ..
  qed
  with \<open>(\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close> show q ..
qed

proposition \<open>p a (f a) \<longrightarrow> p a (f a)\<close>
  ..

proposition \<open>\<forall>p. (p a (f a) \<longrightarrow> p a (f a))\<close>
proof
  show \<open>p a (f a) \<longrightarrow> p a (f a)\<close> for p ..
qed

proposition \<open>\<exists>p. (p a (f a) \<longrightarrow> p a (f a))\<close>
proof
  show \<open>p a (f a) \<longrightarrow> p a (f a)\<close> for p ..
qed

end
