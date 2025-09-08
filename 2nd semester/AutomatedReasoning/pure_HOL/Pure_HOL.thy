text \<open>Pure Higher-Order\<close>

theory Pure_HOL imports Pure begin

typedecl bool

judgment Trueprop :: \<open>bool \<Rightarrow> prop\<close> (\<open>_\<close> 5)

axiomatization Imp (infixr \<open>\<longrightarrow>\<close> 25)
  where Imp_I [intro]: \<open>(p \<Longrightarrow> q) \<Longrightarrow> p \<longrightarrow> q\<close>
    and Imp_E [elim]: \<open>p \<longrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>

axiomatization Uni (binder \<open>\<forall>\<close> 10)
  where Uni_I [intro]: \<open>(\<And>x. p x) \<Longrightarrow> \<forall>x. p x\<close>
    and Uni_E [elim]: \<open>\<forall>x. p x \<Longrightarrow> p c\<close> for c :: 'a

definition True (\<open>\<top>\<close>) where \<open>\<top> \<equiv> \<forall>p. p \<longrightarrow> p\<close>

lemma True_I [intro]: \<top>
proof (unfold True_def)
  show \<open>\<forall>p. p \<longrightarrow> p\<close>
  proof
    fix p
    show \<open>p \<longrightarrow> p\<close> ..
  qed
qed

definition Exi (binder \<open>\<exists>\<close> 10) where \<open>\<exists>x. p x \<equiv> \<forall>q. (\<forall>x. p x \<longrightarrow> q) \<longrightarrow> q\<close>

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

definition False (\<open>\<bottom>\<close>) where \<open>\<bottom> \<equiv> \<forall>p. p\<close>

lemma Fls_E [elim]: \<open>\<bottom> \<Longrightarrow> p\<close>
proof (unfold False_def)
  assume \<open>\<forall>p. p\<close>
  then show p ..
qed

definition Neg (\<open>\<not> _\<close> [40] 40) where \<open>\<not> p \<equiv> p \<longrightarrow> \<bottom>\<close>

lemma Neg_I [intro]: \<open>(p \<Longrightarrow> \<bottom>) \<Longrightarrow> \<not> p\<close>
proof (unfold Neg_def)
  assume \<open>p \<Longrightarrow> \<bottom>\<close>
  then show \<open>p \<longrightarrow> \<bottom>\<close> ..
qed

lemma Neg_E [elim]: \<open>\<not> p \<Longrightarrow> p \<Longrightarrow> q\<close>
proof (unfold Neg_def)
  assume \<open>p \<longrightarrow> \<bottom>\<close> and p
  then have \<bottom> ..
  then show q ..
qed

definition Equality (infix \<open>=\<close> 50) where \<open>x = y \<equiv> \<forall>p. p x \<longrightarrow> p y\<close>

lemma Equality_I [intro]: \<open>x = x\<close>
proof (unfold Equality_def)
  show \<open>\<forall>p. p x \<longrightarrow> p x\<close>
  proof
    fix p
    show \<open>p x \<longrightarrow> p x\<close> ..
  qed
qed

lemma Equality_E1 [elim]: \<open>x = y \<Longrightarrow> p x \<Longrightarrow> p y\<close>
proof (unfold Equality_def)
  assume \<open>\<forall>p. p x \<longrightarrow> p y\<close> and \<open>p x\<close>
  from \<open>\<forall>p. p x \<longrightarrow> p y\<close> have \<open>p x \<longrightarrow> p y\<close> ..
  from this and \<open>p x\<close> show \<open>p y\<close> ..
qed

lemma Equality_E2 [elim]: \<open>x = y \<Longrightarrow> p y \<Longrightarrow> p x\<close>
proof -
  assume \<open>x = y\<close> and \<open>p y\<close>
  have \<open>x = x\<close> ..
  with \<open>x = y\<close> have \<open>y = x\<close> ..
  from this and \<open>p y\<close> show \<open>p x\<close> ..
qed

lemma Equality_1E [elim]: \<open>p x \<Longrightarrow> x = y \<Longrightarrow> p y\<close>
  by (rule Equality_E1)

lemma Equality_2E [elim]: \<open>p y \<Longrightarrow> x = y \<Longrightarrow> p x\<close>
  by (rule Equality_E2)

theorem Cantor: \<open>\<not> (\<exists>f. \<forall>s :: 'a \<Rightarrow> bool. \<exists>x :: 'a. s = f x)\<close>
proof
  assume \<open>\<exists>f. \<forall>s :: 'a \<Rightarrow> bool. \<exists>x :: 'a. s = f x\<close>
  then obtain f where \<open>\<forall>s :: 'a \<Rightarrow> bool. \<exists>x :: 'a. s = f x\<close> ..
  let ?D = \<open>\<lambda>x. \<not> f x x\<close>
  from \<open>\<forall>s. \<exists>x. s = f x\<close> have \<open>\<exists>x. ?D = f x\<close> ..
  then obtain c where \<open>?D = f c\<close> ..
  let ?P = \<open>f c c\<close>
  have \<open>?D c = ?D c\<close> ..
  from this and \<open>?D = f c\<close> have \<open>?D c = ?P\<close> ..
  have \<open>?D c\<close>
  proof
    assume ?P
    with \<open>?D c = ?P\<close> have \<open>?D c\<close> ..
    from this and \<open>?P\<close> show \<bottom> ..
  qed
  with \<open>?D c = ?P\<close> have ?P ..
  with \<open>?D c\<close> show \<bottom> ..
qed

definition Con (infixr \<open>\<and>\<close> 35) where \<open>p \<and> q \<equiv> \<forall>r. (p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> r\<close>

lemma Con_I [intro]: \<open>p \<Longrightarrow> q \<Longrightarrow> p \<and> q\<close>
proof (unfold Con_def)
  assume p and q
  show \<open>\<forall>r. (p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> r\<close>
  proof
    fix r
    show \<open>(p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> r\<close>
    proof
      assume \<open>p \<longrightarrow> q \<longrightarrow> r\<close>
      from this and \<open>p\<close> have \<open>q \<longrightarrow> r\<close> ..
      from this and \<open>q\<close> show r ..
    qed
  qed
qed

lemma Con_E1 [elim]: \<open>p \<and> q \<Longrightarrow> p\<close>
proof (unfold Con_def)
  assume \<open>\<forall>r. (p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> r\<close>
  then have \<open>(p \<longrightarrow> q \<longrightarrow> p) \<longrightarrow> p\<close> ..
  have \<open>p \<longrightarrow> q \<longrightarrow> p\<close>
  proof
    assume p
    then show \<open>q \<longrightarrow> p\<close> ..
  qed
  with \<open>(p \<longrightarrow> q \<longrightarrow> p) \<longrightarrow> p\<close> show p ..
qed

lemma Con_E2 [elim]: \<open>p \<and> q \<Longrightarrow> q\<close>
proof (unfold Con_def)
  assume \<open>\<forall>r. (p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> r\<close>
  then have \<open>(p \<longrightarrow> q \<longrightarrow> q) \<longrightarrow> q\<close> ..
  have \<open>p \<longrightarrow> q \<longrightarrow> q\<close>
  proof
    show \<open>q \<longrightarrow> q\<close> ..
  qed
  with \<open>(p \<longrightarrow> q \<longrightarrow> q) \<longrightarrow> q\<close> show q ..
qed

definition Dis (infixr \<open>\<or>\<close> 30) where \<open>p \<or> q \<equiv> \<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close>

lemma Dis_I1 [intro]: \<open>p \<Longrightarrow> p \<or> q\<close>
proof (unfold Dis_def)
  assume p
  show \<open>\<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close>
  proof
    fix r
    show \<open>(p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close>
    proof
      assume \<open>p \<longrightarrow> r\<close>
      from this and \<open>p\<close> have r ..
      then show \<open>(q \<longrightarrow> r) \<longrightarrow> r\<close> ..
    qed
  qed
qed

lemma Dis_I2 [intro]: \<open>q \<Longrightarrow> p \<or> q\<close>
proof (unfold Dis_def)
  assume q
  show \<open>\<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close>
  proof
    fix r
    show \<open>(p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close>
    proof
      show \<open>(q \<longrightarrow> r) \<longrightarrow> r\<close>
      proof
        assume \<open>q \<longrightarrow> r\<close>
        from this and \<open>q\<close> show r ..
      qed
    qed
  qed
qed

lemma Dis_E [elim]: \<open>p \<or> q \<Longrightarrow> (p \<Longrightarrow> r) \<Longrightarrow> (q \<Longrightarrow> r) \<Longrightarrow> r\<close>
proof (unfold Dis_def)
  assume \<open>\<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close> and \<open>p \<Longrightarrow> r\<close> and \<open>q \<Longrightarrow> r\<close>
  from \<open>\<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close> have \<open>(p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close> ..
  from \<open>p \<Longrightarrow> r\<close> have \<open>p \<longrightarrow> r\<close> ..
  with \<open>(p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r\<close> have \<open>(q \<longrightarrow> r) \<longrightarrow> r\<close> ..
  from \<open>q \<Longrightarrow> r\<close> have \<open>q \<longrightarrow> r\<close> ..
  with \<open>(q \<longrightarrow> r) \<longrightarrow> r\<close> show r ..
qed

abbreviation (input) Iff (infixr \<open>\<longleftrightarrow>\<close> 25) where \<open>p \<longleftrightarrow> q \<equiv> p = q\<close> for p :: bool

axiomatization where Iff_I [intro]: \<open>(p \<Longrightarrow> q) \<Longrightarrow> (q \<Longrightarrow> p) \<Longrightarrow> p \<longleftrightarrow> q\<close>

lemma Iff_E1 [elim]: \<open>p \<longleftrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>
  by (rule Equality_E1)

lemma Iff_E2 [elim]: \<open>p \<longleftrightarrow> q \<Longrightarrow> q \<Longrightarrow> p\<close>
  by (rule Equality_E2)

axiomatization where Extension: \<open>(\<And>x. f x = g x) \<Longrightarrow> f = g\<close> for f :: \<open>'a \<Rightarrow> 'b\<close>

axiomatization Epsilon (\<open>\<epsilon>\<close>) where Choice: \<open>p c \<Longrightarrow> p (\<epsilon> p)\<close> for c :: 'a

lemma Imp_C: \<open>(p \<longrightarrow> q \<Longrightarrow> p) \<Longrightarrow> p\<close>
proof -
  let ?F = \<open>\<lambda>q. q \<or> p \<and> \<not> q\<close> and ?G = \<open>\<lambda>q. p \<and> q \<or> \<not> q\<close>
  have \<open>?F (\<epsilon> ?F)\<close>
  proof (rule Choice)
    have \<top> ..
    then show \<open>?F \<top>\<close> ..
  qed
  have \<open>?G (\<epsilon> ?G)\<close>
  proof (rule Choice)
    have \<open>\<not> \<bottom>\<close> ..
    then show \<open>?G \<bottom>\<close> ..
  qed
  have \<open>p \<Longrightarrow> ?F = ?G\<close>
  proof -
    assume p
    show \<open>?F = ?G\<close>
    proof (rule Extension)
      fix q
      show \<open>?F q \<longleftrightarrow> ?G q\<close>
      proof
        assume \<open>?F q\<close>
        then have \<open>q \<or> p \<and> \<not> q\<close> .
        moreover have \<open>q \<Longrightarrow> p \<and> q \<or> \<not> q\<close>
        proof -
          assume q
          with \<open>p\<close> have \<open>p \<and> q\<close> ..
          then show \<open>p \<and> q \<or> \<not> q\<close> ..
        qed
        moreover have \<open>p \<and> \<not> q \<Longrightarrow> p \<and> q \<or> \<not> q\<close>
        proof -
          assume \<open>p \<and> \<not> q\<close>
          then have \<open>\<not> q\<close> ..
          then show \<open>p \<and> q \<or> \<not> q\<close> ..
        qed
        ultimately have \<open>p \<and> q \<or> \<not> q\<close> ..
        then show \<open>?G q\<close> .
      next
        assume \<open>?G q\<close>
        then have \<open>p \<and> q \<or> \<not> q\<close> .
        moreover have \<open>p \<and> q \<Longrightarrow> q \<or> p \<and> \<not> q\<close>
        proof -
          assume \<open>p \<and> q\<close>
          then have q ..
          then show \<open>q \<or> p \<and> \<not> q\<close> ..
        qed
        moreover have \<open>\<not> q \<Longrightarrow> q \<or> p \<and> \<not> q\<close>
        proof -
          assume \<open>\<not> q\<close>
          with \<open>p\<close> have \<open>p \<and> \<not> q\<close> ..
          then show \<open>q \<or> p \<and> \<not> q\<close> ..
        qed
        ultimately have \<open>q \<or> p \<and> \<not> q\<close> ..
        then show \<open>?F q\<close> .
      qed
    qed
  qed
  assume \<open>p \<longrightarrow> q \<Longrightarrow> p\<close>
  from \<open>?G (\<epsilon> ?G)\<close> have \<open>p \<and> \<epsilon> ?G \<or> \<not> \<epsilon> ?G\<close> .
  moreover have \<open>p \<and> \<epsilon> ?G \<Longrightarrow> p\<close>
  proof -
    assume \<open>p \<and> \<epsilon> ?G\<close>
    then show p ..
  qed
  moreover have \<open>\<not> \<epsilon> ?G \<Longrightarrow> p\<close>
  proof -
    assume \<open>\<not> \<epsilon> ?G\<close>
    from \<open>?F (\<epsilon> ?F)\<close> have \<open>\<epsilon> ?F \<or> p \<and> \<not> \<epsilon> ?F\<close> .
    moreover have \<open>\<epsilon> ?F \<Longrightarrow> p\<close>
    proof -
      assume \<open>\<epsilon> ?F\<close>
      have \<open>p \<longrightarrow> q\<close>
      proof
        assume p
        with \<open>p \<Longrightarrow> ?F = ?G\<close> have \<open>?F = ?G\<close> .
        with \<open>\<epsilon> ?F\<close> have \<open>\<epsilon> ?G\<close> ..
        with \<open>\<not> \<epsilon> ?G\<close> show q ..
      qed
      with \<open>p \<longrightarrow> q \<Longrightarrow> p\<close> show p .
    qed
    moreover have \<open>p \<and> \<not> \<epsilon> ?F \<Longrightarrow> p\<close>
    proof -
      assume \<open>p \<and> \<not> \<epsilon> ?F\<close>
      then show p ..
    qed
    ultimately show p ..
  qed
  ultimately show p ..
qed

lemma LEM: \<open>p \<or> \<not> p\<close>
proof (rule Imp_C)
  assume \<open>p \<or> \<not> p \<longrightarrow> \<bottom>\<close>
  have \<open>\<not> p\<close>
  proof
    assume p
    then have \<open>p \<or> \<not> p\<close> ..
    with \<open>p \<or> \<not> p \<longrightarrow> \<bottom>\<close> show \<bottom> ..
  qed
  then show \<open>p \<or> \<not> p\<close> ..
qed

lemma classical: \<open>(\<not> p \<Longrightarrow> p) \<Longrightarrow> p\<close>
proof -
  have \<open>p \<Longrightarrow> p\<close> .
  assume \<open>\<not> p \<Longrightarrow> p\<close>
  with LEM and \<open>p \<Longrightarrow> p\<close> show p ..
qed

lemma ccontr: \<open>(\<not> p \<Longrightarrow> \<bottom>) \<Longrightarrow> p\<close>
proof -
  assume \<open>\<not> p \<Longrightarrow> \<bottom>\<close>
  then have \<open>\<not> p \<Longrightarrow> p\<close> ..
  with classical show p .
qed

corollary not_not: \<open>\<not> \<not> p \<longleftrightarrow> p\<close>
proof
  assume \<open>\<not> \<not> p\<close>
  show p
  proof (rule ccontr)
    assume \<open>\<not> p\<close>
    with \<open>\<not> \<not> p\<close> show \<bottom> ..
  qed
next
  assume p
  show \<open>\<not> \<not> p\<close>
  proof
    assume \<open>\<not> p\<close>
    from this and \<open>p\<close> show \<bottom> ..
  qed
qed

axiomatization undefined :: 'a

typedecl ind

axiomatization Zero (\<open>0\<close>) and Suc :: \<open>ind \<Rightarrow> ind\<close>
  where Infinity_Base: \<open>Suc x = 0 \<Longrightarrow> p\<close>
    and Infinity_Step: \<open>Suc x = Suc y \<Longrightarrow> x = y\<close>

theorem No_Other_Zero: \<open>\<not> Suc x = 0\<close>
proof
  assume \<open>Suc x = 0\<close>
  with Infinity_Base show \<bottom> .
qed

corollary No_Other_Zero_Exists: \<open>\<not> (\<exists>x. Suc x = 0)\<close>
proof
  assume \<open>\<exists>x. Suc x = 0\<close>
  then obtain c where \<open>Suc c = 0\<close> ..
  with No_Other_Zero show \<bottom> ..
qed

typedecl 'a set

axiomatization Collect and Member :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<in>\<close> 51)
  where Comprehension: \<open>x \<in> Collect p \<longleftrightarrow> p x\<close>
    and Set_Reduction: \<open>Collect (\<lambda>x. x \<in> s) = s\<close>

theorem No_Member_Empty_Set: \<open>\<not> x \<in> Collect (\<lambda>_. \<bottom>)\<close>
proof
  assume \<open>x \<in> Collect (\<lambda>_. \<bottom>)\<close>
  with Comprehension show \<bottom> ..
qed

corollary No_Member_Empty_Set_Exists: \<open>\<not> (\<exists>x. x \<in> Collect (\<lambda>_. \<bottom>))\<close>
proof
  assume \<open>\<exists>x. x \<in> Collect (\<lambda>_ :: 'a. \<bottom>)\<close>
  then obtain c where \<open>c \<in> Collect (\<lambda>_ :: 'a. \<bottom>)\<close> ..
  with No_Member_Empty_Set show \<bottom> ..
qed

end
