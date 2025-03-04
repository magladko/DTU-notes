theory Propositional_Logic_Super imports Main begin

datatype form =
  Falsity (\<open>\<bottom>\<close>) |
  Pro nat (\<open>\<cdot>\<close>) |
  (* Neg form (\<open>\<sim>\<close>) | *)
  Imp form form (infixr \<open>\<rightarrow>\<close> 100)

primrec semantics (infix \<open>\<Turnstile>\<close> 50) where
  \<open>I \<Turnstile> \<bottom> = False\<close> |
  \<open>I \<Turnstile> \<cdot>n = I n\<close> |
  (* \<open>I \<Turnstile> \<sim> p = (\<not> I \<Turnstile> p)\<close> | *)
  \<open>I \<Turnstile> p \<rightarrow> q = (I \<Turnstile> p \<longrightarrow> I \<Turnstile> q)\<close>

abbreviation sc (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>I\<rbrakk> X Y \<equiv> (\<forall>p \<in> set X. I \<Turnstile> p) \<longrightarrow> (\<exists>q \<in> set Y. I \<Turnstile> q)\<close>

inductive SC (infix \<open>\<then>\<close> 50) where
  Fls_L: \<open>\<bottom> # _ \<then> _\<close> |
  (* Neg_L: \<open>\<sim> p # X \<then> Y\<close> if \<open>X \<then> p # Y\<close> | *)
  (* Neg_R: \<open>X \<then> \<sim> p # Y\<close> if \<open>p # X \<then> Y\<close> | *)
  Imp_L: \<open>p \<rightarrow> q # X \<then> Y\<close> if \<open>X \<then> p # Y\<close> and \<open>q # X \<then> Y\<close> |
  Imp_R: \<open>X \<then> p \<rightarrow> q # Y\<close> if \<open>p # X \<then> q # Y\<close> |
  Set_L: \<open>X' \<then> Y\<close> if \<open>X \<then> Y\<close> and \<open>set X' = set X\<close> |
  Set_R: \<open>X \<then> Y'\<close> if \<open>X \<then> Y\<close> and \<open>set Y' = set Y\<close> |
  Basic: \<open>p # _ \<then> p # _\<close>

function mp where
  \<open>mp _ _ (\<bottom> # _) [] = True\<close> |
  \<open>mp A B C (\<bottom> # D) = mp A B C D\<close> |
  (* \<open>mp A B (\<sim> p # C) [] = mp A B C [p]\<close> | *)
  (* \<open>mp A B C (\<sim> p # D) = mp A B (p # C) D\<close> | *)
  \<open>mp A B (p \<rightarrow> q # C) [] = (mp A B C [p] \<and> mp A B (q # C) [])\<close> |
  \<open>mp A B C (p \<rightarrow> q # D) = mp A B (p # C) (q # D)\<close> |
  \<open>mp A B [] [] = (set A \<inter> set B \<noteq> {})\<close> |
  \<open>mp A B (\<cdot>n # C) [] = mp (n # A) B C []\<close> |
  \<open>mp A B C (\<cdot>n # D) = mp A (n # B) C D\<close>
  by pat_completeness simp_all

termination
  by (relation \<open>measure (\<lambda>(_, _, C, D). 2 * (\<Sum>p \<leftarrow> C @ D. size p) + size (C @ D))\<close>) simp_all

lemma main: \<open>(\<forall>I. \<lbrakk>I\<rbrakk> (map \<cdot> A @ C) (map \<cdot> B @ D)) \<longleftrightarrow> mp A B C D\<close>
  by (induct rule: mp.induct) (auto 5 2)

definition prover (\<open>\<turnstile>\<close>) where \<open>\<turnstile> p \<equiv> mp [] [] [] [p]\<close>

theorem prover_correct: \<open>\<turnstile> p \<longleftrightarrow> (\<forall>I. I \<Turnstile> p)\<close>
  unfolding prover_def by (simp flip: main)

export_code \<turnstile> in SML

lemma MP: \<open>mp A B C D \<Longrightarrow> set X \<supseteq> set (map \<cdot> A @ C) \<Longrightarrow> set Y \<supseteq> set (map \<cdot> B @ D) \<Longrightarrow> X \<then> Y\<close>
proof (induct A B C D arbitrary: X Y rule: mp.induct[case_names Fls_L Fls_R (* Neg_L Neg_R *) Imp_L Imp_R Basic])
  case Fls_L
  then show ?case
    using SC.Fls_L Set_L by fastforce
(*
next
  case (Neg_L A B p C)
  have \<open>set (map \<cdot> A @ C) \<subseteq> set X\<close> \<open>set (map \<cdot> B) \<subseteq> set (p # Y)\<close>
    using Neg_L(3,4) by auto
  then have \<open>\<sim> p # X \<then> Y\<close>
    using Neg_L(1,2) SC.Neg_L by simp
  then show ?case
    using Neg_L(3) Set_L by fastforce
next
  case (Neg_R A B C p D)
  have \<open>set (map \<cdot> A @ C) \<subseteq> set (p # X)\<close> \<open>set (map \<cdot> B @ D) \<subseteq> set Y\<close>
    using Neg_R(3,4) by auto
  then have \<open>X \<then> \<sim> p # Y\<close>
    using Neg_R(1,2) SC.Neg_R by simp
  then show ?case
    using Neg_R(4) Set_R by fastforce
*)
next
  case (Imp_L A B p q C)
  have \<open>set (map \<cdot> A @ C) \<subseteq> set X\<close> \<open>set (map \<cdot> B) \<subseteq> set Y\<close>
    using Imp_L(4,5) by auto
  moreover from this have \<open>set (map \<cdot> A @ C) \<subseteq> set (q # X)\<close> \<open>set (map \<cdot> B) \<subseteq> set (p # Y)\<close>
    by auto
  ultimately have \<open>p \<rightarrow> q # X \<then> Y\<close>
    using Imp_L(1-3) SC.Imp_L by simp
  then show ?case
    using Imp_L(4) Set_L by fastforce
next
  case (Imp_R A B C p q D)
  have \<open>set (map \<cdot> A @ C) \<subseteq> set (p # X)\<close> \<open>set (map \<cdot> B @ D) \<subseteq> set (q # Y)\<close>
    using Imp_R(3,4) by auto
  then have \<open>X \<then> p \<rightarrow> q # Y\<close>
    using Imp_R(1,2) SC.Imp_R by simp
  then show ?case
    using Imp_R(4) Set_R by fastforce
next
  case (Basic A B)
  obtain n where \<open>n \<in> set A\<close> \<open>n \<in> set B\<close>
    using Basic(1) by auto
  then have \<open>set (\<cdot>n # X) = set X\<close> \<open>set (\<cdot>n # Y) = set Y\<close>
    using Basic(2,3) by auto
  then show ?case
    using Set_L Set_R SC.Basic by metis
qed simp_all

theorem OK: \<open>(\<forall>I. \<lbrakk>I\<rbrakk> X Y) \<longleftrightarrow> X \<then> Y\<close>
  by (rule, use MP main[of \<open>[]\<close> _ \<open>[]\<close> _] in simp, induct rule: SC.induct) auto

corollary \<open>[] \<then> [p] \<longleftrightarrow> (\<forall>I. I \<Turnstile> p)\<close>
  using OK by force

proposition \<open>[] \<then> [p \<rightarrow> p]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p] \<then> [p]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [p \<rightarrow> (p \<rightarrow> q) \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p] \<then> [(p \<rightarrow> q) \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p \<rightarrow> q, p] \<then> [q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, q]\<close> and \<open>[q, p] \<then> [q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [p \<rightarrow> q \<rightarrow> q \<rightarrow> p]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p] \<then> [q \<rightarrow> q \<rightarrow> p]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[q, p] \<then> [q \<rightarrow> p]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[q, q, p] \<then> [p]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p, q] \<then> [p]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

abbreviation Neg (\<open>\<sim>\<close>) where \<open>\<sim> p \<equiv> p \<rightarrow> \<bottom>\<close>

proposition \<open>I \<Turnstile> \<sim> p = (\<not> I \<Turnstile> p)\<close> 
  by simp 

lemma *: \<open>(\<forall>I. \<lbrakk>I\<rbrakk> X Y) \<longleftrightarrow> (\<forall>I. \<lbrakk>I\<rbrakk> X (\<bottom> # Y))\<close> 
  by simp 

lemma Fls_R: \<open>X \<then> p # Y\<close> if \<open>X \<then> Y\<close> 
  using that * OK list.set_intros 
  by meson 

lemma Neg_L: \<open>\<sim> p # X \<then> Y\<close> if \<open>X \<then> p # Y\<close> 
  using that Fls_L Imp_L 
  by simp

lemma Neg_R: \<open>X \<then> \<sim> p # Y\<close> if \<open>p # X \<then> Y\<close> 
  using that Fls_R Imp_R 
  by simp

end
