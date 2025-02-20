section \<open>Proof Systems for First-Order Logic - Refining the Natural Deduction Assistant (NaDeA)\<close>

theory MainProof imports Main begin

section \<open>Natural Deduction\<close>

subsection \<open>Syntax\<close>

type_synonym id = nat

datatype tm = Var nat | Fun id \<open>tm list\<close>

datatype fm = Falsity | Pre id \<open>tm list\<close> | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm

subsection \<open>Semantics\<close>

primrec
  semantics_term :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a\<close> and
  semantics_list :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list\<close> where
  \<open>semantics_term e f (Var n) = e n\<close> |
  \<open>semantics_term e f (Fun i l) = f i (semantics_list e f l)\<close> |
  \<open>semantics_list e f [] = []\<close> |
  \<open>semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l\<close>

primrec
  semantics :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>semantics e f g Falsity = False\<close> |
  \<open>semantics e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>semantics e f g (Imp p q) = (if semantics e f g p then semantics e f g q else True)\<close> |
  \<open>semantics e f g (Dis p q) = (if semantics e f g p then True else semantics e f g q)\<close> |
  \<open>semantics e f g (Con p q) = (if semantics e f g p then semantics e f g q else False)\<close> |
  \<open>semantics e f g (Exi p) = (\<exists>x. semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p)\<close> |
  \<open>semantics e f g (Uni p) = (\<forall>x. semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p)\<close>

subsection \<open>Proof System\<close>

primrec member :: \<open>fm \<Rightarrow> fm list \<Rightarrow> bool\<close> where
  \<open>member p [] = False\<close> |
  \<open>member p (q # z) = (if p = q then True else member p z)\<close>

primrec
  new_term :: \<open>id \<Rightarrow> tm \<Rightarrow> bool\<close> and
  new_list :: \<open>id \<Rightarrow> tm list \<Rightarrow> bool\<close> where
  \<open>new_term c (Var n) = True\<close> |
  \<open>new_term c (Fun i l) = (if i = c then False else new_list c l)\<close> |
  \<open>new_list c [] = True\<close> |
  \<open>new_list c (t # l) = (if new_term c t then new_list c l else False)\<close>

primrec new :: \<open>id \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>new c Falsity = True\<close> |
  \<open>new c (Pre i l) = new_list c l\<close> |
  \<open>new c (Imp p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Dis p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Con p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Exi p) = new c p\<close> |
  \<open>new c (Uni p) = new c p\<close>

primrec news :: \<open>id \<Rightarrow> fm list \<Rightarrow> bool\<close> where
  \<open>news c [] = True\<close> |
  \<open>news c (p # z) = (if new c p then news c z else False)\<close>

primrec
  inc_term :: \<open>tm \<Rightarrow> tm\<close> and
  inc_list :: \<open>tm list \<Rightarrow> tm list\<close> where
  \<open>inc_term (Var n) = Var (n + 1)\<close> |
  \<open>inc_term (Fun i l) = Fun i (inc_list l)\<close> |
  \<open>inc_list [] = []\<close> |
  \<open>inc_list (t # l) = inc_term t # inc_list l\<close>

primrec
  sub_term :: \<open>nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm\<close> and
  sub_list :: \<open>nat \<Rightarrow> tm \<Rightarrow> tm list \<Rightarrow> tm list\<close> where
  \<open>sub_term v s (Var n) = (if n < v then Var n else if n = v then s else Var (n - 1))\<close> |
  \<open>sub_term v s (Fun i l) = Fun i (sub_list v s l)\<close> |
  \<open>sub_list v s [] = []\<close> |
  \<open>sub_list v s (t # l) = sub_term v s t # sub_list v s l\<close>

primrec sub :: \<open>nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm\<close> where
  \<open>sub v s Falsity = Falsity\<close> |
  \<open>sub v s (Pre i l) = Pre i (sub_list v s l)\<close> |
  \<open>sub v s (Imp p q) = Imp (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Dis p q) = Dis (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Con p q) = Con (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Exi p) = Exi (sub (v + 1) (inc_term s) p)\<close> |
  \<open>sub v s (Uni p) = Uni (sub (v + 1) (inc_term s) p)\<close>

abbreviation (input) \<open>subt t p \<equiv> sub 0 t p\<close>

abbreviation (input) \<open>inst c p \<equiv> subt (Fun c []) p\<close>

inductive natural_deduction :: \<open>fm list \<Rightarrow> fm \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<close> 0) where
  Assms: \<open>z \<leadsto> p\<close> if \<open>member p z\<close> |
  Fls_E: \<open>z \<leadsto> p\<close> if \<open>z \<leadsto> Falsity\<close> |
  Imp_E: \<open>z \<leadsto> q\<close> if \<open>z \<leadsto> Imp p q\<close> and \<open>z \<leadsto> p\<close> |
  Imp_I: \<open>z \<leadsto> Imp p q\<close> if \<open>p # z \<leadsto> q\<close> |
  Dis_E: \<open>z \<leadsto> r\<close> if \<open>z \<leadsto> Dis p q\<close> and \<open>p # z \<leadsto> r\<close> and \<open>q # z \<leadsto> r\<close> |
  Dis_I: \<open>z \<leadsto> Dis p q\<close> if \<open>z \<leadsto> p\<close> |
  Dis_J: \<open>z \<leadsto> Dis p q\<close> if \<open>z \<leadsto> q\<close> |
  Con_E: \<open>z \<leadsto> p\<close> if \<open>z \<leadsto> Con p q\<close> |
  Con_F: \<open>z \<leadsto> q\<close> if \<open>z \<leadsto> Con p q\<close> |
  Con_I: \<open>z \<leadsto> Con p q\<close> if \<open>z \<leadsto> p\<close> and \<open>z \<leadsto> q\<close> |
  Exi_E: \<open>z \<leadsto> q\<close> if \<open>z \<leadsto> Exi p\<close> and \<open>inst c p # z \<leadsto> q\<close> and \<open>news c (p # q # z)\<close> |
  Exi_I: \<open>z \<leadsto> Exi p\<close> if \<open>z \<leadsto> subt t p\<close> |
  Uni_E: \<open>z \<leadsto> subt t p\<close> if \<open>z \<leadsto> Uni p\<close> |
  Uni_I: \<open>z \<leadsto> Uni p\<close> if \<open>z \<leadsto> inst c p\<close> and \<open>news c (p # z)\<close> |
  Imp_C: \<open>z \<leadsto> p\<close> if \<open>Imp p q # z \<leadsto> p\<close>

subsection \<open>Soundness\<close>

lemma member [iff]: \<open>member p z \<longleftrightarrow> p \<in> set z\<close>
  by (induct z) simp_all

lemma symbols [simp]:
  \<open>(if p then q else True) = (p \<longrightarrow> q)\<close>
  \<open>(if p then True else q) = (p \<or> q)\<close>
  \<open>(if p then q else False) = (p \<and> q)\<close>
  by simp_all

fun put :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>put e v x = (\<lambda>n. if n < v then e n else if n = v then x else e (n - 1))\<close>

proposition \<open>put e 0 x = (\<lambda>n. if n = 0 then x else e (n - 1))\<close>
  by simp

proposition
  \<open>semantics e f g (Exi p) = (\<exists>x. semantics (put e 0 x) f g p)\<close>
  \<open>semantics e f g (Uni p) = (\<forall>x. semantics (put e 0 x) f g p)\<close>
  by simp_all

lemma increment:
  \<open>semantics_term (put e 0 x) f (inc_term t) = semantics_term e f t\<close>
  \<open>semantics_list (put e 0 x) f (inc_list l) = semantics_list e f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma commute: \<open>put (put e v x) 0 y = put (put e 0 y) (v + 1) x\<close>
  by fastforce

lemma allnew [simp]: \<open>list_all (new c) z = news c z\<close>
  by (induct z) simp_all

lemma map' [simp]:
  \<open>new_term n t \<Longrightarrow> semantics_term e (f(n := x)) t = semantics_term e f t\<close>
  \<open>new_list n l \<Longrightarrow> semantics_list e (f(n := x)) l = semantics_list e f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) auto

lemma map [simp]: \<open>new n p \<Longrightarrow> semantics e (f(n := x)) g p = semantics e f g p\<close>
  by (induct p arbitrary: e) simp_all

lemma allmap [simp]:
  \<open>news c z \<Longrightarrow> list_all (semantics e (f(c := m)) g) z = list_all (semantics e f g) z\<close>
  by (induct z) simp_all

lemma substitute' [simp]:
  \<open>semantics_term e f (sub_term v s t) = semantics_term (put e v (semantics_term e f s)) f t\<close>
  \<open>semantics_list e f (sub_list v s l) = semantics_list (put e v (semantics_term e f s)) f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma substitute [simp]:
  \<open>semantics e f g (sub v t p) = semantics (put e v (semantics_term e f t)) f g p\<close>
proof (induct p arbitrary: e v t)
  case (Exi p)
  have \<open>semantics e f g (sub v t (Exi p)) =
      (\<exists>x. semantics (put e 0 x) f g (sub (v + 1) (inc_term t) p))\<close>
    by simp
  also have \<open>\<dots> = (\<exists>x. semantics (put (put e 0 x) (v + 1)
      (semantics_term (put e 0 x) f (inc_term t))) f g p)\<close>
    using Exi by simp
  also have \<open>\<dots> = (\<exists>x. semantics (put (put e v (semantics_term e f t)) 0 x) f g p)\<close>
    using commute increment(1) by metis
  finally show ?case
    by simp
next
  case (Uni p)
  have \<open>semantics e f g (sub v t (Uni p)) =
      (\<forall>x. semantics (put e 0 x) f g (sub (v + 1) (inc_term t) p))\<close>
    by simp
  also have \<open>\<dots> =
      (\<forall>x. semantics (put (put e 0 x) (v + 1) (semantics_term (put e 0 x) f (inc_term t))) f g p)\<close>
    using Uni by simp
  also have \<open>\<dots> = (\<forall>x. semantics (put (put e v (semantics_term e f t)) 0 x) f g p)\<close>
    using commute increment(1) by metis
  finally show ?case
    by simp
qed simp_all

lemma natural_deduction_soundness: \<open>z \<leadsto> p \<Longrightarrow> list_all (semantics e f g) z \<Longrightarrow> semantics e f g p\<close>
proof (induct z p arbitrary: f rule: natural_deduction.induct)
  case (Exi_E z p c q)
  then obtain x where \<open>semantics (put e 0 x) f g p\<close>
    by auto
  then have \<open>semantics (put e 0 x) (f(c := \<lambda>w. x)) g p\<close>
    using \<open>news c (p # q # z)\<close> by simp
  then have \<open>semantics e (f(c := \<lambda>w. x)) g (inst c p)\<close>
    by simp
  then have \<open>list_all (semantics e (f(c := \<lambda>w. x)) g) (inst c p # z)\<close>
    using Exi_E by simp
  then have \<open>semantics e (f(c := \<lambda>w. x)) g q\<close>
    using Exi_E by blast
  then show \<open>semantics e f g q\<close>
    using \<open>news c (p # q # z)\<close> by simp
next
  case (Uni_I z c p)
  then have \<open>\<forall>x. list_all (semantics e (f(c := \<lambda>w. x)) g) z\<close>
    by simp
  then have \<open>\<forall>x. semantics e (f(c := \<lambda>w. x)) g (inst c p)\<close>
    using Uni_I by blast
  then have \<open>\<forall>x. semantics (put e 0 x) (f(c := \<lambda>w. x)) g p\<close>
    by simp
  then have \<open>\<forall>x. semantics (put e 0 x) f g p\<close>
    using \<open>news c (p # z)\<close> by simp
  then show \<open>semantics e f g (Uni p)\<close>
    by simp
qed (auto simp: list_all_iff)

abbreviation \<open>Neg p \<equiv> Imp p Falsity\<close>

abbreviation \<open>Truth \<equiv> Neg Falsity\<close>

abbreviation provable (\<open>\<turnstile> _\<close> 0) where \<open>(\<turnstile> p) \<equiv> ([] \<leadsto> p)\<close>

proposition \<open>\<turnstile> Truth\<close>
  using Assms Imp_I by (meson member.simps)

theorem soundness_provable: \<open>semantics e f g p\<close> if \<open>\<turnstile> p\<close>
  using natural_deduction_soundness that by fastforce

subsection \<open>Equivalent Proof System (NaDeA)\<close>

inductive OK where
  Assms: \<open>member p z \<Longrightarrow> OK p z\<close> |
  Imp_E: \<open>OK (Imp p q) z \<Longrightarrow> OK p z \<Longrightarrow> OK q z\<close> |
  Imp_I: \<open>OK q (p # z) \<Longrightarrow> OK (Imp p q) z\<close> |
  Dis_E: \<open>OK (Dis p q) z \<Longrightarrow> OK r (p # z) \<Longrightarrow> OK r (q # z) \<Longrightarrow> OK r z\<close> |
  Dis_I: \<open>OK p z \<Longrightarrow> OK (Dis p q) z\<close> |
  Dis_J: \<open>OK q z \<Longrightarrow> OK (Dis p q) z\<close> |
  Con_E: \<open>OK (Con p q) z \<Longrightarrow> OK p z\<close> |
  Con_F: \<open>OK (Con p q) z \<Longrightarrow> OK q z\<close> |
  Con_I: \<open>OK p z \<Longrightarrow> OK q z \<Longrightarrow> OK (Con p q) z\<close> |
  Exi_E: \<open>OK (Exi p) z \<Longrightarrow> OK q (inst c p # z) \<Longrightarrow> news c (p # q # z) \<Longrightarrow> OK q z\<close> |
  Exi_I: \<open>OK (subt t p) z \<Longrightarrow> OK (Exi p) z\<close> |
  Uni_E: \<open>OK (Uni p) z \<Longrightarrow> OK (subt t p) z\<close> |
  Uni_I: \<open>OK (inst c p) z \<Longrightarrow> news c (p # z) \<Longrightarrow> OK (Uni p) z\<close> |
  Boole: \<open>OK Falsity (Neg p # z) \<Longrightarrow> OK p z\<close>

lemmas
  Dis_I1 = Dis_I and
  Dis_I2 = Dis_J and
  Con_E1 = Con_E and
  Con_E2 = Con_F and
  Assume = Assms

lemma OK_to_natural_deduction: \<open>OK p z \<Longrightarrow> (z \<leadsto> p)\<close>
proof (induct p z rule: OK.induct)
  case Assms
  then show ?case
    using natural_deduction.Assms by blast
next
  case Imp_E
  then show ?case
    using natural_deduction.Imp_E by blast
next
  case Imp_I
  then show ?case
    using natural_deduction.Imp_I by blast
next
  case Dis_E
  then show ?case
    using natural_deduction.Dis_E by blast
next
  case Dis_I
  then show ?case
    using natural_deduction.Dis_I by blast
next
  case Dis_J
  then show ?case
    using natural_deduction.Dis_J by blast
next
  case Con_E
  then show ?case
    using natural_deduction.Con_E by blast
next
  case Con_F
  then show ?case
    using natural_deduction.Con_F by blast
next
  case Con_I
  then show ?case
    using natural_deduction.Con_I by blast
next
  case Exi_E
  then show ?case
    using natural_deduction.Exi_E by blast
next
  case Exi_I
  then show ?case
    using natural_deduction.Exi_I by blast
next
  case Uni_E
  then show ?case
    using natural_deduction.Uni_E by blast
next
  case Uni_I
  then show ?case
    using natural_deduction.Uni_I by blast
next
  case Boole
  then show ?case
    using Fls_E Imp_C by blast
qed

lemma Peirce: \<open>OK (Imp (Imp (Imp p q) p) p) z\<close>
proof (rule Imp_I)
  show \<open>OK p (Imp (Imp p q) p # z)\<close>
  proof (rule Boole)
    show \<open>OK Falsity (Neg p # Imp (Imp p q) p # z)\<close>
    proof (rule Imp_E)
      show \<open>OK (Neg p) (Neg p # Imp (Imp p q) p # z)\<close>
        by (rule Assume) simp
    next
      show \<open>OK p (Neg p # Imp (Imp p q) p # z)\<close>
      proof (rule Imp_E)
        show \<open>OK (Imp (Imp p q) p) (Neg p # Imp (Imp p q) p # z)\<close>
          by (rule Assume) simp
      next
        show \<open>OK (Imp p q) (Neg p # Imp (Imp p q) p # z)\<close>
        proof (rule Imp_I)
          show \<open>OK q (p # Neg p # Imp (Imp p q) p # z)\<close>
          proof (rule Boole)
            show \<open>OK Falsity (Neg q # p # Neg p # Imp (Imp p q) p # z)\<close>
            proof (rule Imp_E)
              show \<open>OK (Neg p) (Neg q # p # Neg p # Imp (Imp p q) p # z)\<close>
                by (rule Assume) simp
            next
              show \<open>OK p (Neg q # p # Neg p # Imp (Imp p q) p # z)\<close>
                by (rule Assume) simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma natural_deduction_to_OK: \<open>(z \<leadsto> p) \<Longrightarrow> OK p z\<close>
proof (induct z p rule: natural_deduction.induct)
  case Assms
  then show ?case
    using Assume by blast
next
  case Fls_E
  then show ?case
    using Assume Boole Imp_E Imp_I by (meson member.simps)
next
  case Imp_E
  then show ?case
    using OK.Imp_E by blast
next
  case Imp_I
  then show ?case
    using OK.Imp_I by blast
next
  case Dis_E
  then show ?case
    using OK.Dis_E by blast
next
  case Dis_I
  then show ?case
    using OK.Dis_I by blast
next
  case Dis_J
  then show ?case
    using OK.Dis_J by blast
next
  case Con_E
  then show ?case
    using OK.Con_E by blast
next
  case Con_F
  then show ?case
    using OK.Con_F by blast
next
  case Con_I
  then show ?case
    using OK.Con_I by blast
next
  case Exi_E
  then show ?case
    using OK.Exi_E by blast
next
  case Exi_I
  then show ?case
    using OK.Exi_I by blast
next
  case Uni_E
  then show ?case
    using OK.Uni_E by blast
next
  case Uni_I
  then show ?case
    using OK.Uni_I by blast
next
  case Imp_C
  then show ?case
    using Imp_E Imp_I Peirce by blast
qed

theorem OK_natural_deduction: \<open>OK p z = (z \<leadsto> p)\<close>
  using OK_to_natural_deduction natural_deduction_to_OK by blast

theorem soundness: \<open>OK p [] \<Longrightarrow> semantics e f g p\<close>
  using OK_natural_deduction soundness_provable by blast

corollary \<open>\<exists>p. OK p []\<close> \<open>\<exists>p. \<not> OK p []\<close>
proof -
  have \<open>OK (Imp p p) []\<close> for p
    by (rule Imp_I, rule Assume, simp)
  then show \<open>\<exists>p. OK p []\<close>
    by iprover
next
  have \<open>\<not> semantics (e :: _ \<Rightarrow> unit) f g Falsity\<close> for e f g
    by simp
  then show \<open>\<exists>p. \<not> OK p []\<close>
    using soundness by iprover
qed

section \<open>Appendix: Sequent Calculus\<close>

subsection \<open>Proof System\<close>

inductive sequent_calculus :: \<open>fm list \<Rightarrow> bool\<close> (\<open>\<tturnstile> _\<close> 0) where
  Basic: \<open>\<tturnstile> p # z\<close> if \<open>member (Neg p) z\<close> |
  Imp_R: \<open>\<tturnstile> Imp p q # z\<close> if \<open>\<tturnstile> Neg p # q # z\<close> |
  Imp_L: \<open>\<tturnstile> Neg (Imp p q) # z\<close> if \<open>\<tturnstile> p # z\<close> and \<open>\<tturnstile> Neg q # z\<close> |
  Dis_R: \<open>\<tturnstile> Dis p q # z\<close> if \<open>\<tturnstile> p # q # z\<close> |
  Dis_L: \<open>\<tturnstile> Neg (Dis p q) # z\<close> if \<open>\<tturnstile> Neg p # z\<close> and \<open>\<tturnstile> Neg q # z\<close> |
  Con_R: \<open>\<tturnstile> Con p q # z\<close> if \<open>\<tturnstile> p # z\<close> and \<open>\<tturnstile> q # z\<close> |
  Con_L: \<open>\<tturnstile> Neg (Con p q) # z\<close> if \<open>\<tturnstile> Neg p # Neg q # z\<close> |
  Exi_R: \<open>\<tturnstile> Exi p # z\<close> if \<open>\<tturnstile> subt t p # z\<close> |
  Exi_L: \<open>\<tturnstile> Neg (Exi p) # z\<close> if \<open>\<tturnstile> Neg (inst c p) # z\<close> and \<open>news c (p # z)\<close> |
  Uni_R: \<open>\<tturnstile> Uni p # z\<close> if \<open>\<tturnstile> inst c p # z\<close> and \<open>news c (p # z)\<close> |
  Uni_L: \<open>\<tturnstile> Neg (Uni p) # z\<close> if \<open>\<tturnstile> Neg (subt t p) # z\<close> |
  Extra: \<open>\<tturnstile> z\<close> if \<open>\<tturnstile> p # z\<close> and \<open>member p z\<close>

subsection \<open>Soundness\<close>

theorem sequent_calculus_soundness: \<open>\<tturnstile> z \<Longrightarrow> \<exists>p \<in> set z. semantics e f g p\<close>
proof (induct arbitrary: f rule: sequent_calculus.induct)
  case (Exi_L c p z)
  then consider
    \<open>\<forall>x. semantics e (f(c := \<lambda>w. x)) g (Neg (inst c p))\<close> |
    \<open>\<exists>x. \<exists>p \<in> set (Neg (Exi p) # z). semantics e (f(c := \<lambda>w. x)) g p\<close>
    by fastforce
  then show ?case
  proof cases
    case 1
    then have \<open>\<forall>x. semantics (put e 0 x) (f(c := \<lambda>w. x)) g (Neg p)\<close>
      by simp
    then have \<open>\<forall>x. semantics (put e 0 x) f g (Neg p)\<close>
      using \<open>news c (p # z)\<close> by simp
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using \<open>news c (p # z)\<close> by (metis Ball_set allnew map new.simps(1,3,6) news.simps(2))
  qed
next
  case (Uni_R c p z)
  then consider
    \<open>\<forall>x. semantics e (f(c := \<lambda>w. x)) g (inst c p)\<close> |
    \<open>\<exists>x. \<exists>p \<in> set (Uni p # z). semantics e (f(c := \<lambda>w. x)) g p\<close>
    by fastforce
  then show ?case
  proof cases
    case 1
    then have \<open>\<forall>x. semantics (put e 0 x) (f(c := \<lambda>w. x)) g p\<close>
      by simp
    then have \<open>\<forall>x. semantics (put e 0 x) f g p\<close>
      using \<open>news c (p # z)\<close> by simp
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using \<open>news c (p # z)\<close> by (metis Ball_set allnew map new.simps(7) news.simps(2))
  qed
qed force+

subsection \<open>Derived Rules\<close>

theorem Truth: \<open>\<tturnstile> Truth # z\<close>
  using Basic Extra Imp_R by (meson member.simps)

theorem NegNeg: \<open>\<tturnstile> Neg (Neg p) # z\<close> if \<open>\<tturnstile> p # z\<close>
  using Imp_L that Truth .

text \<open>MiniCalc uses the derived rule Ext instead of Extra and does not allow Falsity and Truth\<close>

end
