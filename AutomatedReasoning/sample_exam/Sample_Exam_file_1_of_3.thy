theory Sample_Exam_file_1_of_3 imports MiniCalc begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Use MiniCalc to prove the following formulas and include all "Copy Result to Clipboard" lines.

\<close>

proposition \<open>(p \<longrightarrow> \<not> p) \<longrightarrow> \<not> p\<close>
  by metis

proposition \<open>\<exists>x. p x \<longrightarrow> (\<forall>x. p x)\<close>
  by metis

proposition \<open>\<not> (\<exists>x. p (f x)) \<longrightarrow> (\<forall>x. \<not> p (f x))\<close>
  by metis

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

term \<open>(p \<longrightarrow> (\<not> p)) \<longrightarrow> (\<not> p)\<close>

term \<open>\<exists>x. ((p x) \<longrightarrow> (\<forall>y. (p y)))\<close>

term \<open>(\<not> (\<exists>x. (p (f x)))) \<longrightarrow> (\<forall>x. (\<not> (p (f x))))\<close>

section \<open>Proposition 1\<close>

proposition \<open>(p \<longrightarrow> (\<not> p)) \<longrightarrow> (\<not> p)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre 0 []) (Neg (Pre 0 []))) (Neg (Pre 0 []))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Neg (Pre 0 []))),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Neg (Pre 0 [])),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Pre 0 [])),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Proposition 2\<close>

proposition \<open>\<exists>x. ((p x) \<longrightarrow> (\<forall>y. (p y)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = a
    1 = b
  \<close>

lemma \<open>\<tturnstile>
  [
    Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0])))
  ]
  \<close>
proof -
  from Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0]))),
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0])),
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Uni (Pre 0 [Var 0]),
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Pre 0 [Var 0]),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Uni_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 0 []]),
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Imp (Pre 0 [Var 0]) (Uni (Pre 0 [Var 0]))),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 1 []]) (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 []]),
      Uni (Pre 0 [Var 0]),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Proposition 3\<close>

proposition \<open>(\<not> (\<exists>x. (p (f x)))) \<longrightarrow> (\<forall>x. (\<not> (p (f x))))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = f
    1 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Neg (Exi (Pre 0 [Fun 0 [Var 0]]))) (Uni (Neg (Pre 0 [Fun 0 [Var 0]])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Exi (Pre 0 [Fun 0 [Var 0]]))),
      Uni (Neg (Pre 0 [Fun 0 [Var 0]]))
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 0 [Fun 0 [Var 0]]),
      Uni (Neg (Pre 0 [Fun 0 [Var 0]]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Neg (Pre 0 [Fun 0 [Var 0]])),
      Exi (Pre 0 [Fun 0 [Var 0]])
    ]
    \<close>
    using that by simp
  with Uni_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 1 []]]),
      Exi (Pre 0 [Fun 0 [Var 0]])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 0 [Fun 0 [Var 0]]),
      Neg (Pre 0 [Fun 0 [Fun 1 []]])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 1 []]],
      Neg (Pre 0 [Fun 0 [Fun 1 []]])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

# "Proposition 1"

(* (p \<longrightarrow> (\<not> p)) \<longrightarrow> (\<not> p) *)

Imp (Imp p (Neg p)) (Neg p)

Imp_R
  Neg (Imp p (Neg p))
  Neg p
Imp_L
  p
  Neg p
+
  Neg (Neg p)
  Neg p
Basic
  Neg (Neg p)
  Neg p
NegNeg
  p
  Neg p
Basic

# "Proposition 2"

(* \<exists>x. ((p x) \<longrightarrow> (\<forall>y. (p y))) *)

Exi (Imp p[0] (Uni p[0]))

Ext
  Exi (Imp p[0] (Uni p[0]))
  Exi (Imp p[0] (Uni p[0]))
Exi_R[a]
  Imp p[a] (Uni p[0])
  Exi (Imp p[0] (Uni p[0]))
Imp_R
  Neg p[a]
  Uni p[0]
  Exi (Imp p[0] (Uni p[0]))
Ext
  Uni p[0]
  Neg p[a]
  Exi (Imp p[0] (Uni p[0]))
Uni_R
  p[b]
  Neg p[a]
  Exi (Imp p[0] (Uni p[0]))
Ext
  Exi (Imp p[0] (Uni p[0]))
  p[b]
Exi_R[b]
  Imp p[b] (Uni p[0])
  p[b]
Imp_R
  Neg p[b]
  Uni p[0]
  p[b]
Ext
  p[b]
  Neg p[b]
Basic

# "Proposition 3"

(* (\<not> (\<exists>x. (p (f x)))) \<longrightarrow> (\<forall>x. (\<not> (p (f x)))) *)

Imp (Neg (Exi p[f[0]])) (Uni (Neg p[f[0]]))

Imp_R
  Neg (Neg (Exi p[f[0]]))
  Uni (Neg p[f[0]])
NegNeg
  Exi p[f[0]]
  Uni (Neg p[f[0]])
Ext
  Uni (Neg p[f[0]])
  Exi p[f[0]]
Uni_R
  Neg p[f[a]]
  Exi p[f[0]]
Ext
  Exi p[f[0]]
  Neg p[f[a]]
Exi_R[a]
  p[f[a]]
  Neg p[f[a]]
Basic

*)

end
