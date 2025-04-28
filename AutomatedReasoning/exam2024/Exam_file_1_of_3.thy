theory Exam_file_1_of_3 imports MiniCalc begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Use MiniCalc to prove the following formulas and include all "Copy Result to Clipboard" lines.

\<close>

proposition \<open>p \<longrightarrow> \<not> (p \<and> \<not> q) \<longrightarrow> q\<close>
  oops

proposition \<open>(\<forall>x. p x \<and> q x) \<longrightarrow> (\<exists>x. q x \<or> r x)\<close>
  oops

proposition \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
  oops

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

term \<open>p \<longrightarrow> ((\<not> (p \<and> (\<not> q))) \<longrightarrow> q)\<close>

term \<open>(\<forall>x. ((p x) \<and> (q x))) \<longrightarrow> (\<exists>x. ((q x) \<or> (r x)))\<close>

term \<open>((p (f a b c)) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. (\<forall>y. (r x y))))\<close>

section \<open>Formula 1\<close>

proposition \<open>p \<longrightarrow> ((\<not> (p \<and> (\<not> q))) \<longrightarrow> q)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 []) (Imp (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))) (Pre 1 []))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Imp (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))) (Pre 1 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 []) (Neg (Pre 1 [])),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 []),
      Pre 1 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 2\<close>

proposition \<open>(\<forall>x. ((p x) \<and> (q x))) \<longrightarrow> (\<exists>x. ((q x) \<or> (r x)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
    2 = r
  Function numbers
    0 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0]))) (Exi (Dis (Pre 1 [Var 0]) (Pre 2 [Var 0])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0]))),
      Exi (Dis (Pre 1 [Var 0]) (Pre 2 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Dis (Pre 1 [Var 0]) (Pre 2 [Var 0])),
      Neg (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Dis (Pre 1 [Fun 0 []]) (Pre 2 [Fun 0 []]),
      Neg (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Pre 2 [Fun 0 []],
      Neg (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0]))),
      Pre 1 [Fun 0 []],
      Pre 2 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []])),
      Pre 1 [Fun 0 []],
      Pre 2 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with Con_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []]),
      Pre 1 [Fun 0 []],
      Pre 2 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 3\<close>

proposition \<open>((p (f a b c)) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. (\<forall>y. (r x y))))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
    2 = r
  Function numbers
    0 = f
    1 = a
    2 = b
    3 = c
  \<close>

lemma \<open>\<tturnstile>
  [
    Dis (Imp (Pre 0 [Fun 0 [Fun 1 [], Fun 2 [], Fun 3 []]]) (Pre 1 [])) (Imp (Pre 1 []) (Exi (Uni (Pre 2 [Var 1, Var 0]))))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 0 [Fun 1 [], Fun 2 [], Fun 3 []]]) (Pre 1 []),
      Imp (Pre 1 []) (Exi (Uni (Pre 2 [Var 1, Var 0])))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 1 [], Fun 2 [], Fun 3 []]]),
      Pre 1 [],
      Imp (Pre 1 []) (Exi (Uni (Pre 2 [Var 1, Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 1 []) (Exi (Uni (Pre 2 [Var 1, Var 0]))),
      Neg (Pre 0 [Fun 0 [Fun 1 [], Fun 2 [], Fun 3 []]]),
      Pre 1 []
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Exi (Uni (Pre 2 [Var 1, Var 0])),
      Neg (Pre 0 [Fun 0 [Fun 1 [], Fun 2 [], Fun 3 []]]),
      Pre 1 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

# "Formula 1"

(* p \<longrightarrow> ((\<not> (p \<and> (\<not> q))) \<longrightarrow> q) *)

Imp p (Imp (Neg (Con p (Neg q))) q)

Imp_R
  Neg p
  Imp (Neg (Con p (Neg q))) q
Ext
  Imp (Neg (Con p (Neg q))) q
  Neg p
Imp_R
  Neg (Neg (Con p (Neg q)))
  q
  Neg p
NegNeg
  Con p (Neg q)
  q
  Neg p
Con_R
  p
  q
  Neg p
+
  Neg q
  q
  Neg p
Ext
  p
  Neg p
  q
+
  q
  Neg q
  Neg p
Basic

# "Formula 2"

(* (\<forall>x. ((p x) \<and> (q x))) \<longrightarrow> (\<exists>x. ((q x) \<or> (r x))) *)

Imp (Uni (Con p[0] q[0])) (Exi (Dis q[0] r[0]))

Imp_R
  Neg (Uni (Con p[0] q[0]))
  Exi (Dis q[0] r[0])
Ext
  Exi (Dis q[0] r[0])
  Neg (Uni (Con p[0] q[0]))
Exi_R[a]
  Dis q[a] r[a]
  Neg (Uni (Con p[0] q[0]))
Dis_R
  q[a]
  r[a]
  Neg (Uni (Con p[0] q[0]))
Ext
  Neg (Uni (Con p[0] q[0]))
  q[a]
  r[a]
Uni_L[a]
  Neg (Con p[a] q[a])
  q[a]
  r[a]
Con_L
  Neg p[a]
  Neg q[a]
  q[a]
  r[a]
Ext
  q[a]
  Neg q[a]
Basic

# "Formula 3"

(* ((p (f a b c)) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. (\<forall>y. (r x y)))) *)

Dis (Imp p[f[a, b, c]] q) (Imp q (Exi (Uni r[1, 0])))

Dis_R
  Imp p[f[a, b, c]] q
  Imp q (Exi (Uni r[1, 0]))
Imp_R
  Neg p[f[a, b, c]]
  q
  Imp q (Exi (Uni r[1, 0]))
Ext
  Imp q (Exi (Uni r[1, 0]))
  Neg p[f[a, b, c]]
  q
Imp_R
  Neg q
  Exi (Uni r[1, 0])
  Neg p[f[a, b, c]]
  q
Ext
  q
  Neg q
Basic

*)

end
