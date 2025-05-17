theory Exam_file_1_of_3 imports MiniCalc begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Use MiniCalc to prove the following formulas and include all "Copy Result to Clipboard" lines.

\<close>

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> (\<not> p \<longrightarrow> q) \<longrightarrow> q\<close>
  by metis

proposition \<open>(\<forall>x. p x) \<and> q a \<longrightarrow> p a \<and> (\<exists>x. q x)\<close>
  by metis

proposition \<open>(\<exists>x. \<forall>y. p x y) \<longrightarrow> (\<exists>x. p x a \<or> q a x)\<close>
  by metis

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

term \<open>(p \<longrightarrow> q) \<longrightarrow> (((\<not> p) \<longrightarrow> q) \<longrightarrow> q)\<close>

term \<open>((\<forall>x. (p x)) \<and> (q a)) \<longrightarrow> ((p a) \<and> (\<exists>x. (q x)))\<close>

term \<open>(\<exists>x. (\<forall>y. (p x y))) \<longrightarrow> (\<exists>x. ((p x a) \<or> (q a x)))\<close>

section \<open>Proposition 1\<close>

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> (((\<not> p) \<longrightarrow> q) \<longrightarrow> q)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre 0 []) (Pre 1 [])) (Imp (Imp (Neg (Pre 0 [])) (Pre 1 [])) (Pre 1 []))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Imp (Imp (Neg (Pre 0 [])) (Pre 1 [])) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp (Neg (Pre 0 [])) (Pre 1 [])) (Pre 1 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [])) (Pre 1 [])),
      Pre 1 [],
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 1 [],
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Pre 1 [],
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 1 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 1 []
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 []),
      Pre 1 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Neg (Pre 0 []),
      Pre 1 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Proposition 2\<close>

proposition \<open>((\<forall>x. (p x)) \<and> (q a)) \<longrightarrow> ((p a) \<and> (\<exists>x. (q x)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  Function numbers
    0 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Con (Uni (Pre 0 [Var 0])) (Pre 1 [Fun 0 []])) (Con (Pre 0 [Fun 0 []]) (Exi (Pre 1 [Var 0])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Uni (Pre 0 [Var 0])) (Pre 1 [Fun 0 []])),
      Con (Pre 0 [Fun 0 []]) (Exi (Pre 1 [Var 0]))
    ]
    \<close>
    using that by simp
  with Con_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Neg (Pre 1 [Fun 0 []]),
      Con (Pre 0 [Fun 0 []]) (Exi (Pre 1 [Var 0]))
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []]),
      Con (Pre 0 [Fun 0 []]) (Exi (Pre 1 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 0 []]) (Exi (Pre 1 [Var 0])),
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Pre 1 [Var 0]),
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 1 [Var 0]),
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []]),
      Neg (Pre 1 [Fun 0 []])
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

section \<open>Proposition 3\<close>

proposition \<open>(\<exists>x. (\<forall>y. (p x y))) \<longrightarrow> (\<exists>x. ((p x a) \<or> (q a x)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  Function numbers
    0 = a
    1 = b
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Exi (Uni (Pre 0 [Var 1, Var 0]))) (Exi (Dis (Pre 0 [Var 0, Fun 0 []]) (Pre 1 [Fun 0 [], Var 0])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Uni (Pre 0 [Var 1, Var 0]))),
      Exi (Dis (Pre 0 [Var 0, Fun 0 []]) (Pre 1 [Fun 0 [], Var 0]))
    ]
    \<close>
    using that by simp
  with Exi_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Fun 1 [], Var 0])),
      Exi (Dis (Pre 0 [Var 0, Fun 0 []]) (Pre 1 [Fun 0 [], Var 0]))
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 [], Fun 0 []]),
      Exi (Dis (Pre 0 [Var 0, Fun 0 []]) (Pre 1 [Fun 0 [], Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Dis (Pre 0 [Var 0, Fun 0 []]) (Pre 1 [Fun 0 [], Var 0])),
      Neg (Pre 0 [Fun 1 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Dis (Pre 0 [Fun 1 [], Fun 0 []]) (Pre 1 [Fun 0 [], Fun 1 []]),
      Neg (Pre 0 [Fun 1 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 [], Fun 0 []],
      Pre 1 [Fun 0 [], Fun 1 []],
      Neg (Pre 0 [Fun 1 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 [], Fun 0 []],
      Neg (Pre 0 [Fun 1 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

# "Proposition 1"

(* (p \<longrightarrow> q) \<longrightarrow> (((\<not> p) \<longrightarrow> q) \<longrightarrow> q) *)

Imp (Imp p q) (Imp (Imp (Neg p) q) q)

Imp_R
  Neg (Imp p q)
  Imp (Imp (Neg p) q) q
Ext
  Imp (Imp (Neg p) q) q
  Neg (Imp p q)
Imp_R
  Neg (Imp (Neg p) q)
  q
  Neg (Imp p q)
Imp_L
  Neg p
  q
  Neg (Imp p q)
+
  Neg q
  q
  Neg (Imp p q)
Ext
  Neg (Imp p q)
  Neg p
  q
+
  q
  Neg q
  Neg (Imp p q)
Basic
  Neg (Imp p q)
  Neg p
  q
Imp_L
  p
  Neg p
  q
+
  Neg q
  Neg p
  q
Ext
  p
  Neg p
+
  q
  Neg q
Basic

# "Proposition 2"

(* ((\<forall>x. (p x)) \<and> (q a)) \<longrightarrow> ((p a) \<and> (\<exists>x. (q x))) *)

Imp (Con (Uni p[0]) q[a]) (Con p[a] (Exi q[0]))

Imp_R
  Neg (Con (Uni p[0]) q[a])
  Con p[a] (Exi q[0])
Con_L
  Neg (Uni p[0])
  Neg q[a]
  Con p[a] (Exi q[0])
Uni_L[a]
  Neg p[a]
  Neg q[a]
  Con p[a] (Exi q[0])
Ext
  Con p[a] (Exi q[0])
  Neg p[a]
  Neg q[a]
Con_R
  p[a]
  Neg p[a]
  Neg q[a]
+
  Exi q[0]
  Neg p[a]
  Neg q[a]
Basic
  Exi q[0]
  Neg p[a]
  Neg q[a]
Exi_R[a]
  q[a]
  Neg p[a]
  Neg q[a]
Ext
  q[a]
  Neg q[a]
Basic

# "Proposition 3"

(* (\<exists>x. (\<forall>y. (p x y))) \<longrightarrow> (\<exists>x. ((p x a) \<or> (q a x))) *)

Imp (Exi (Uni p[1, 0])) (Exi (Dis p[0, a] q[a, 0]))

Imp_R
  Neg (Exi (Uni p[1, 0]))
  Exi (Dis p[0, a] q[a, 0])
Exi_L
  Neg (Uni p[b, 0])
  Exi (Dis p[0, a] q[a, 0])
Uni_L[a]
  Neg p[b, a]
  Exi (Dis p[0, a] q[a, 0])
Ext
  Exi (Dis p[0, a] q[a, 0])
  Neg p[b, a]
Exi_R[b]
  Dis p[b, a] q[a, b]
  Neg p[b, a]
Dis_R
  p[b, a]
  q[a, b]
  Neg p[b, a]
Ext
  p[b, a]
  Neg p[b, a]
Basic

*)

end
