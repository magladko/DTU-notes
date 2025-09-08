theory Assignment4_minicalc imports MiniCalc begin

term \<open>((\<not> p) \<longrightarrow> p) \<longrightarrow> ((p \<longrightarrow> (\<not> p)) \<longrightarrow> q)\<close>

term \<open>(\<forall>x. (p x)) \<longrightarrow> ((p a) \<and> (p (f a)))\<close>

term \<open>(\<exists>x. (\<forall>y. (r x y))) \<longrightarrow> (\<forall>x. (\<exists>y. (r y x)))\<close>

section \<open>Formula 1\<close>

proposition \<open>((\<not> p) \<longrightarrow> p) \<longrightarrow> ((p \<longrightarrow> (\<not> p)) \<longrightarrow> q)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Neg (Pre 0 [])) (Pre 0 [])) (Imp (Imp (Pre 0 []) (Neg (Pre 0 []))) (Pre 1 []))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [])) (Pre 0 [])),
      Imp (Imp (Pre 0 []) (Neg (Pre 0 []))) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Imp (Imp (Pre 0 []) (Neg (Pre 0 []))) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp (Pre 0 []) (Neg (Pre 0 []))) (Pre 1 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Neg (Pre 0 []))),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Neg (Pre 0 [])),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [],
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 2\<close>

proposition \<open>(\<forall>x. (p x)) \<longrightarrow> ((p a) \<and> (p (f a)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = a
    1 = f
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Pre 0 [Var 0])) (Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 [Fun 0 []]]))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 [Fun 0 []]])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 [Fun 0 []]]),
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 [Fun 0 []]],
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 [Fun 0 []]],
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 [Fun 0 []]],
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 1 [Fun 0 []]]
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 1 [Fun 0 []]]
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 1 [Fun 0 []]\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 [Fun 0 []]]),
      Pre 0 [Fun 1 [Fun 0 []]]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 [Fun 0 []]],
      Neg (Pre 0 [Fun 1 [Fun 0 []]])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 3\<close>

proposition \<open>(\<exists>x. (\<forall>y. (r x y))) \<longrightarrow> (\<forall>x. (\<exists>y. (r y x)))\<close> by metis

text \<open>
  Predicate numbers
    0 = r
  Function numbers
    0 = a
    1 = b
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Exi (Uni (Pre 0 [Var 1, Var 0]))) (Uni (Exi (Pre 0 [Var 0, Var 1])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Uni (Pre 0 [Var 1, Var 0]))),
      Uni (Exi (Pre 0 [Var 0, Var 1]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Exi (Pre 0 [Var 0, Var 1])),
      Neg (Exi (Uni (Pre 0 [Var 1, Var 0])))
    ]
    \<close>
    using that by simp
  with Uni_R have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 0 [Var 0, Fun 0 []]),
      Neg (Exi (Uni (Pre 0 [Var 1, Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Uni (Pre 0 [Var 1, Var 0]))),
      Exi (Pre 0 [Var 0, Fun 0 []])
    ]
    \<close>
    using that by simp
  with Exi_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Fun 1 [], Var 0])),
      Exi (Pre 0 [Var 0, Fun 0 []])
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 [], Fun 0 []]),
      Exi (Pre 0 [Var 0, Fun 0 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 0 [Var 0, Fun 0 []]),
      Neg (Pre 0 [Fun 1 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
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

# "Formula 1"

(* ((\<not> p) \<longrightarrow> p) \<longrightarrow> ((p \<longrightarrow> (\<not> p)) \<longrightarrow> q) *)

Imp (Imp (Neg p) p) (Imp (Imp p (Neg p)) q)

Imp_R
  Neg (Imp (Neg p) p)
  Imp (Imp p (Neg p)) q
Imp_L
  Neg p
  Imp (Imp p (Neg p)) q
Ext
  Imp (Imp p (Neg p)) q
  Neg p
Imp_R
  Neg (Imp p (Neg p))
  q
  Neg p
Imp_L
  p
  q
  Neg p
+
  Neg (Neg p)
  q
  Neg p
NegNeg
  p
  q
  Neg p
+
  p
  q
  Neg p
Basic

# "Formula 2"

(* (\<forall>x. (p x)) \<longrightarrow> ((p a) \<and> (p (f a))) *)

Imp (Uni p[0]) (Con p[a] p[f[a]])

Imp_R
  Neg (Uni p[0])
  Con p[a] p[f[a]]
Ext
  Con p[a] p[f[a]]
  Neg (Uni p[0])
Con_R
  p[a]
  Neg (Uni p[0])
+
  p[f[a]]
  Neg (Uni p[0])
Ext
  Neg (Uni p[0])
  p[a]
+
  p[f[a]]
  Neg (Uni p[0])
Uni_L[a]
  Neg p[a]
  p[a]
+
  p[f[a]]
  Neg (Uni p[0])
Ext
  p[a]
  Neg p[a]
+
  Neg (Uni p[0])
  p[f[a]]
Basic
  Neg (Uni p[0])
  p[f[a]]
Uni_L[f[a]]
  Neg p[f[a]]
  p[f[a]]
Ext
  p[f[a]]
  Neg p[f[a]]
Basic

# "Formula 3"

(* (\<exists>x. (\<forall>y. (r x y))) \<longrightarrow> (\<forall>x. (\<exists>y. (r y x))) *)

Imp (Exi (Uni r[1, 0])) (Uni (Exi r[0, 1]))

Imp_R
  Neg (Exi (Uni r[1, 0]))
  Uni (Exi r[0, 1])
Ext
  Uni (Exi r[0, 1])
  Neg (Exi (Uni r[1, 0]))
Uni_R
  Exi r[0, a]
  Neg (Exi (Uni r[1, 0]))
Ext
  Neg (Exi (Uni r[1, 0]))
  Exi r[0, a]
Exi_L
  Neg (Uni r[b, 0])
  Exi r[0, a]
Uni_L[a]
  Neg r[b, a]
  Exi r[0, a]
Ext
  Exi r[0, a]
  Neg r[b, a]
Exi_R[b]
  r[b, a]
  Neg r[b, a]
Basic

*)

end