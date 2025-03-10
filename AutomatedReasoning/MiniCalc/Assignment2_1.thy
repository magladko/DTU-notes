theory Assignment2_1 imports MiniCalc begin

term \<open>(\<not> (\<not> p)) \<longrightarrow> p\<close>

term \<open>(q \<longrightarrow> r) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))\<close>

term \<open>(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> r))\<close>

term \<open>(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))\<close>

term \<open>(\<forall>x. (p x)) \<longrightarrow> (\<exists>x. (p x))\<close>

section \<open>Formula 1\<close>

proposition \<open>(\<not> (\<not> p)) \<longrightarrow> p\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Neg (Neg (Pre 0 []))) (Pre 0 [])
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Neg (Pre 0 []))),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 2\<close>

proposition \<open>(q \<longrightarrow> r) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))\<close> by metis

text \<open>
  Predicate numbers
    0 = q
    1 = r
    2 = p
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre 0 []) (Pre 1 [])) (Imp (Imp (Pre 2 []) (Pre 0 [])) (Imp (Pre 2 []) (Pre 1 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Imp (Imp (Pre 2 []) (Pre 0 [])) (Imp (Pre 2 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp (Pre 2 []) (Pre 0 [])) (Imp (Pre 2 []) (Pre 1 [])),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 2 []) (Pre 0 [])),
      Imp (Pre 2 []) (Pre 1 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 2 [],
      Imp (Pre 2 []) (Pre 1 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 2 []) (Pre 1 []),
      Pre 2 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Pre 1 [],
      Pre 2 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 2 [],
      Neg (Pre 2 []),
      Pre 1 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Neg (Pre 0 []),
      Imp (Pre 2 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 2 []) (Pre 1 []),
      Neg (Pre 1 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Pre 1 [],
      Neg (Pre 1 []),
      Neg (Pre 0 [])
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

section \<open>Formula 3\<close>

proposition \<open>(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> r))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
    2 = r
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 []))) (Imp (Pre 1 []) (Imp (Pre 0 []) (Pre 2 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 []))),
      Imp (Pre 1 []) (Imp (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Imp (Pre 1 []) (Imp (Pre 0 []) (Pre 2 []))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Imp (Pre 1 []) (Imp (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 1 []) (Imp (Pre 0 []) (Pre 2 [])),
      Pre 0 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Imp (Pre 1 []) (Imp (Pre 0 []) (Pre 2 [])),
      Neg (Imp (Pre 1 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Imp (Pre 0 []) (Pre 2 []),
      Pre 0 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Imp (Pre 0 []) (Pre 2 []),
      Neg (Imp (Pre 1 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 []) (Pre 2 []),
      Pre 0 [],
      Neg (Pre 1 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Imp (Pre 0 []) (Pre 2 []),
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 2 [],
      Pre 0 [],
      Neg (Pre 1 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Neg (Pre 1 [])
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
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Pre 1 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 2 [],
      Neg (Pre 2 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 4\<close>

proposition \<open>(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
    2 = r
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 []))) (Imp (Imp (Pre 0 []) (Pre 1 [])) (Imp (Pre 0 []) (Pre 2 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 []))),
      Imp (Imp (Pre 0 []) (Pre 1 [])) (Imp (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp (Pre 0 []) (Pre 1 [])) (Imp (Pre 0 []) (Pre 2 [])),
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 [])))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Imp (Pre 0 []) (Pre 2 []),
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 [])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 []) (Pre 2 []),
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 [])))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 2 [],
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 [])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 2 []))),
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 1 []) (Pre 2 [])),
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 1 [],
      Pre 2 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 2 [],
      Neg (Pre 2 [])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Neg (Pre 0 []),
      Pre 1 [],
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 []),
      Pre 1 [],
      Pre 2 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Neg (Pre 0 []),
      Pre 1 [],
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 1 []),
      Neg (Pre 0 []),
      Pre 1 [],
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 []),
      Neg (Pre 0 []),
      Pre 2 []
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 5\<close>

proposition \<open>(\<forall>x. (p x)) \<longrightarrow> (\<exists>x. (p x))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = x
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Pre 0 [Var 0])) (Exi (Pre 0 [Var 0]))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Exi (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 0 [Var 0]),
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

# "Formula 1"

(* (\<not> (\<not> p)) \<longrightarrow> p *)

Imp (Neg (Neg p)) p

Imp_R
  Neg (Neg (Neg p))
  p
NegNeg
  Neg p
  p
Ext
  p
  Neg p
Basic

# "Formula 2"

(* (q \<longrightarrow> r) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)) *)

Imp (Imp q r) (Imp (Imp p q) (Imp p r))

Imp_R
  Neg (Imp q r)
  Imp (Imp p q) (Imp p r)
Ext
  Imp (Imp p q) (Imp p r)
  Neg (Imp q r)
Imp_R
  Neg (Imp p q)
  Imp p r
  Neg (Imp q r)
Imp_L
  p
  Imp p r
  Neg (Imp q r)
+
  Neg q
  Imp p r
  Neg (Imp q r)
Ext
  Imp p r
  p
+
  Neg (Imp q r)
  Neg q
  Imp p r
Imp_R
  Neg p
  r
  p
+
  Neg (Imp q r)
  Neg q
  Imp p r
Ext
  p
  Neg p
  r
+
  Neg (Imp q r)
  Neg q
  Imp p r
Basic
  Neg (Imp q r)
  Neg q
  Imp p r
Imp_L
  q
  Neg q
  Imp p r
+
  Neg r
  Neg q
  Imp p r
Basic
  Neg r
  Neg q
  Imp p r
Ext
  Imp p r
  Neg r
  Neg q
Imp_R
  Neg p
  r
  Neg r
  Neg q
Ext
  r
  Neg r
Basic

# "Formula 3"

(* (p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> r)) *)

Imp (Imp p (Imp q r)) (Imp q (Imp p r))

Imp_R
  Neg (Imp p (Imp q r))
  Imp q (Imp p r)
Imp_L
  p
  Imp q (Imp p r)
+
  Neg (Imp q r)
  Imp q (Imp p r)
Ext
  Imp q (Imp p r)
  p
+
  Imp q (Imp p r)
  Neg (Imp q r)
Imp_R
  Neg q
  Imp p r
  p
+
  Neg q
  Imp p r
  Neg (Imp q r)
Ext
  Imp p r
  p
  Neg q
+
  Imp p r
  Neg (Imp q r)
  Neg q
Imp_R
  Neg p
  r
  p
  Neg q
+
  Neg p
  r
  Neg (Imp q r)
  Neg q
Ext
  p
  Neg p
+
  Neg (Imp q r)
  Neg p
  r
  Neg q
Basic
  Neg (Imp q r)
  Neg p
  r
  Neg q
Imp_L
  q
  Neg p
  r
  Neg q
+
  Neg r
  Neg p
  r
  Neg q
Basic
  Neg r
  Neg p
  r
  Neg q
Ext
  r
  Neg r
Basic

# "Formula 4"

(* (p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)) *)

Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r))

Imp_R
  Neg (Imp p (Imp q r))
  Imp (Imp p q) (Imp p r)
Ext
  Imp (Imp p q) (Imp p r)
  Neg (Imp p (Imp q r))
Imp_R
  Neg (Imp p q)
  Imp p r
  Neg (Imp p (Imp q r))
Ext
  Imp p r
  Neg (Imp p q)
  Neg (Imp p (Imp q r))
Imp_R
  Neg p
  r
  Neg (Imp p q)
  Neg (Imp p (Imp q r))
Ext
  Neg (Imp p (Imp q r))
  Neg (Imp p q)
  Neg p
  r
Imp_L
  p
  Neg (Imp p q)
  Neg p
  r
+
  Neg (Imp q r)
  Neg (Imp p q)
  Neg p
  r
Basic
  Neg (Imp q r)
  Neg (Imp p q)
  Neg p
  r
Imp_L
  q
  Neg (Imp p q)
  Neg p
  r
+
  Neg r
  Neg (Imp p q)
  Neg p
  r
Ext
  Neg (Imp p q)
  Neg p
  q
  r
+
  r
  Neg r
Basic
  Neg (Imp p q)
  Neg p
  q
  r
Imp_L
  p
  Neg p
  q
  r
+
  Neg q
  Neg p
  q
  r
Basic
  Neg q
  Neg p
  q
  r
Ext
  q
  Neg q
  Neg p
  r
Basic

# "Formula 5"

(* (\<forall>x. (p x)) \<longrightarrow> (\<exists>x. (p x)) *)

Imp (Uni p[0]) (Exi p[0])

Imp_R
  Neg (Uni p[0])
  Exi p[0]
Uni_L[x]
  Neg p[x]
  Exi p[0]
Ext
  Exi p[0]
  Neg p[x]
Exi_R[x]
  p[x]
  Neg p[x]
Basic

*)

end