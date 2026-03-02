theory MyTest imports MiniCalc begin

term \<open>p \<or> (\<not> p)\<close>

term \<open>p \<longrightarrow> (\<not> (\<not> p))\<close>

term \<open>p \<or> (p \<longrightarrow> q)\<close>

term \<open>(p \<and> q) \<longrightarrow> (r \<longrightarrow> (p \<and> r))\<close>

term \<open>(p (f a)) \<longrightarrow> (\<exists>x. (p x))\<close>

term \<open>(p \<longrightarrow> (\<not> p)) \<longrightarrow> (\<not> p)\<close>

term \<open>(p \<longrightarrow> q) \<or> (r \<longrightarrow> p)\<close>

term \<open>(\<not> (\<exists>x. (p (f x)))) \<longrightarrow> (\<forall>x. (\<not> (p (f x))))\<close>

section \<open>Formula 1\<close>

proposition \<open>p \<or> (\<not> p)\<close> by metis

text \<open>
  Pre: p
\<close>

lemma \<open>\<tturnstile>
  [
    Dis (Pre ''p'' []) (Neg (Pre ''p'' []))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 2\<close>

proposition \<open>p \<longrightarrow> (\<not> (\<not> p))\<close> by metis

text \<open>
  Pre: p
\<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre ''p'' []) (Neg (Neg (Pre ''p'' [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' []),
      Neg (Neg (Pre ''p'' []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Pre ''p'' [])),
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 3\<close>

proposition \<open>p \<or> (p \<longrightarrow> q)\<close> by metis

text \<open>
  Pre: p, q
\<close>

lemma \<open>\<tturnstile>
  [
    Dis (Pre ''p'' []) (Imp (Pre ''p'' []) (Pre ''q'' []))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Imp (Pre ''p'' []) (Pre ''q'' [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre ''p'' []) (Pre ''q'' []),
      Pre ''p'' []
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' []),
      Pre ''q'' [],
      Pre ''p'' []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 4\<close>

proposition \<open>(p \<and> q) \<longrightarrow> (r \<longrightarrow> (p \<and> r))\<close> by metis

text \<open>
  Pre: p, q, r
\<close>

lemma \<open>\<tturnstile>
  [
    Imp (Con (Pre ''p'' []) (Pre ''q'' [])) (Imp (Pre ''r'' []) (Con (Pre ''p'' []) (Pre ''r'' [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Pre ''p'' []) (Pre ''q'' [])),
      Imp (Pre ''r'' []) (Con (Pre ''p'' []) (Pre ''r'' []))
    ]
    \<close>
    using that by simp
  with Con_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' []),
      Neg (Pre ''q'' []),
      Imp (Pre ''r'' []) (Con (Pre ''p'' []) (Pre ''r'' []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre ''r'' []) (Con (Pre ''p'' []) (Pre ''r'' [])),
      Neg (Pre ''p'' []),
      Neg (Pre ''q'' [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''r'' []),
      Con (Pre ''p'' []) (Pre ''r'' []),
      Neg (Pre ''p'' []),
      Neg (Pre ''q'' [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre ''p'' []) (Pre ''r'' []),
      Neg (Pre ''r'' []),
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''r'' []),
      Neg (Pre ''p'' [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre ''r'' [],
      Neg (Pre ''r'' []),
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre ''r'' [],
      Neg (Pre ''r'' [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 5\<close>

proposition \<open>(p (f a)) \<longrightarrow> (\<exists>x. (p x))\<close> by metis

text \<open>
  Pre: p
  Fun: a, f
\<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre ''p'' [Fun ''f'' [Fun ''a'' []]]) (Exi (Pre ''p'' [Var 0]))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' [Fun ''f'' [Fun ''a'' []]]),
      Exi (Pre ''p'' [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre ''p'' [Var 0]),
      Neg (Pre ''p'' [Fun ''f'' [Fun ''a'' []]])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun ''f'' [Fun ''a'' []]\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [Fun ''f'' [Fun ''a'' []]],
      Neg (Pre ''p'' [Fun ''f'' [Fun ''a'' []]])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 6\<close>

proposition \<open>(p \<longrightarrow> (\<not> p)) \<longrightarrow> (\<not> p)\<close> by metis

text \<open>
  Pre: p
\<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre ''p'' []) (Neg (Pre ''p'' []))) (Neg (Pre ''p'' []))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre ''p'' []) (Neg (Pre ''p'' []))),
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Neg (Pre ''p'' [])),
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 7\<close>

proposition \<open>(p \<longrightarrow> q) \<or> (r \<longrightarrow> p)\<close> by metis

text \<open>
  Pre: p, q, r
\<close>

lemma \<open>\<tturnstile>
  [
    Dis (Imp (Pre ''p'' []) (Pre ''q'' [])) (Imp (Pre ''r'' []) (Pre ''p'' []))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre ''p'' []) (Pre ''q'' []),
      Imp (Pre ''r'' []) (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' []),
      Pre ''q'' [],
      Imp (Pre ''r'' []) (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre ''r'' []) (Pre ''p'' []),
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''r'' []),
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [],
      Neg (Pre ''p'' [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Formula 8\<close>

proposition \<open>(\<not> (\<exists>x. (p (f x)))) \<longrightarrow> (\<forall>x. (\<not> (p (f x))))\<close> by metis

text \<open>
  Pre: p
  Fun: a, f
\<close>

lemma \<open>\<tturnstile>
  [
    Imp (Neg (Exi (Pre ''p'' [Fun ''f'' [Var 0]]))) (Uni (Neg (Pre ''p'' [Fun ''f'' [Var 0]])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Exi (Pre ''p'' [Fun ''f'' [Var 0]]))),
      Uni (Neg (Pre ''p'' [Fun ''f'' [Var 0]]))
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre ''p'' [Fun ''f'' [Var 0]]),
      Uni (Neg (Pre ''p'' [Fun ''f'' [Var 0]]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Neg (Pre ''p'' [Fun ''f'' [Var 0]])),
      Exi (Pre ''p'' [Fun ''f'' [Var 0]])
    ]
    \<close>
    using that by simp
  with Uni_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' [Fun ''f'' [Fun ''a'' []]]),
      Exi (Pre ''p'' [Fun ''f'' [Var 0]])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre ''p'' [Fun ''f'' [Var 0]]),
      Neg (Pre ''p'' [Fun ''f'' [Fun ''a'' []]])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun ''a'' []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [Fun ''f'' [Fun ''a'' []]],
      Neg (Pre ''p'' [Fun ''f'' [Fun ''a'' []]])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

# "Formula 1"

(* p \<or> (\<not> p) *)

Dis p (Neg p)

Dis_R
  p
  Neg p
Basic

# "Formula 2"

(* p \<longrightarrow> (\<not> (\<not> p)) *)

Imp p (Neg (Neg p))

Imp_R
  Neg p
  Neg (Neg p)
Ext
  Neg (Neg p)
  Neg p
NegNeg
  p
  Neg p
Basic

# "Formula 3"

(* p \<or> (p \<longrightarrow> q) *)

Dis p (Imp p q)

Dis_R
  p
  Imp p q
Ext
  Imp p q
  p
Imp_R
  Neg p
  q
  p
Ext
  p
  Neg p
Basic

# "Formula 4"

(* (p \<and> q) \<longrightarrow> (r \<longrightarrow> (p \<and> r)) *)

Imp (Con p q) (Imp r (Con p r))

Imp_R
  Neg (Con p q)
  Imp r (Con p r)
Con_L
  Neg p
  Neg q
  Imp r (Con p r)
Ext
  Imp r (Con p r)
  Neg p
  Neg q
Imp_R
  Neg r
  Con p r
  Neg p
  Neg q
Ext
  Con p r
  Neg r
  Neg p
Con_R
  p
  Neg r
  Neg p
+
  r
  Neg r
  Neg p
Ext
  p
  Neg p
+
  r
  Neg r
Basic

# "Formula 5"

(* (p (f a)) \<longrightarrow> (\<exists>x. (p x)) *)

Imp p[f[a]] (Exi p[0])

Imp_R
  Neg p[f[a]]
  Exi p[0]
Ext
  Exi p[0]
  Neg p[f[a]]
Exi_R[f[a]]
  p[f[a]]
  Neg p[f[a]]
Basic

# "Formula 6"

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
NegNeg
  p
  Neg p
+
  p
  Neg p
Basic

# "Formula 7"

(* (p \<longrightarrow> q) \<or> (r \<longrightarrow> p) *)

Dis (Imp p q) (Imp r p)

Dis_R
  Imp p q
  Imp r p
Imp_R
  Neg p
  q
  Imp r p
Ext
  Imp r p
  Neg p
Imp_R
  Neg r
  p
  Neg p
Ext
  p
  Neg p
Basic

# "Formula 8"

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