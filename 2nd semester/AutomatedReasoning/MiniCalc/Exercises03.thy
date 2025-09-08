theory Exercises03 imports MiniCalc begin

(* ============  1. ============= *)

term \<open>p \<or> (\<not> p)\<close>

proposition \<open>p \<or> (\<not> p)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  \<close>

lemma \<open>\<tturnstile>
  [
    Dis (Pre 0 []) (Neg (Pre 0 []))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

(* p \<or> (\<not> p) *)

Dis p (Neg p)

Dis_R
  p
  Neg p
Basic

*)

(* ============  2. ============= *)

term \<open>p \<longrightarrow> (\<not> (\<not> p))\<close>

proposition \<open>p \<longrightarrow> (\<not> (\<not> p))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 []) (Neg (Neg (Pre 0 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Neg (Pre 0 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
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

(*

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

*)

(* ============  3. ============= *)

term \<open>p \<or> (p \<longrightarrow> q)\<close>

proposition \<open>p \<or> (p \<longrightarrow> q)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  \<close>

lemma \<open>\<tturnstile>
  [
    Dis (Pre 0 []) (Imp (Pre 0 []) (Pre 1 []))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Imp (Pre 0 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 []) (Pre 1 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 1 [],
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

(*

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

*)

(* ============  4. ============= *)

term \<open>(p \<and> q) \<longrightarrow> (r \<longrightarrow> (p \<and> r))\<close>

proposition \<open>(p \<and> q) \<longrightarrow> (r \<longrightarrow> (p \<and> r))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
    2 = r
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Con (Pre 0 []) (Pre 1 [])) (Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Pre 0 []) (Pre 1 [])),
      Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Con_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Pre 1 []),
      Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 [])),
      Neg (Pre 0 []),
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Con (Pre 0 []) (Pre 2 []),
      Neg (Pre 0 []),
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 []) (Pre 2 []),
      Neg (Pre 2 []),
      Neg (Pre 0 []),
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 2 []),
      Neg (Pre 0 []),
      Neg (Pre 1 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 2 [],
      Neg (Pre 2 []),
      Neg (Pre 0 []),
      Neg (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

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
  Neg q
Con_R
  p
  Neg r
  Neg p
  Neg q
+
  r
  Neg r
  Neg p
  Neg q
Basic

*)

(* ============  5. ============= *)

term \<open>(p (f a)) \<longrightarrow> (\<exists>x. (p x))\<close>

proposition \<open>(p (f a)) \<longrightarrow> (\<exists>x. (p x))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = f
    1 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 [Fun 0 [Fun 1 []]]) (Exi (Pre 0 [Var 0]))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 1 []]]),
      Exi (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 0 [Var 0]),
      Neg (Pre 0 [Fun 0 [Fun 1 []]])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 [Fun 1 []]\<close>] have ?thesis if \<open>\<tturnstile>
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

*)

(* ============  6. ============= *)

term \<open>(p \<longrightarrow> (\<not> p)) \<longrightarrow> (\<not> p)\<close>

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

(*

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

*)

(* ============  7. ============= *)

term \<open>(p \<longrightarrow> q) \<or> (r \<longrightarrow> p)\<close>

proposition \<open>(p \<longrightarrow> q) \<or> (r \<longrightarrow> p)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
    2 = r
  \<close>

lemma \<open>\<tturnstile>
  [
    Dis (Imp (Pre 0 []) (Pre 1 [])) (Imp (Pre 2 []) (Pre 0 []))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 []) (Pre 1 []),
      Imp (Pre 2 []) (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 1 [],
      Imp (Pre 2 []) (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 2 []) (Pre 0 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Pre 0 [],
      Neg (Pre 0 [])
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

(*

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

*)

(* ============  8. ============= *)

term \<open>(\<not> (\<exists>x. (p (f x)))) \<longrightarrow> (\<forall>x. (\<not> (p (f x))))\<close>

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