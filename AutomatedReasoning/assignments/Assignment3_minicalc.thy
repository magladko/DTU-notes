theory Assignment3_minicalc imports MiniCalc begin

term \<open>(\<not> q) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (\<not> p))\<close>

term \<open>(p \<longrightarrow> q) \<longrightarrow> ((\<not> q) \<longrightarrow> (\<not> p))\<close>

section \<open>Formula 1\<close>

proposition \<open>(\<not> q) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (\<not> p))\<close> by metis

text \<open>
  Predicate numbers
    0 = q
    1 = p
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Neg (Pre 0 [])) (Imp (Imp (Pre 1 []) (Pre 0 [])) (Neg (Pre 1 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Pre 0 [])),
      Imp (Imp (Pre 1 []) (Pre 0 [])) (Neg (Pre 1 []))
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Imp (Imp (Pre 1 []) (Pre 0 [])) (Neg (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp (Pre 1 []) (Pre 0 [])) (Neg (Pre 1 [])),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 1 []) (Pre 0 [])),
      Neg (Pre 1 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 []),
      Pre 0 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Pre 1 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Pre 1 []),
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

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> ((\<not> q) \<longrightarrow> (\<not> p))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Imp (Pre 0 []) (Pre 1 [])) (Imp (Neg (Pre 1 [])) (Neg (Pre 0 [])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
      Imp (Neg (Pre 1 [])) (Neg (Pre 0 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Neg (Pre 1 [])) (Neg (Pre 0 [])),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Pre 1 [])),
      Neg (Pre 0 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 0 []),
      Neg (Imp (Pre 0 []) (Pre 1 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 []) (Pre 1 [])),
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
      Neg (Pre 1 []),
      Pre 1 [],
      Neg (Pre 0 [])
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

(*

# "Formula 1"

(* (\<not> q) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (\<not> p)) *)

Imp (Neg q) (Imp (Imp p q) (Neg p))

Imp_R
  Neg (Neg q)
  Imp (Imp p q) (Neg p)
NegNeg
  q
  Imp (Imp p q) (Neg p)
Ext
  Imp (Imp p q) (Neg p)
  q
Imp_R
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
Basic
  Neg q
  Neg p
  q
Ext
  q
  Neg q
Basic

# "Formula 2"

(* (p \<longrightarrow> q) \<longrightarrow> ((\<not> q) \<longrightarrow> (\<not> p)) *)

Imp (Imp p q) (Imp (Neg q) (Neg p))

Imp_R
  Neg (Imp p q)
  Imp (Neg q) (Neg p)
Ext
  Imp (Neg q) (Neg p)
  Neg (Imp p q)
Imp_R
  Neg (Neg q)
  Neg p
  Neg (Imp p q)
NegNeg
  q
  Neg p
  Neg (Imp p q)
Ext
  Neg (Imp p q)
  q
  Neg p
Imp_L
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
+
  q
  Neg q
Basic

*)

end