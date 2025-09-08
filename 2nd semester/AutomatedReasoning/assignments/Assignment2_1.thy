theory Assignment2_1 imports MiniCalc begin

term \<open>((\<not> p) \<longrightarrow> p) \<longrightarrow> ((p \<longrightarrow> (\<not> p)) \<longrightarrow> q)\<close>

term \<open>(\<forall>x. (p x)) \<longrightarrow> ((p a) \<and> (p (f a)))\<close>

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
  from Imp_R show ?thesis
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

*)

end