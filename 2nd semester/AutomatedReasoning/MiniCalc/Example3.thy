theory Example3 imports MiniCalc begin

term \<open>(\<forall>x. ((p x) \<longrightarrow> (q x))) \<longrightarrow> ((\<exists>x. (p x)) \<longrightarrow> (\<exists>x. (q x)))\<close>

proposition \<open>(\<forall>x. ((p x) \<longrightarrow> (q x))) \<longrightarrow> ((\<exists>x. (p x)) \<longrightarrow> (\<exists>x. (q x)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  Function numbers
    0 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0]))) (Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0]))),
      Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0])),
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Pre 0 [Var 0])),
      Exi (Pre 1 [Var 0]),
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Exi_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0]),
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0]))),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []])),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 [Fun 0 []]),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 1 [Fun 0 []]),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 1 [Var 0]),
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

(* (\<forall>x. ((p x) \<longrightarrow> (q x))) \<longrightarrow> ((\<exists>x. (p x)) \<longrightarrow> (\<exists>x. (q x))) *)

Imp (Uni (Imp p[0] q[0])) (Imp (Exi p[0]) (Exi q[0]))

Imp_R
  Neg (Uni (Imp p[0] q[0]))
  Imp (Exi p[0]) (Exi q[0])
Ext
  Imp (Exi p[0]) (Exi q[0])
  Neg (Uni (Imp p[0] q[0]))
Imp_R
  Neg (Exi p[0])
  Exi q[0]
  Neg (Uni (Imp p[0] q[0]))
Exi_L
  Neg p[a]
  Exi q[0]
  Neg (Uni (Imp p[0] q[0]))
Ext
  Neg (Uni (Imp p[0] q[0]))
  Neg p[a]
  Exi q[0]
Uni_L[a]
  Neg (Imp p[a] q[a])
  Neg p[a]
  Exi q[0]
Imp_L
  p[a]
  Neg p[a]
  Exi q[0]
+
  Neg q[a]
  Neg p[a]
  Exi q[0]
Basic
  Neg q[a]
  Neg p[a]
  Exi q[0]
Ext
  Exi q[0]
  Neg q[a]
Exi_R[a]
  q[a]
  Neg q[a]
Basic

*)

end