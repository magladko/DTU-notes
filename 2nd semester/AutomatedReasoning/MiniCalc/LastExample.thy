theory LastExample imports MiniCalc begin

term \<open>\<exists>x. (\<forall>y. ((p x) \<longrightarrow> (p y)))\<close>

proposition \<open>\<exists>x. (\<forall>y. ((p x) \<longrightarrow> (p y)))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = a
    1 = b
    2 = c
  \<close>

lemma \<open>\<tturnstile>
  [
    Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
  ]
  \<close>
proof -
  from Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0]))),
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Uni (Imp (Pre 0 [Fun 0 []]) (Pre 0 [Var 0])),
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Uni_R have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]),
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 1 []],
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0]))),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Uni (Imp (Pre 0 [Fun 1 []]) (Pre 0 [Var 0])),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Uni_R have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 1 []]) (Pre 0 [Fun 2 []]),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 []]),
      Pre 0 [Fun 2 []],
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

(*

(* \<exists>x. (\<forall>y. ((p x) \<longrightarrow> (p y))) *)

Exi (Uni (Imp p[1] p[0]))

Ext
  Exi (Uni (Imp p[1] p[0]))
  Exi (Uni (Imp p[1] p[0]))
Exi_R[a]
  Uni (Imp p[a] p[0])
  Exi (Uni (Imp p[1] p[0]))
Uni_R
  Imp p[a] p[b]
  Exi (Uni (Imp p[1] p[0]))
Imp_R
  Neg p[a]
  p[b]
  Exi (Uni (Imp p[1] p[0]))
Ext
  Exi (Uni (Imp p[1] p[0]))
  p[b]
Exi_R[b]
  Uni (Imp p[b] p[0])
  p[b]
Uni_R
  Imp p[b] p[c]
  p[b]
Imp_R
  Neg p[b]
  p[c]
  p[b]
Ext
  p[b]
  Neg p[b]
Basic

*)

end