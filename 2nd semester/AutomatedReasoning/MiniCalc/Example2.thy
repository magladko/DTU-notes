theory Example2 imports MiniCalc begin

term \<open>(\<forall>x. (\<forall>y. (p x y))) \<longrightarrow> (p a a)\<close>

proposition \<open>(\<forall>x. (\<forall>y. (p x y))) \<longrightarrow> (p a a)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Uni (Pre 0 [Var 1, Var 0]))) (Pre 0 [Fun 0 [], Fun 0 []])
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Uni (Pre 0 [Var 1, Var 0]))),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Fun 0 [], Var 0])),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with Uni_L[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [], Fun 0 []]),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [], Fun 0 []],
      Neg (Pre 0 [Fun 0 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

(* (\<forall>x. (\<forall>y. (p x y))) \<longrightarrow> (p a a) *)

Imp (Uni (Uni p[1, 0])) p[a, a]

Imp_R
  Neg (Uni (Uni p[1, 0]))
  p[a, a]
Uni_L[a]
  Neg (Uni p[a, 0])
  p[a, a]
Uni_L[a]
  Neg p[a, a]
  p[a, a]
Ext
  p[a, a]
  Neg p[a, a]
Basic

*)

end