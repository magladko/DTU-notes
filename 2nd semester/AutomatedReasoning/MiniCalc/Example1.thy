theory Example1 imports MiniCalc begin

term \<open>(p a b) \<or> (\<not> (p a b))\<close>

proposition \<open>(p a b) \<or> (\<not> (p a b))\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  Function numbers
    0 = a
    1 = b
    2 = f
    3 = g
  \<close>

lemma \<open>\<tturnstile>
  [
    Dis (Pre 0 [Fun 0 [], Fun 1 []]) (Neg (Pre 0 [Fun 0 [], Fun 1 []]))
  ]
  \<close>
proof -
  from Dis_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [], Fun 1 []],
      Neg (Pre 0 [Fun 0 [], Fun 1 []])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Imp (Con (Pre 0 []) (Pre 1 [Fun 2 [Fun 0 [], Fun 3 [Fun 1 []]]])) (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Pre 0 []) (Pre 1 [Fun 2 [Fun 0 [], Fun 3 [Fun 1 []]]])),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Con_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Pre 1 [Fun 2 [Fun 0 [], Fun 3 [Fun 1 []]]]),
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

(* (p a b) \<or> (\<not> (p a b)) *)

Dis p[a, b] (Neg p[a, b])

Dis_R
  p[a, b]
  Neg p[a, b]
Basic
  Imp (Con p q[f[a, g[b]]]) p
Imp_R
  Neg (Con p q[f[a, g[b]]])
  p
Con_L
  Neg p
  Neg q[f[a, g[b]]]
  p
Ext
  p
  Neg p
Basic

*)

end