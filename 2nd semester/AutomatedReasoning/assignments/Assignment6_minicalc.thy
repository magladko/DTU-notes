theory Assignment6_minicalc imports MiniCalc begin
term \<open>(\<forall>x. ((\<not> (r x)) \<longrightarrow> (r (f x)))) \<longrightarrow> (\<exists>x. ((r x) \<and> (r (f (f x)))))\<close>

proposition \<open>(\<forall>x. ((\<not> (r x)) \<longrightarrow> (r (f x)))) \<longrightarrow> (\<exists>x. ((r x) \<and> (r (f (f x)))))\<close> by metis

text \<open>
  Predicate numbers
    0 = r
  Function numbers
    0 = f
    1 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))) (Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 1 []]) (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 1 []]) (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]),
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 [Fun 1 []]\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 0 [Fun 1 []]]) (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]),
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 [Fun 0 [Fun 1 []]]\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]) (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Uni_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [Fun 1 []])) (Pre 0 [Fun 0 [Fun 1 []]])),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]])) (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]])) (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 []]),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 1 []]]),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 1 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 1 []]],
      Neg (Pre 0 [Fun 0 [Fun 1 []]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Exi (Con (Pre 0 [Var 0]) (Pre 0 [Fun 0 [Fun 0 [Var 0]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Exi_R[where t=\<open>Fun 0 [Fun 1 []]\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 0 [Fun 1 []]]) (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Neg (Pre 0 [Var 0])) (Pre 0 [Fun 0 [Var 0]]))),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close>
    using that by simp
  with Uni_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [Fun 0 [Fun 1 []]])) (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]])),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp (Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]])) (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]])),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close>
    using that by simp
  with Imp_L have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 1 []]]),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]),
      Pre 0 [Fun 0 [Fun 1 []]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]]),
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 1 []]],
      Neg (Pre 0 [Fun 0 [Fun 1 []]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 1 []]]])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]],
      Neg (Pre 0 [Fun 0 [Fun 0 [Fun 0 [Fun 1 []]]]])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

(* (\<forall>x. ((\<not> (r x)) \<longrightarrow> (r (f x)))) \<longrightarrow> (\<exists>x. ((r x) \<and> (r (f (f x))))) *)

Imp (Uni (Imp (Neg r[0]) r[f[0]])) (Exi (Con r[0] r[f[f[0]]]))

Imp_R
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
Ext
  Exi (Con r[0] r[f[f[0]]])
  Exi (Con r[0] r[f[f[0]]])
  Exi (Con r[0] r[f[f[0]]])
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Exi_R[a]
  Con r[a] r[f[f[a]]]
  Exi (Con r[0] r[f[f[0]]])
  Exi (Con r[0] r[f[f[0]]])
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Ext
  Con r[a] r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
  Exi (Con r[0] r[f[f[0]]])
Con_R
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
  Exi (Con r[0] r[f[f[0]]])
+
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
  Exi (Con r[0] r[f[f[0]]])
Ext
  Exi (Con r[0] r[f[f[0]]])
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Exi_R[f[a]]
  Con r[f[a]] r[f[f[f[a]]]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Con_R
  r[f[a]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
+
  r[f[f[f[a]]]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  Exi (Con r[0] r[f[f[0]]])
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Ext
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[a]]
  r[a]
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[f[a]]]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Exi_R[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[a]]
  r[a]
+
  Con r[f[f[a]]] r[f[f[f[f[a]]]]]
  r[f[f[f[a]]]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Con_R
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[a]]
  r[a]
+
  r[f[f[a]]]
  r[f[f[f[a]]]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
+
  r[f[f[f[f[a]]]]]
  r[f[f[f[a]]]]
  r[a]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Ext
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[a]]
  r[a]
+
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[f[a]]]
  r[f[f[f[a]]]]
  r[a]
+
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[f[f[f[a]]]]]
  r[f[f[f[a]]]]
  r[a]
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Uni_L
  Neg (Imp (Neg r[a]) r[f[a]])
  r[f[a]]
  r[a]
+
  Neg (Imp (Neg r[f[f[a]]]) r[f[f[f[a]]]])
  r[f[f[a]]]
  r[f[f[f[a]]]]
  r[a]
+
  Neg (Imp (Neg r[f[f[f[a]]]]) r[f[f[f[f[a]]]]])
  r[f[f[f[f[a]]]]]
  r[f[f[f[a]]]]
  r[a]
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Imp_L
  Neg r[a]
  r[f[a]]
  r[a]
+
  Neg r[f[a]]
  r[f[a]]
  r[a]
+
  Neg r[f[f[a]]]
  r[f[f[a]]]
  r[f[f[f[a]]]]
  r[a]
+
  Neg r[f[f[f[a]]]]
  r[f[f[a]]]
  r[f[f[f[a]]]]
  r[a]
+
  Neg r[f[f[f[a]]]]
  r[f[f[f[f[a]]]]]
  r[f[f[f[a]]]]
  r[a]
+
  Neg r[f[f[f[f[a]]]]]
  r[f[f[f[f[a]]]]]
  r[f[f[f[a]]]]
  r[a]
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Ext
  r[a]
  Neg r[a]
+
  r[f[a]]
  Neg r[f[a]]
+
  r[f[f[a]]]
  Neg r[f[f[a]]]
+
  r[f[f[f[a]]]]
  Neg r[f[f[f[a]]]]
+
  r[f[f[f[a]]]]
  Neg r[f[f[f[a]]]]
+
  r[f[f[f[f[a]]]]]
  Neg r[f[f[f[f[a]]]]]
+
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Basic
  Exi (Con r[0] r[f[f[0]]])
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Exi_R[f[a]]
  Con r[f[a]] r[f[f[f[a]]]]
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Con_R
  r[f[a]]
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
+
  r[f[f[f[a]]]]
  r[f[f[a]]]
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
Ext
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[a]]
  r[f[f[a]]]
+
  Neg (Uni (Imp (Neg r[0]) r[f[0]]))
  r[f[f[f[a]]]]
  r[f[f[a]]]
Uni_L
  Neg (Imp (Neg r[f[a]]) r[f[f[a]]])
  r[f[a]]
  r[f[f[a]]]
+
  Neg (Imp (Neg r[f[f[a]]]) r[f[f[f[a]]]])
  r[f[f[f[a]]]]
  r[f[f[a]]]
Imp_L
  Neg r[f[a]]
  r[f[a]]
  r[f[f[a]]]
+
  Neg r[f[f[a]]]
  r[f[a]]
  r[f[f[a]]]
+
  Neg r[f[f[a]]]
  r[f[f[f[a]]]]
  r[f[f[a]]]
+
  Neg r[f[f[f[a]]]]
  r[f[f[f[a]]]]
  r[f[f[a]]]
Ext
  r[f[a]]
  Neg r[f[a]]
+
  r[f[f[a]]]
  Neg r[f[f[a]]]
+
  r[f[f[a]]]
  Neg r[f[f[a]]]
+
  r[f[f[f[a]]]]
  Neg r[f[f[f[a]]]]
Basic

*)

end