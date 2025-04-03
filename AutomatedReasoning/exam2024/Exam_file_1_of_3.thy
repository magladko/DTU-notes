theory Exam_file_1_of_3 imports MiniCalc begin

\<comment> \<open>Please try to keep each line shorter than 100 characters and do not alter the "theory" command\<close>

text \<open>

Use MiniCalc to prove the following formulas and include all "Copy Result to Clipboard" lines.

\<close>

proposition \<open>p \<longrightarrow> \<not> (p \<and> \<not> q) \<longrightarrow> q\<close>
  oops

proposition \<open>(\<forall>x. p x \<and> q x) \<longrightarrow> (\<exists>x. q x \<or> r x)\<close>
  oops

proposition \<open>(p (f a b c) \<longrightarrow> q) \<or> (q \<longrightarrow> (\<exists>x. \<forall>y. r x y))\<close>
  oops

\<comment> \<open>Please keep the "end" command and ensure that Isabelle/HOL does not indicate any errors at all\<close>

term \<open>p \<longrightarrow> ((\<not> (p \<and> (\<not> q))) \<longrightarrow> q)\<close>

proposition \<open>p \<longrightarrow> ((\<not> (p \<and> (\<not> q))) \<longrightarrow> q)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 []) (Imp (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))) (Pre 1 []))
  ]
  \<close>
proof -
  from Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Imp (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))) (Pre 1 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Imp_R have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Con (Pre 0 []) (Neg (Pre 1 [])))),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 []) (Neg (Pre 1 [])),
      Pre 1 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Con_R have ?thesis if \<open>\<tturnstile>
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
      Neg (Pre 0 []),
      Pre 1 []
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 1 [],
      Neg (Pre 1 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

(*

(* p \<longrightarrow> ((\<not> (p \<and> (\<not> q))) \<longrightarrow> q) *)

Imp p (Imp (Neg (Con p (Neg q))) q)

Imp_R
  Neg p
  Imp (Neg (Con p (Neg q))) q
Ext
  Imp (Neg (Con p (Neg q))) q
  Neg p
Imp_R
  Neg (Neg (Con p (Neg q)))
  q
  Neg p
NegNeg
  Con p (Neg q)
  q
  Neg p
Con_R
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
  q
+
  q
  Neg q
  Neg p
Basic

*)

end
