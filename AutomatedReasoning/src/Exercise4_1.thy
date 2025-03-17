theory Exercise4_1 imports Main begin

lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
  show "T x y" using A T TA \<open>A x y\<close> by blast
qed

end