theory Exercise4_1 imports Main begin

(*lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
  show "T x y" using A T TA \<open>A x y\<close> by blast
qed*)

lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
  (* Instantiate totality of T at our specific x and y *)
  have disj: "T x y \<or> T y x" using T by simp

  show "T x y"
  proof (cases "T x y")
    (* Case 1: T x y already holds — trivial *)
    case True
    then show ?thesis .
  next
    (* Case 2: T x y does not hold, so T y x must hold *)
    case False
    then have tyx: "T y x" using disj by simp

    (* Apply TA to get A y x from T y x *)
    then have ayx: "A y x" using TA by simp

    (* We have A x y (given) and A y x, so antisymmetry gives x = y *)
    then have eq: "x = y" using A \<open>A x y\<close> ayx by blast

    (* Since x = y, T x y is the same as T x x, which holds by totality *)
    then show "T x y" using T by blast
  qed
qed

end