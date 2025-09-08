theory Scratch imports Complex_Main begin

(* ML - Meta Language *)

ML \<open>fun f x = f x\<close>

fun f where \<open>f x = x\<close>

theorem \<open>x / 0 = 0\<close> for x :: complex
  by auto

end