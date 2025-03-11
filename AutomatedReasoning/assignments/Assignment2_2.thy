theory Assignment2_2 imports Main begin

(* Exercise 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a [b] = [b]" |
  "intersperse a (b # xs) = b # a # intersperse a xs"

theorem map_intersperse_commute:
  "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  by auto

(* Exercise 2.9 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_suc_step [simp]: "itadd m (Suc n) = Suc (itadd m n)"
  by (induction m arbitrary: n) auto

theorem tail_rec_add: "itadd m n = add m n"
  by (induction m) auto

end