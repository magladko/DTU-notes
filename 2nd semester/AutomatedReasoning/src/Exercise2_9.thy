theory Exercise2_9 imports Main begin

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