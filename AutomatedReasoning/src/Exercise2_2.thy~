theory Exercise2_2 imports Main begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_1 [simp]: "Suc (add m n) = add m (Suc n)"
  apply(induction m)
  apply(auto)
  done

theorem add_com: "add m n = add n m"
  apply(induction m)
  apply(induction n)
  apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

theorem double_add: "double m = add m m"
  apply(induction m)
  apply(auto)
  done

end