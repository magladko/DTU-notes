theory Exercise2_4 imports Main begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (b # xs) a = b # (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (a # xs) = snoc (reverse xs) a"

lemma reverse_snoc [simp]: "reverse (snoc xs a) = a # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

theorem double_reverse: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

end