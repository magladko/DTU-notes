theory Exercise2_3 imports Main begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a [] = 0" |
"count a (b # xs) = (count a xs) + (if a = b then 1 else 0)"

theorem count_limit: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

end