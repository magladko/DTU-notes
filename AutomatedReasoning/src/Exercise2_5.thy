theory Exercise2_5 imports Main begin

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto n = n + sum_upto (n - 1)"

theorem sum_upto_calc: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

end