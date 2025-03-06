theory Exercise3_2 imports Main begin

inductive palindrome :: "'a list \<Rightarrow> bool" where
palindrome0: "palindrome []" |
palindrome1: "palindrome [a]" |
palindrome_wrap: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

theorem is_palindrome: "palindrome xs \<Longrightarrow> (rev xs) = xs"
  apply(induction rule: palindrome.induct)
  by auto

end