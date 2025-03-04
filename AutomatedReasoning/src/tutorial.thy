theory tutorial
  imports Main
begin

fun remove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "remove x [] = []" |
    "remove x (y#ys) = (if x=y then (remove x ys) else y#(remove x ys))"

value "remove (2::int) [1,2,3]" (* this is a simple test *)

lemma "\<not> (List.member (remove e l) e)"

  value "remove (1::int) [1,1]"
  apply (induct l)
  apply auto
   apply (simp add: member_rec(2))
  by (simp add: member_rec(1))


lemma count_remove: "(length l) = (length (remove e l)) + (count_list l e)"
  apply (induct l)
   apply auto
  done

lemma "(length (remove e l)) = (length l) \<longrightarrow> \<not> (List.member l e)"
  apply (induct l)
   apply auto
     apply (simp add: member_rec(2))
  apply (metis Suc_n_not_le_n count_remove le_add1)
  apply (metis Suc_n_not_le_n count_remove le_add1)
  by (simp add: member_rec(1))

export_code remove in Haskell

end