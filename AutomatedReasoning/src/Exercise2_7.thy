theory Exercise2_7 imports Main Exercise2_6 begin

fun pre_order:: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = a # (pre_order l) @ (pre_order r)"

fun post_order:: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

lemma pre_post: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  by auto

end