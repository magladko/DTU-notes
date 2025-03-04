theory Exercise2_6 imports Main begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t" 
  apply(induction t)
  by auto

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = a # (contents l) @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

lemma sum_eq: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  by auto

end