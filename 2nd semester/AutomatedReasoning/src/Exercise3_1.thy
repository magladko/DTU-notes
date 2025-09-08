theory Exercise3_1 imports Main begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l a r) = {a} \<union> (set l) \<union> (set r)"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node (Node ll b lr) a (Node rl c rr)) = 
      ((b < a) \<and> (a < c) \<and> (ord ll) \<and> (ord lr) \<and> (ord rl) \<and> (ord rr))" |
"ord (Node (Node l b r) a Tip) = ((b < a) \<and> (ord l) \<and> (ord r))" |
"ord (Node Tip a (Node l c r)) = ((a < c) \<and> (ord l) \<and> (ord r))" |
"ord (Node Tip a Tip) = True"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins a Tip = (Node Tip a Tip)" |
"ins a (Node l b r) = (if a = b then (Node l b r) else
                        (if a < b then (Node(ins a l) b r) else (Node l b (ins a r))))"

theorem theorem1: "set (ins x t) = {x} \<union> set t"
  apply(induction t)
  by auto

theorem theorem2: "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t rule: ord.induct)
  by auto

end