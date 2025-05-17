theory Prog_Prove_Solutions_1 imports Main begin

section \<open>Exercise 2.1\<close>

value \<open>1 + (2::nat)\<close>

value \<open>1 + (2::int)\<close>

value \<open>1 - (2::nat)\<close>

value \<open>1 - (2::int)\<close>

section \<open>Exercise 2.2\<close>

fun add :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>add 0 n = n\<close> |
  \<open>add (Suc m) n = Suc (add m n)\<close>

lemma add_01: \<open>add m (add mn n) = add (add m mn) n\<close>
  apply (induction m)
   apply auto
  done

lemma add_02 [simp]: \<open>add m 0 = m\<close>
  apply (induction m)
   apply auto
  done

lemma add_03 [simp]: \<open>add m (Suc n) = Suc (add m n)\<close>
  apply (induction m)
   apply auto
  done

lemma add_04: \<open>add m n = add n m\<close>
  apply (induction m)
   apply auto
  done

fun double :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>double 0 = 0\<close> |
  \<open>double (Suc m) = Suc (Suc (double m))\<close>

theorem \<open>double m = add m m\<close>
  apply (induction m)
   apply auto
  done

section \<open>Exercise 2.3\<close>

fun count :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>count _ [] = 0\<close> |
  \<open>count x (y # xs) = (if x = y then Suc (count x xs) else count x xs)\<close>

lemma \<open>count x xs \<le> length xs\<close>
  apply (induction xs)
   apply auto
  done

section \<open>Exercise 2.4\<close>

fun snoc :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> 'a list\<close> where
  \<open>snoc [] x = [x]\<close> |
  \<open>snoc (y # ys) x = y # snoc ys x\<close>

fun reverse :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>reverse [] = []\<close> |
  \<open>reverse (x # xs) = snoc (reverse xs) x\<close>

lemma [simp]: \<open>reverse (snoc xs x) = x # reverse xs\<close>
  apply (induction xs)
   apply auto
  done

lemma \<open>reverse (reverse xs) = xs\<close>
  apply (induction xs)
   apply auto
  done

section \<open>Exercise 2.5\<close>

fun sum_upto :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>sum_upto 0 = 0\<close> |
  \<open>sum_upto (Suc n) = Suc n + sum_upto n\<close>

lemma \<open>sum_upto n = n * (n + 1) div 2\<close>
  apply (induction n)
   apply auto
  done

section \<open>Exercise 2.6\<close>

datatype 'a tree = Tip | Node \<open>'a tree\<close> \<open>'a\<close> \<open>'a tree\<close>

fun contents :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>contents Tip = []\<close> |
  \<open>contents (Node l a r) = contents l @ a # contents r\<close>

fun sum_tree :: \<open>nat tree \<Rightarrow> nat\<close> where
  \<open>sum_tree Tip = 0\<close> |
  \<open>sum_tree (Node l a r) = sum_tree l + a + sum_tree r\<close>

lemma \<open>sum_tree t = sum_list (contents t)\<close>
  apply (induction t)
   apply auto
  done

section \<open>Exercise 2.7\<close>

fun mirror :: \<open>'a tree \<Rightarrow> 'a tree\<close> where
  \<open>mirror Tip = Tip\<close> |
  \<open>mirror (Node l a r) = Node (mirror r) a (mirror l)\<close>

fun pre_order :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>pre_order Tip = []\<close> |
  \<open>pre_order (Node l a r) = a # pre_order l @ pre_order r\<close>

fun post_order :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>post_order Tip = []\<close> |
  \<open>post_order (Node l a r) = post_order l @ post_order r @ [a]\<close>

lemma \<open>pre_order (mirror t) = rev (post_order t)\<close>
  apply (induction t)
   apply auto
  done

section \<open>Exercise 3.1\<close>

fun set :: \<open>'a tree \<Rightarrow> 'a set\<close> where
  \<open>set Tip = {}\<close> |
  \<open>set (Node l a r) = set l \<union> {a} \<union> set r\<close>

fun ord :: \<open>int tree \<Rightarrow> bool\<close> where
  \<open>ord Tip = True\<close> |
  \<open>ord (Node l a r) = ((\<forall>i \<in> set l. i < a) \<and> ord l \<and>
                       (\<forall>i \<in> set r. a < i) \<and> ord r)\<close>

fun ins :: \<open>int \<Rightarrow> int tree \<Rightarrow> int tree\<close> where
  \<open>ins i Tip = Node Tip i Tip\<close> |
  \<open>ins i (Node l a r) = (if i < a then Node (ins i l) a r else
                         if a < i then Node l a (ins i r) else Node l a r)\<close>

lemma [simp]: \<open>set (ins i t) = {i} \<union> set t\<close>
  by (induction t) auto

lemma \<open>ord t \<Longrightarrow> ord (ins i t)\<close>
  by (induction t) simp_all

section \<open>Exercise 3.2\<close>

inductive palindrome :: \<open>'a list \<Rightarrow> bool\<close> where
  \<open>palindrome []\<close> |
  \<open>palindrome [_]\<close> |
  \<open>palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])\<close>

lemma \<open>palindrome xs \<Longrightarrow> rev xs = xs\<close>
  by (induction rule: palindrome.induct) simp_all

end
