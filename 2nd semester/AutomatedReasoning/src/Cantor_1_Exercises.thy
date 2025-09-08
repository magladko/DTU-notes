theory Cantor_1_Exercises imports Simple_Main begin

(* Simple_Main is Main with notation False (\<open>\<bottom>\<close>) and True (\<open>\<top>\<close>) *)

section \<open>Exercise 1\<close>

(* Remove the sorry in theorem Contradiction: any formula follows from a contradiction *)

theorem Contradiction: \<open>(\<not> p \<longleftrightarrow> p) \<longrightarrow> q\<close>
proof
  assume \<open>\<not> p \<longleftrightarrow> p\<close>
  then have \<open>\<not> p \<longrightarrow> p\<close> ..
  from \<open>\<not> p \<longleftrightarrow> p\<close> have \<open>p \<longrightarrow> \<not> p\<close> ..
  have \<open>\<not> p \<or> p\<close> ..
  then show \<open>q\<close>
  proof
    assume \<open>p\<close>
    from \<open>p \<longrightarrow> \<not> p\<close> and this have \<open>\<not> p\<close> ..
    from \<open>\<not> p\<close> and \<open>p\<close> have \<open>\<bottom>\<close> ..
    then show \<open>q\<close> ..
  next
    assume \<open>\<not> p\<close>
    from \<open>\<not> p \<longrightarrow> p\<close> and this have \<open>p\<close> ..
    from \<open>\<not> p\<close> and \<open>p\<close> have \<open>\<bottom>\<close> ..
    then show \<open>q\<close> ..
  qed
qed

theorem contradiction:  \<open>\<not> p \<longleftrightarrow> p \<Longrightarrow> q\<close>
  using Contradiction ..

section \<open>Exercise 2\<close>

(* Remove the sorry in theorem Cantor: every set has more subsets than members *)

theorem Cantor: \<open>\<not> (\<exists>f. \<forall>s :: 'a \<Rightarrow> bool. \<exists>x :: 'a. s = f x)\<close>
proof
  assume \<open>\<exists>f. \<forall>s :: 'a \<Rightarrow> bool. \<exists>x :: 'a. s = f x\<close>
  then obtain f where \<open>\<forall>s :: 'a \<Rightarrow> bool. \<exists>x :: 'a. s = f x\<close> ..
  let ?D = \<open>\<lambda>x. \<not> f x x\<close>
  from \<open>\<forall>s. \<exists>x. s = f x\<close> have \<open>\<exists>x. ?D = f x\<close> ..
  then obtain c where \<open>?D = f c\<close> ..
  then have \<open>\<not> f c c \<longleftrightarrow> f c c\<close>
    by metis
    (*sorry*)
  with contradiction show \<bottom> .
qed

(* Study the given proof steps in order to be ready for Cantor_2_Exercises *)

end
