theory Cantor_2_Exercises imports Pure_HOL begin

(* Pure_HOL imports Pure and has a simple axiomatization of Higher-Order Logic *)

section \<open>Exercise 1\<close>

(* Remove the sorry in theorem Contradiction: any formula follows from a contradiction *)

theorem Contradiction: \<open>(\<not> p \<longleftrightarrow> p) \<longrightarrow> q\<close>
proof
  assume \<open>\<not> p \<longleftrightarrow> p\<close>
  then have \<open>\<not> p \<Longrightarrow> p\<close> ..
  then have \<open>\<not> p \<longrightarrow> p\<close> ..
  from \<open>\<not> p \<longleftrightarrow> p\<close> have \<open>p \<Longrightarrow> \<not> p\<close> ..
  then have \<open>p \<longrightarrow> \<not> p\<close> ..
  have \<open>p \<or> \<not> p\<close> by (rule LEM)
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
  have \<open>?D c \<longleftrightarrow> ?D c\<close> ..
  from this \<open>?D = f c\<close> have \<open>\<not> f c c \<longleftrightarrow> f c c\<close> ..
  with contradiction show \<bottom> .
qed

(* This is difficult but reuse as much as possible from Cantor_Exercises_1 *)

end
