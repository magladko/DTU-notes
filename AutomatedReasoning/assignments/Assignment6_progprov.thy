theory Assignment6_progprov imports Main begin

section \<open>3.5\<close>

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S_empty: "S []" |
S_wrap: "S w \<Longrightarrow> S (a # w @ [b])" |
S_con: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_empty: "T []" |
T_case: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ [a] @ w2 @ [b])"

lemma T_S: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(rule S.S_empty)
  by (simp add: S_con S_wrap)

lemma t_con: "T w2 \<Longrightarrow> T w1 \<Longrightarrow> T (w1 @ w2)"
  apply(induction w2 arbitrary: w1 rule: T.induct)
   apply simp_all
  by (metis T_case append.left_neutral append_Cons append_assoc)

lemma S_T: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
    apply(rule T.T_empty)
  using T_case T_empty apply fastforce
  apply(rule t_con)
  apply blast
  by blast

lemma "S w = T w"
  using S_T T_S by blast

section \<open>4.7\<close>

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0 [] = True" |
"balanced n (a # w) = balanced (Suc n) w" |
"balanced (Suc n) (b # w) = balanced n w" |
"balanced n w = False"

lemma middle_insert: "S (w1 @ w2) \<Longrightarrow> S (w1 @ [a, b] @ w2)"
proof (induct \<open>w1 @ w2\<close> arbitrary: w1 w2 rule: S.induct)
  case S_empty
  then show ?case
    using S.S_empty S_wrap by force
next
  case (S_wrap w)
  then show ?case
  proof (cases \<open>length w1 = 0\<close>)
    case True
    then have \<open>w1 = []\<close> by simp
    then show ?thesis
      by (metis S.S_wrap S_con S_empty S_wrap.hyps(1,3) append_Nil)
  next
    case False
    then obtain w1' where \<open>w1 = a # w1'\<close>
      by (metis Cons_eq_append_conv S_wrap.hyps(3) list.size(3))
    then show ?thesis
    proof (cases \<open>length w2 = 0\<close>)
      case True
      then have \<open>w2 = []\<close> by simp
      then show ?thesis
        by (metis Cons_eq_append_conv S.simps S_wrap.hyps(1,3) append_Nil2)
    next
      case False
      then obtain w2' where \<open>w2 = w2' @ [b]\<close>
        by (metis S_wrap.hyps(3) last.simps last_appendR list.size(3)
            snoc_eq_iff_butlast)
      have \<open>w1 @ [a, b] @ w2 = a # w1' @ [a, b] @ w2' @ [b]\<close>
        by (simp add: \<open>w1 = a # w1'\<close> \<open>w2 = w2' @ [b]\<close>)
      moreover obtain w where \<open>w = w1' @ [a, b] @ w2'\<close> by auto
      moreover have \<open>w1 @ [a, b] @ w2 = a # w @ [b]\<close>
        using calculation(1,2) by force
      ultimately show ?thesis
        using S.S_wrap S_wrap.hyps(2,3) \<open>w2 = w2' @ [b]\<close> by fastforce
    qed
  qed
next
  case (S_con w1' w2')
  show ?case
  proof (cases "length w1' \<ge> length w1")
    case True
    obtain u v where \<open>w1' = u @ v\<close> \<open>u = w1\<close>
      by (metis S_con.hyps(5) True append_eq_append_conv_if append_eq_conv_conj)
    then have \<open>v @ w2' = w2\<close> using S_con.hyps(5) by auto
    also have \<open>S (u @ [a,b] @ v)\<close> using S_con.hyps(2) \<open>w1' = u @ v\<close> by presburger
    then have \<open>S (u @ [a, b] @ v @ w2')\<close>
      by (metis S.S_con S_con.hyps(3) append.assoc)
    then show ?thesis
      using \<open>v @ w2' = w2\<close> \<open>u = w1\<close> by blast
  next
    case False
    obtain u v where \<open>w2' = u @ v\<close> \<open>w1' @ u = w1\<close> \<open>v = w2\<close>
      by (metis False S_con.hyps(5) append_eq_append_conv_if append_eq_conv_conj)
    then have \<open>S (u @ [a, b] @ v)\<close> using local.S_con(4) by blast
    then show ?thesis
      using S.S_con S_con.hyps(1) \<open>v = w2\<close> \<open>w1' @ u = w1\<close> by force
  qed
qed

lemma BSrep: "balanced n w \<Longrightarrow> S (replicate n a @ w)"
proof (induct n w rule: balanced.induct)
  case 1
  then show ?case
    using S_empty by auto
next
  case (2 n w)
  then show ?case
    by (simp add: replicate_app_Cons_same)
next
  case (3 n w)
  then show ?case
  proof -
    have "replicate (Suc n) a @ b # w = replicate n a @ [a] @ [b] @ w"
      by (simp add: replicate_app_Cons_same)
    
    also have h1: "S (replicate n a @ w)" using "3.hyps" "3.prems" by auto
    have "S (replicate n a @ [a] @ [b] @ w)"
      proof -
        from h1 have "S ([a] @ (replicate n a @ w) @ [b])"
          using S_wrap by force
        then show ?thesis using h1 middle_insert by auto
      qed
    ultimately show ?thesis by simp
  qed
next
  case ("4_1" v)
  then show ?case by simp
next
  case ("4_2" va)
  then show ?case by simp
qed

lemma SrepB: "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induct \<open>replicate n a @ w\<close> arbitrary: n w rule: balanced.induct)
  case 1
  then show ?case by simp
next
  case (2 n w')
  then obtain n' v where repl: \<open>w = replicate n' a @ [b] @ v\<close> sorry
  then obtain m where \<open>m = n + n'\<close> by blast
  then have \<open>m > 0\<close> using "2.hyps"(2) repl
    by (metis add.right_neutral alpha.distinct(1) append_Cons append_Nil
        bot_nat_0.not_eq_extremum list.inject not_add_less2 replicate_0)
  then have \<open>a # w' = replicate m a @ [b] @ v\<close>
    by (simp add: "2.hyps"(2) \<open>m = n + n'\<close> repl replicate_add)
  then have \<open>w' = replicate (m-1) a @ [b] @ v\<close>
    by (metis \<open>0 < m\<close> gr0_conv_Suc list.distinct(1) list.sel(3) replicate_Suc tl_append2
        tl_replicate)

  then show ?case sorry
next
  case (3 n w')
  then show ?case sorry
next
  case ("4_1" v)
  then show ?case by simp
next
  case ("4_2" va)
  then show ?case sorry
qed

lemma "balanced n w = S (replicate n a @ w)"
proof -
  show ?thesis using SrepB BSrep by blast
qed

end