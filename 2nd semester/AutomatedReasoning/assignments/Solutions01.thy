theory Solutions01 imports Core_Logic begin

proposition \<open>[] \<then> [(p \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> q] \<then> [p \<rightarrow> q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [p \<rightarrow> p \<rightarrow> q \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p] \<then> [p \<rightarrow> q \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, p] \<then> [q \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[q, p, p] \<then> [q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [(p \<rightarrow> p \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> p \<rightarrow> q] \<then> [p \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, p \<rightarrow> p \<rightarrow> q] \<then> [q]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p \<rightarrow> p \<rightarrow> q, p] \<then> [q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, q]\<close> and \<open>[p \<rightarrow> q, p] \<then> [q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, q]\<close> and \<open>[q, p] \<then> [q]\<close> and \<open>[p] \<then> [p, q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [p \<rightarrow> q \<rightarrow> p]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p] \<then> [q \<rightarrow> p]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[q, p] \<then> [p]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p, q] \<then> [p]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [(p \<rightarrow> r) \<rightarrow> (r \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> r] \<then> [(r \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[r \<rightarrow> q, p \<rightarrow> r] \<then> [p \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, r \<rightarrow> q, p \<rightarrow> r] \<then> [q]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[r \<rightarrow> q, p \<rightarrow> r, p] \<then> [q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p \<rightarrow> r, p] \<then> [r, q]\<close> and \<open>[q, p \<rightarrow> r, p] \<then> [q]\<close>
    using that by force
  with Basic have ?thesis if \<open>[p \<rightarrow> r, p] \<then> [r, q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, r, q]\<close> and \<open>[r, p] \<then> [r, q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p]\<close>
proof -
  from Imp_R have ?thesis if \<open>[(p \<rightarrow> q) \<rightarrow> p] \<then> [p]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[] \<then> [p \<rightarrow> q, p]\<close> and \<open>[p] \<then> [p]\<close>
    using that by force
  with Basic have ?thesis if \<open>[] \<then> [p \<rightarrow> q, p]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p] \<then> [q, p]\<close>
    using that by force
  with Set_R have ?thesis if \<open>[p] \<then> [p, q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

end
