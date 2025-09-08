theory Assignment1 imports Core_Logic begin

proposition \<open>[] \<then> [(q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r]\<close>
proof -
  from Imp_R have ?thesis if \<open>[(q \<rightarrow> r)] \<then> [(p \<rightarrow> q) \<rightarrow> p \<rightarrow> r]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[(p \<rightarrow> q), (q \<rightarrow> r)] \<then> [p \<rightarrow> r]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, (p \<rightarrow> q), (q \<rightarrow> r)] \<then> [r]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[(q \<rightarrow> r), p, (p \<rightarrow> q)] \<then> [r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p, (p \<rightarrow> q)] \<then> [q, r]\<close> and \<open>[r, p, (p \<rightarrow> q)] \<then> [r]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p \<rightarrow> q, p] \<then> [q, r]\<close> and \<open>[r, p, (p \<rightarrow> q)] \<then> [r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, q, r]\<close> and \<open>[q, p] \<then> [q, r]\<close> and \<open>[r, p, (p \<rightarrow> q)] \<then> [r]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [(p \<rightarrow> q \<rightarrow> r) \<rightarrow> q \<rightarrow> p \<rightarrow> r]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> q \<rightarrow> r] \<then> [q \<rightarrow> p \<rightarrow> r]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[q, p \<rightarrow> q \<rightarrow> r] \<then> [p \<rightarrow> r]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, q, p \<rightarrow> q \<rightarrow> r] \<then> [r]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p \<rightarrow> q \<rightarrow> r, p, q] \<then> [r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p, q] \<then> [p, r]\<close> and \<open>[q \<rightarrow> r, p, q] \<then> [r]\<close>
    using that by force
  with Basic have ?thesis if \<open>[q \<rightarrow> r, p, q] \<then> [r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p, q] \<then> [q, r]\<close> and \<open>[r, p, q] \<then> [r]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[q, p] \<then> [q, r]\<close> and \<open>[r, p, q] \<then> [r]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

proposition \<open>[] \<then> [(p \<rightarrow> q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> q \<rightarrow> r] \<then> [(p \<rightarrow> q) \<rightarrow> p \<rightarrow> r]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p \<rightarrow> q, p \<rightarrow> q \<rightarrow> r] \<then> [p \<rightarrow> r]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, p \<rightarrow> q, p \<rightarrow> q \<rightarrow> r] \<then> [r]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p \<rightarrow> q \<rightarrow> r, p, p \<rightarrow> q] \<then> [r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p, p \<rightarrow> q] \<then> [p, r]\<close> and \<open>[q \<rightarrow> r, p, p \<rightarrow> q] \<then> [r]\<close>
    using that by force
  with Basic have ?thesis if \<open>[q \<rightarrow> r, p, p \<rightarrow> q] \<then> [r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p, p \<rightarrow> q] \<then> [q, r]\<close> and \<open>[r, p, p \<rightarrow> q] \<then> [r]\<close>
    using that by force
  with Basic have ?thesis if \<open>[p, p \<rightarrow> q] \<then> [q, r]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p \<rightarrow> q, p] \<then> [q, r]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, q, r]\<close> and \<open>[q, p] \<then> [q, r]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

end