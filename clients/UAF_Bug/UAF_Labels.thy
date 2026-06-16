(*
   Shared label-encoding helpers for the UAF client.

   Factored out of UAF_Bug.thy so that the GENERATED future set
   (UAF_Phi_fixed_gen.thy, emitted by scripts/generate_phi.py --core) and the
   proof in UAF_Bug.thy share one definition of il / ev0 / edge.  An instruction
   "<scope>.<seq>" maps to the iloc with that owner and sequence number
   (loop-free: ilo_loops = []); its leading event-label "<scope>.<seq>#0" is
   "sub iloc 0".  Init = mordor g, Thr 0 = reclaimer (t0), Thr 1 = reader (t1).
*)

theory UAF_Labels
  imports "OpSem.OpSem"
begin

section \<open>Owners, instruction-labels, event-labels, edges\<close>

definition il :: "owner \<Rightarrow> nat \<Rightarrow> iloc" where
  "il own s = \<lparr> ilo_owner = own, ilo_seq = s, ilo_loops = [] \<rparr>"

abbreviation "g_il s   \<equiv> il Init s"
abbreviation "t0_il s  \<equiv> il (Thr 0) s"
abbreviation "t1_il s  \<equiv> il (Thr 1) s"

text \<open>The leading event-label @{text "l#0"} of an instruction-label.\<close>
definition ev0 :: "iloc \<Rightarrow> elabel" where
  "ev0 l = sub l 0"

text \<open>An edge over the two instruction-labels' @{text "#0"} sub-events.\<close>
abbreviation edge :: "iloc \<Rightarrow> iloc \<Rightarrow> (elabel \<times> elabel)" where
  "edge a b \<equiv> (ev0 a, ev0 b)"

end
