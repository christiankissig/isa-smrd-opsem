(*
   Shared label-encoding helpers for the RCU client.

   Mirrors clients/UAF_Bug/UAF_Labels.thy so that the GENERATED RCU future set
   (RCU_Phi_gen.thy, emitted by scripts/generate_phi.py --core) and the proof in
   RCU_Client.thy share ONE definition of il / il_in / ev0 / edge / ev_it.

   An instruction "<scope>.<seq>" maps to the iloc with that owner and sequence
   number (loop-free: ilo_loops = []); its leading event-label "<scope>.<seq>#0"
   is "sub iloc 0".  A loop-iteration event-label "<scope>.<seq>@<loop>:<iter>#<k>"
   maps via `ev_it`: the iloc records the enclosing
   loop (ilo_loops = [loop]) and the elabel records the iteration (el_iters =
   [iter]) and the sub-event index (el_k = k).  Init = the init scope.
*)

theory RCU_Labels
  imports "OpSem.OpSem"
begin

section \<open>Owners, instruction-labels, event-labels, edges\<close>

definition il :: "owner \<Rightarrow> nat \<Rightarrow> iloc" where
  "il own s = \<lparr> ilo_owner = own, ilo_seq = s, ilo_loops = [] \<rparr>"

text \<open>An instruction-label INSIDE loop @{text lp} (the nested @{term While} /
  @{term Do} body): same owner / seq, but recording the enclosing loop.\<close>
definition il_in :: "owner \<Rightarrow> nat \<Rightarrow> loopid \<Rightarrow> iloc" where
  "il_in own s lp = \<lparr> ilo_owner = own, ilo_seq = s, ilo_loops = [lp] \<rparr>"

abbreviation "g_il s   \<equiv> il Init s"
abbreviation "t0_il s  \<equiv> il (Thr 0) s"

text \<open>The leading event-label @{text "l#0"} of an instruction-label.\<close>
definition ev0 :: "iloc \<Rightarrow> elabel" where
  "ev0 l = sub l 0"

text \<open>An edge over the two instruction-labels' @{text "#0"} sub-events.\<close>
abbreviation edge :: "iloc \<Rightarrow> iloc \<Rightarrow> (elabel \<times> elabel)" where
  "edge a b \<equiv> (ev0 a, ev0 b)"

text \<open>A loop-iteration event-label @{text "<own>.<seq>@<lp>:<it>#<k>"}: the elabel
  whose iloc records the enclosing loop @{text lp} (via @{term il_in}) and whose
  @{term el_iters} records the iteration @{text it}, with sub-event index
  @{text k}.  For @{text "k = 0"} this is the leading event of the loop-body
  instruction at iteration @{text it}.\<close>
definition ev_it :: "owner \<Rightarrow> nat \<Rightarrow> loopid \<Rightarrow> iter \<Rightarrow> nat \<Rightarrow> elabel" where
  "ev_it own s lp it k =
     \<lparr> el_iloc = il_in own s lp, el_iters = [it], el_k = k \<rparr>"

end
