(*
  GENERATED FILE -- do not hand-edit.

  Rendered by scripts/generate_phi.py --core from a
  MoRDor isa-mode JSON document (schema v0.1, docs/MORDOR_ISA_FORMAT.md).
  Source program : uaf-bug-fixed.lit

  Emits \<Phi>_uaf_bug_fixed over the REAL Core @{typ elabel} types (via the shared
  label helpers il/ev0/edge in UAF_Labels), so the client proof consumes it
  directly: g.<seq>#0 = ev0 (il Init <seq>), t<t>.<seq>#0 = ev0 (il (Thr t) <seq>).

  \<Phi> is ENRICHED with cross-thread release-handshake edges DERIVED from
  MoRDor's per-execution reads-from (release-class writer); flagged inline.
*)

theory UAF_Phi_fixed_gen
  imports UAF_Labels
begin

text \<open>The future set \<open>\<Phi>_uaf_bug_fixed\<close> over Core @{typ elabel}, one
  edge-set per execution; rendered from the MoRDor isa JSON.\<close>

text \<open>exec 0: +1 derived release-handshake edge(s): t1.2#0 \<rightarrow> t0.1#0\<close>
definition \<Phi>_uaf_bug_fixed_exec0 :: future where
  "\<Phi>_uaf_bug_fixed_exec0 =
  {
  edge (il Init 1) (il Init 2),
  edge (il Init 1) (il Init 5),
  edge (il Init 1) (il (Thr 0) 1),
  edge (il Init 1) (il (Thr 1) 1),
  edge (il Init 1) (il (Thr 1) 2),
  edge (il Init 2) (il Init 5),
  edge (il Init 2) (il (Thr 0) 1),
  edge (il Init 2) (il (Thr 1) 1),
  edge (il Init 2) (il (Thr 1) 2),
  edge (il Init 3) (il Init 4),
  edge (il Init 3) (il Init 5),
  edge (il Init 3) (il (Thr 0) 1),
  edge (il Init 3) (il (Thr 1) 1),
  edge (il Init 3) (il (Thr 1) 2),
  edge (il Init 4) (il Init 5),
  edge (il Init 4) (il (Thr 0) 1),
  edge (il Init 4) (il (Thr 1) 1),
  edge (il Init 4) (il (Thr 1) 2),
  edge (il Init 5) (il (Thr 0) 1),
  edge (il Init 5) (il (Thr 1) 1),
  edge (il Init 5) (il (Thr 1) 2),
  edge (il (Thr 1) 1) (il (Thr 1) 2),
  edge (il (Thr 1) 2) (il (Thr 0) 1)
  }"

text \<open>exec 1: +1 derived release-handshake edge(s): t1.2#0 \<rightarrow> t0.1#0\<close>
definition \<Phi>_uaf_bug_fixed_exec1 :: future where
  "\<Phi>_uaf_bug_fixed_exec1 =
  {
  edge (il Init 1) (il Init 2),
  edge (il Init 1) (il Init 5),
  edge (il Init 1) (il (Thr 0) 1),
  edge (il Init 1) (il (Thr 0) 3),
  edge (il Init 1) (il (Thr 1) 1),
  edge (il Init 1) (il (Thr 1) 2),
  edge (il Init 2) (il Init 5),
  edge (il Init 2) (il (Thr 0) 1),
  edge (il Init 2) (il (Thr 0) 3),
  edge (il Init 2) (il (Thr 1) 1),
  edge (il Init 2) (il (Thr 1) 2),
  edge (il Init 3) (il Init 4),
  edge (il Init 3) (il Init 5),
  edge (il Init 3) (il (Thr 0) 1),
  edge (il Init 3) (il (Thr 0) 3),
  edge (il Init 3) (il (Thr 1) 1),
  edge (il Init 3) (il (Thr 1) 2),
  edge (il Init 4) (il Init 5),
  edge (il Init 4) (il (Thr 0) 1),
  edge (il Init 4) (il (Thr 0) 3),
  edge (il Init 4) (il (Thr 1) 1),
  edge (il Init 4) (il (Thr 1) 2),
  edge (il Init 5) (il (Thr 0) 1),
  edge (il Init 5) (il (Thr 0) 3),
  edge (il Init 5) (il (Thr 1) 1),
  edge (il Init 5) (il (Thr 1) 2),
  edge (il (Thr 0) 1) (il (Thr 0) 3),
  edge (il (Thr 1) 1) (il (Thr 1) 2),
  edge (il (Thr 1) 2) (il (Thr 0) 1)
  }"

definition \<Phi>_uaf_bug_fixed :: Phi where
  "\<Phi>_uaf_bug_fixed =
  { \<Phi>_uaf_bug_fixed_exec0,
    \<Phi>_uaf_bug_fixed_exec1 }"

end
