(*
  GENERATED FILE -- do not hand-edit.

  Rendered by scripts/generate_phi.py (repo-side renderer)
  from a MoRDor `isa`-mode JSON document (schema v0.1, docs/MORDOR_ISA_FORMAT.md).

  Source program : uaf-bug-fixed.lit
  Producing cmd  : mordor futures --single uaf-bug-fixed.lit --output-mode isa
                   (rendered: scripts/generate_phi.py <isa.json> -o <this file>)
  Memory orders  : rlx, acq, rel, acq_rel, sc

  Contents:
    * provisional encoding types (WIP, to be replaced by Spike B Core types)
    * the digested program: per-thread `LABEL is INSTRUCTION` lists
    * \<Phi>_uaf_bug_fixed : the future set, one edge-set over event-labels per execution
      (ENRICHED with cross-thread release-handshake edges derived from a
       companion executions-mode JSON's reads-from relation -- see below)

  Notes / faithfulness:
    * Cross-thread release HANDSHAKE edges (W -> R) are DERIVED from
      MoRDor's per-execution reads-from (release-class writer) and added
      to \<Phi>; single-program `futures` does not emit these synchronizes-
      with edges.  Each derived edge is flagged with an inline `text` note
      on the execution it augments (added only where both endpoints occur).
    * RMW (Faa/Cas) is ONE instruction carrying several events (Faa #0,#1;
      Cas #0,#1,#2 -- the W #2 is absent on a failing CAS).
    * Loop-iteration event-labels (e.g. t0.4@1:1#0) are rendered verbatim in \<Phi>.
    * init-scope labels are g.* ; thread-scope labels are t<tid>.* .
    * Edges are normalised before rendering: reflexive (identity) edges are
      DROPPED (the consumer takes reflexive closure, MORDOR_ISA_FORMAT.md s1)
      and exact duplicates removed; first-occurrence order is preserved.
    * Faa/Cas `rmw_op` (strong/weak) has no slot in the provisional command
      type, so it is preserved as an inline Isabelle comment on the entry.
*)

theory Prog_uaf_bug_fixed_generated
  imports Main
begin

section \<open>PROVISIONAL / WIP encoding types\<close>

text \<open>
  The datatypes below are a minimal placeholder vocabulary so that the
  generated digest and \<open>\<Phi>\<close> are well-formed Isabelle.  They are
  intentionally lightweight and are TO BE REPLACED by the Core action /
  command / order types from Spike B.  Nothing here is meant to be definitive.
\<close>

datatype mem_order = rlx | acq | rel | acq_rel | sc

datatype expr =
    EInt int
  | EReg string
  | EEq expr expr
  | EAdd expr expr
  | EOp string "expr list"   \<comment> \<open>generic n-ary operator fall-back\<close>

type_synonym reg = string
type_synonym label = string
type_synonym loop_id = int

text \<open>One source instruction = one abstract \<open>command\<close> with full operands.
  An RMW (\<open>Faa\<close>, \<open>Cas\<close>) is a single command carrying several events.
  Control flow (\<open>If\<close>/\<open>While\<close>/\<open>Do\<close>) keeps the program \emph{rolled}: the
  branches/bodies are themselves digests.\<close>

datatype command =
    Set reg expr
  | ReadPtr mem_order reg expr
  | ReadVar mem_order reg string
  | ReadRef reg string
  | WritePtr mem_order expr expr
  | WriteVar mem_order string expr
  | Faa mem_order mem_order reg expr expr
  | Cas mem_order mem_order reg expr expr expr
  | Alloc reg expr
  | Free expr
  | Fence mem_order
  | If expr "(label \<times> command) list" "(label \<times> command) list"
  | While expr "(label \<times> command) list" loop_id
  | Do expr "(label \<times> command) list" loop_id

text \<open>The digest notation \<open>LABEL is INSTRUCTION\<close>.  (PROVISIONAL: \<open>is\<close> is a
  reserved outer-syntax keyword used in term-abbreviation patterns; should that
  clash, rename this mixfix when wiring in the Spike B Core types.)\<close>

definition entry :: "label \<Rightarrow> command \<Rightarrow> (label \<times> command)"  (infix "is" 49)
  where "lbl is cmd \<equiv> (lbl, cmd)"


section \<open>Digested program: uaf-bug-fixed.lit\<close>

definition prog_uaf_bug_fixed_init :: "(label \<times> command) list" where
  "prog_uaf_bug_fixed_init =
  [
       ''g.1'' is Alloc ''rC'' (EInt 1),
       ''g.2'' is Alloc ''rcu'' (EInt 1),
       ''g.3'' is Set ''rcu'' (EInt 0)
       ]
  "

definition prog_uaf_bug_fixed_t0 :: "(label \<times> command) list" where
  "prog_uaf_bug_fixed_t0 =
  [
       ''t0.1'' is ReadPtr rlx ''rtemp'' (EReg ''rcu''),
       ''t0.2'' is If (EEq (EReg ''rtemp'') (EInt 0))
           [
           ''t0.3'' is Free (EReg ''rC'')
           ]
           []
       ]
  "

definition prog_uaf_bug_fixed_t1 :: "(label \<times> command) list" where
  "prog_uaf_bug_fixed_t1 =
  [
       ''t1.1'' is WritePtr acq (EReg ''rcu'') (EInt 1),
       ''t1.2'' is ReadPtr rlx ''rv'' (EReg ''rC''),
       ''t1.3'' is WritePtr rel (EReg ''rcu'') (EInt 0)
       ]
  "

definition prog_uaf_bug_fixed :: "(label \<times> command) list list" where
  "prog_uaf_bug_fixed = [prog_uaf_bug_fixed_init, prog_uaf_bug_fixed_t0, prog_uaf_bug_fixed_t1]"

text \<open>Static event \<open>\<rightarrow>\<close> instruction map (event-label,
  instruction-label, type).  These are the \emph{rolled} event-labels (no
  \<open>@loop:iter\<close> suffix); the unrolled iter-labels appearing in \<open>\<Phi>\<close>
  collapse onto these via the \<open>lb\<close>-rule (MORDOR_ISA_FORMAT.md s2).\<close>
definition evmap_uaf_bug_fixed :: "(string \<times> string \<times> string) list" where
  "evmap_uaf_bug_fixed = [
  (''g.1#0'', ''g.1'', ''Alloc''),
  (''g.2#0'', ''g.2'', ''Alloc''),
  (''t0.1#0'', ''t0.1'', ''R''),
  (''t0.2#0'', ''t0.2'', ''Branch''),
  (''t0.3#0'', ''t0.3'', ''Dealloc''),
  (''t1.1#0'', ''t1.1'', ''W''),
  (''t1.2#0'', ''t1.2'', ''R''),
  (''t1.3#0'', ''t1.3'', ''W'')
  ]"

section \<open>Future set \<open>\<Phi>\<close>\<close>

text \<open>Each execution contributes one edge-set (\<open>(ppo \<union> dp)\<close> over
  event-labels); \<open>\<Phi>_uaf_bug_fixed\<close> is the set of those edge-sets.\<close>
text \<open>This \<open>\<Phi>\<close> is ENRICHED with cross-thread release-handshake
  edges \<open>(W \<rightarrow> R)\<close> DERIVED from MoRDor's per-execution
  reads-from relation (release-class writer); these are the
  synchronizes-with that single-program \<open>futures\<close> omits.  Each is
  added only to executions whose event-labels already contain both
  endpoints, and is flagged inline below.\<close>

definition \<Phi>_uaf_bug_fixed_exec0 :: "(string \<times> string) set" where
  "\<Phi>_uaf_bug_fixed_exec0 =
  {
  (''g.1#0'', ''t1.2#0''),
  (''g.1#0'', ''t1.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''t1.1#0'', ''t1.3#0''),
  (''t1.2#0'', ''t1.3#0'')
  }"

text \<open>exec 1: +1 derived release-handshake edge(s): t1.3#0 \<rightarrow> t0.1#0\<close>
definition \<Phi>_uaf_bug_fixed_exec1 :: "(string \<times> string) set" where
  "\<Phi>_uaf_bug_fixed_exec1 =
  {
  (''g.1#0'', ''t0.3#0''),
  (''g.1#0'', ''t1.2#0''),
  (''g.1#0'', ''t1.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''t0.1#0'', ''t0.3#0''),
  (''t1.1#0'', ''t1.3#0''),
  (''t1.2#0'', ''t1.3#0''),
  (''t1.3#0'', ''t0.1#0'')
  }"

definition \<Phi>_uaf_bug_fixed :: "(string \<times> string) set set" where
  "\<Phi>_uaf_bug_fixed =
  { \<Phi>_uaf_bug_fixed_exec0,
    \<Phi>_uaf_bug_fixed_exec1 }"

end
