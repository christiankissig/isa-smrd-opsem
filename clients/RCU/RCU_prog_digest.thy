(*
  GENERATED FILE -- do not hand-edit.

  Rendered by scripts/generate_phi.py (repo-side renderer)
  from a mordor `isa`-mode JSON document (schema v0.1, docs/MORDOR_ISA_FORMAT.md).

  Source program : rcu3
  Producing cmd  : mordor futures --single rcu3 --output-mode isa
                   (rendered: scripts/generate_phi.py <isa.json> -o <this file>)
  Memory orders  : rlx, acq, rel, acq_rel, sc

  Contents:
    * provisional encoding types (WIP, to be replaced by Spike B Core types)
    * the digested program: per-thread `LABEL is INSTRUCTION` lists
    * \<Phi>_rcu3 : the future set, one edge-set over event-labels per execution

  Notes / faithfulness:
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

theory RCU_prog_digest
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


section \<open>Digested program: rcu3\<close>

definition prog_rcu3_init :: "(label \<times> command) list" where
  "prog_rcu3_init =
  [
       ''g.1'' is Set ''rN'' (EInt 3),
       ''g.2'' is Alloc ''rrcu'' (EReg ''rN''),
       ''g.3'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EInt 0)) (EInt 0),
       ''g.4'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EInt 1)) (EInt 0),
       ''g.5'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EInt 2)) (EInt 0),
       ''g.6'' is Alloc ''rC'' (EInt 1),
       ''g.7'' is WritePtr rlx (EReg ''rC'') (EInt 0),
       ''g.8'' is Alloc ''rdet'' (EReg ''rN'')
       ]
  "

definition prog_rcu3_t0 :: "(label \<times> command) list" where
  "prog_rcu3_t0 =
  [
       ''t0.1'' is Set ''rtid'' (EInt 0),
       ''t0.2'' is Alloc ''rn'' (EInt 1),
       ''t0.3'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 1),
       ''t0.4'' is Do (EEq (EReg ''rsucc'') (EInt 0))
           [
           ''t0.5'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 0),
           ''t0.6'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 1),
           ''t0.7'' is Faa acq rel ''rs'' (EReg ''rC'') (EInt 0) \<comment> \<open>rmw_op: strong\<close>,
           ''t0.8'' is ReadPtr rlx ''rv'' (EReg ''rs''),
           ''t0.9'' is WritePtr rlx (EReg ''rn'') (EAdd (EReg ''rv'') (EInt 1)),
           ''t0.10'' is Cas acq rel ''rsucc'' (EReg ''rC'') (EReg ''rs'') (EReg ''rn'')
           ]
           1,
       ''t0.11'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 0),
       ''t0.12'' is WritePtr rlx (EAdd (EReg ''rdet'') (EReg ''rtid'')) (EReg ''rs''),
       ''t0.13'' is Alloc ''rr'' (EAdd (EReg ''rN'') (EInt 1)),
       ''t0.14'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 0)),
       ''t0.15'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 0)) (EReg ''rtemp''),
       ''t0.16'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 1)),
       ''t0.17'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 1)) (EReg ''rtemp''),
       ''t0.18'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 2)),
       ''t0.19'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 2)) (EReg ''rtemp''),
       ''t0.20'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 0)),
       ''t0.21'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t0.22'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t0.23'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 0))
               ]
               2
           ]
           [],
       ''t0.24'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 1)),
       ''t0.25'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t0.26'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t0.27'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 1))
               ]
               3
           ]
           [],
       ''t0.28'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 2)),
       ''t0.29'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t0.30'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t0.31'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 2))
               ]
               4
           ]
           [],
       ''t0.32'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rdet'') (EReg ''rtid'')),
       ''t0.33'' is Free (EReg ''rtemp'')
       ]
  "

definition prog_rcu3_t1 :: "(label \<times> command) list" where
  "prog_rcu3_t1 =
  [
       ''t1.1'' is Set ''rtid'' (EInt 1),
       ''t1.2'' is Alloc ''rn'' (EInt 1),
       ''t1.3'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 1),
       ''t1.4'' is Do (EEq (EReg ''rsucc'') (EInt 0))
           [
           ''t1.5'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 0),
           ''t1.6'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 1),
           ''t1.7'' is Faa acq rel ''rs'' (EReg ''rC'') (EInt 0) \<comment> \<open>rmw_op: strong\<close>,
           ''t1.8'' is ReadPtr rlx ''rv'' (EReg ''rs''),
           ''t1.9'' is WritePtr rlx (EReg ''rn'') (EAdd (EReg ''rv'') (EInt 1)),
           ''t1.10'' is Cas acq rel ''rsucc'' (EReg ''rC'') (EReg ''rs'') (EReg ''rn'')
           ]
           5,
       ''t1.11'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 0),
       ''t1.12'' is WritePtr rlx (EAdd (EReg ''rdet'') (EReg ''rtid'')) (EReg ''rs''),
       ''t1.13'' is Alloc ''rr'' (EAdd (EReg ''rN'') (EInt 1)),
       ''t1.14'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 0)),
       ''t1.15'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 0)) (EReg ''rtemp''),
       ''t1.16'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 1)),
       ''t1.17'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 1)) (EReg ''rtemp''),
       ''t1.18'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 2)),
       ''t1.19'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 2)) (EReg ''rtemp''),
       ''t1.20'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 0)),
       ''t1.21'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t1.22'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t1.23'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 0))
               ]
               6
           ]
           [],
       ''t1.24'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 1)),
       ''t1.25'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t1.26'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t1.27'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 1))
               ]
               7
           ]
           [],
       ''t1.28'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 2)),
       ''t1.29'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t1.30'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t1.31'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 2))
               ]
               8
           ]
           [],
       ''t1.32'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rdet'') (EReg ''rtid'')),
       ''t1.33'' is Free (EReg ''rtemp'')
       ]
  "

definition prog_rcu3_t2 :: "(label \<times> command) list" where
  "prog_rcu3_t2 =
  [
       ''t2.1'' is Set ''rtid'' (EInt 2),
       ''t2.2'' is Alloc ''rn'' (EInt 1),
       ''t2.3'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 1),
       ''t2.4'' is Do (EEq (EReg ''rsucc'') (EInt 0))
           [
           ''t2.5'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 0),
           ''t2.6'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 1),
           ''t2.7'' is Faa acq rel ''rs'' (EReg ''rC'') (EInt 0) \<comment> \<open>rmw_op: strong\<close>,
           ''t2.8'' is ReadPtr rlx ''rv'' (EReg ''rs''),
           ''t2.9'' is WritePtr rlx (EReg ''rn'') (EAdd (EReg ''rv'') (EInt 1)),
           ''t2.10'' is Cas acq rel ''rsucc'' (EReg ''rC'') (EReg ''rs'') (EReg ''rn'')
           ]
           9,
       ''t2.11'' is WritePtr rlx (EAdd (EReg ''rrcu'') (EReg ''rtid'')) (EInt 0),
       ''t2.12'' is WritePtr rlx (EAdd (EReg ''rdet'') (EReg ''rtid'')) (EReg ''rs''),
       ''t2.13'' is Alloc ''rr'' (EAdd (EReg ''rN'') (EInt 1)),
       ''t2.14'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 0)),
       ''t2.15'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 0)) (EReg ''rtemp''),
       ''t2.16'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 1)),
       ''t2.17'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 1)) (EReg ''rtemp''),
       ''t2.18'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 2)),
       ''t2.19'' is WritePtr rlx (EAdd (EReg ''rr'') (EInt 2)) (EReg ''rtemp''),
       ''t2.20'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 0)),
       ''t2.21'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t2.22'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t2.23'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 0))
               ]
               10
           ]
           [],
       ''t2.24'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 1)),
       ''t2.25'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t2.26'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t2.27'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 1))
               ]
               11
           ]
           [],
       ''t2.28'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rr'') (EInt 2)),
       ''t2.29'' is If (EEq (EReg ''rtemp'') (EInt 1))
           [
           ''t2.30'' is Do (EEq (EReg ''rtemp'') (EInt 1))
               [
               ''t2.31'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rrcu'') (EInt 2))
               ]
               12
           ]
           [],
       ''t2.32'' is ReadPtr rlx ''rtemp'' (EAdd (EReg ''rdet'') (EReg ''rtid'')),
       ''t2.33'' is Free (EReg ''rtemp'')
       ]
  "

definition prog_rcu3 :: "(label \<times> command) list list" where
  "prog_rcu3 = [prog_rcu3_init, prog_rcu3_t0, prog_rcu3_t1, prog_rcu3_t2]"

text \<open>Static event \<open>\<rightarrow>\<close> instruction map (event-label,
  instruction-label, type).  These are the \emph{rolled} event-labels (no
  \<open>@loop:iter\<close> suffix); the unrolled iter-labels appearing in \<open>\<Phi>\<close>
  collapse onto these via the \<open>lb\<close>-rule (MORDOR_ISA_FORMAT.md s2).\<close>
definition evmap_rcu3 :: "(string \<times> string \<times> string) list" where
  "evmap_rcu3 = [
  (''g.2#0'', ''g.2'', ''Alloc''),
  (''g.3#0'', ''g.3'', ''W''),
  (''g.4#0'', ''g.4'', ''W''),
  (''g.5#0'', ''g.5'', ''W''),
  (''g.6#0'', ''g.6'', ''Alloc''),
  (''g.7#0'', ''g.7'', ''W''),
  (''g.8#0'', ''g.8'', ''Alloc''),
  (''t0.2#0'', ''t0.2'', ''Alloc''),
  (''t0.3#0'', ''t0.3'', ''W''),
  (''t0.4#0'', ''t0.4'', ''Branch''),
  (''t0.5#0'', ''t0.5'', ''W''),
  (''t0.6#0'', ''t0.6'', ''W''),
  (''t0.7#0'', ''t0.7'', ''R''),
  (''t0.7#1'', ''t0.7'', ''W''),
  (''t0.8#0'', ''t0.8'', ''R''),
  (''t0.9#0'', ''t0.9'', ''W''),
  (''t0.10#0'', ''t0.10'', ''R''),
  (''t0.10#1'', ''t0.10'', ''Branch''),
  (''t0.10#2'', ''t0.10'', ''W''),
  (''t0.11#0'', ''t0.11'', ''W''),
  (''t0.12#0'', ''t0.12'', ''W''),
  (''t0.13#0'', ''t0.13'', ''Alloc''),
  (''t0.14#0'', ''t0.14'', ''R''),
  (''t0.15#0'', ''t0.15'', ''W''),
  (''t0.16#0'', ''t0.16'', ''R''),
  (''t0.17#0'', ''t0.17'', ''W''),
  (''t0.18#0'', ''t0.18'', ''R''),
  (''t0.19#0'', ''t0.19'', ''W''),
  (''t0.20#0'', ''t0.20'', ''R''),
  (''t0.21#0'', ''t0.21'', ''Branch''),
  (''t0.22#0'', ''t0.22'', ''Branch''),
  (''t0.23#0'', ''t0.23'', ''R''),
  (''t0.24#0'', ''t0.24'', ''R''),
  (''t0.25#0'', ''t0.25'', ''Branch''),
  (''t0.26#0'', ''t0.26'', ''Branch''),
  (''t0.27#0'', ''t0.27'', ''R''),
  (''t0.28#0'', ''t0.28'', ''R''),
  (''t0.29#0'', ''t0.29'', ''Branch''),
  (''t0.30#0'', ''t0.30'', ''Branch''),
  (''t0.31#0'', ''t0.31'', ''R''),
  (''t0.32#0'', ''t0.32'', ''R''),
  (''t0.33#0'', ''t0.33'', ''Dealloc''),
  (''t1.2#0'', ''t1.2'', ''Alloc''),
  (''t1.3#0'', ''t1.3'', ''W''),
  (''t1.4#0'', ''t1.4'', ''Branch''),
  (''t1.5#0'', ''t1.5'', ''W''),
  (''t1.6#0'', ''t1.6'', ''W''),
  (''t1.7#0'', ''t1.7'', ''R''),
  (''t1.7#1'', ''t1.7'', ''W''),
  (''t1.8#0'', ''t1.8'', ''R''),
  (''t1.9#0'', ''t1.9'', ''W''),
  (''t1.10#0'', ''t1.10'', ''R''),
  (''t1.10#1'', ''t1.10'', ''Branch''),
  (''t1.10#2'', ''t1.10'', ''W''),
  (''t1.11#0'', ''t1.11'', ''W''),
  (''t1.12#0'', ''t1.12'', ''W''),
  (''t1.13#0'', ''t1.13'', ''Alloc''),
  (''t1.14#0'', ''t1.14'', ''R''),
  (''t1.15#0'', ''t1.15'', ''W''),
  (''t1.16#0'', ''t1.16'', ''R''),
  (''t1.17#0'', ''t1.17'', ''W''),
  (''t1.18#0'', ''t1.18'', ''R''),
  (''t1.19#0'', ''t1.19'', ''W''),
  (''t1.20#0'', ''t1.20'', ''R''),
  (''t1.21#0'', ''t1.21'', ''Branch''),
  (''t1.22#0'', ''t1.22'', ''Branch''),
  (''t1.23#0'', ''t1.23'', ''R''),
  (''t1.24#0'', ''t1.24'', ''R''),
  (''t1.25#0'', ''t1.25'', ''Branch''),
  (''t1.26#0'', ''t1.26'', ''Branch''),
  (''t1.27#0'', ''t1.27'', ''R''),
  (''t1.28#0'', ''t1.28'', ''R''),
  (''t1.29#0'', ''t1.29'', ''Branch''),
  (''t1.30#0'', ''t1.30'', ''Branch''),
  (''t1.31#0'', ''t1.31'', ''R''),
  (''t1.32#0'', ''t1.32'', ''R''),
  (''t1.33#0'', ''t1.33'', ''Dealloc''),
  (''t2.2#0'', ''t2.2'', ''Alloc''),
  (''t2.3#0'', ''t2.3'', ''W''),
  (''t2.4#0'', ''t2.4'', ''Branch''),
  (''t2.5#0'', ''t2.5'', ''W''),
  (''t2.6#0'', ''t2.6'', ''W''),
  (''t2.7#0'', ''t2.7'', ''R''),
  (''t2.7#1'', ''t2.7'', ''W''),
  (''t2.8#0'', ''t2.8'', ''R''),
  (''t2.9#0'', ''t2.9'', ''W''),
  (''t2.10#0'', ''t2.10'', ''R''),
  (''t2.10#1'', ''t2.10'', ''Branch''),
  (''t2.10#2'', ''t2.10'', ''W''),
  (''t2.11#0'', ''t2.11'', ''W''),
  (''t2.12#0'', ''t2.12'', ''W''),
  (''t2.13#0'', ''t2.13'', ''Alloc''),
  (''t2.14#0'', ''t2.14'', ''R''),
  (''t2.15#0'', ''t2.15'', ''W''),
  (''t2.16#0'', ''t2.16'', ''R''),
  (''t2.17#0'', ''t2.17'', ''W''),
  (''t2.18#0'', ''t2.18'', ''R''),
  (''t2.19#0'', ''t2.19'', ''W''),
  (''t2.20#0'', ''t2.20'', ''R''),
  (''t2.21#0'', ''t2.21'', ''Branch''),
  (''t2.22#0'', ''t2.22'', ''Branch''),
  (''t2.23#0'', ''t2.23'', ''R''),
  (''t2.24#0'', ''t2.24'', ''R''),
  (''t2.25#0'', ''t2.25'', ''Branch''),
  (''t2.26#0'', ''t2.26'', ''Branch''),
  (''t2.27#0'', ''t2.27'', ''R''),
  (''t2.28#0'', ''t2.28'', ''R''),
  (''t2.29#0'', ''t2.29'', ''Branch''),
  (''t2.30#0'', ''t2.30'', ''Branch''),
  (''t2.31#0'', ''t2.31'', ''R''),
  (''t2.32#0'', ''t2.32'', ''R''),
  (''t2.33#0'', ''t2.33'', ''Dealloc'')
  ]"

section \<open>Future set \<open>\<Phi>\<close>\<close>

text \<open>Each execution contributes one edge-set (\<open>(ppo \<union> dp)\<close> over
  event-labels); \<open>\<Phi>_rcu3\<close> is the set of those edge-sets.\<close>

definition \<Phi>_rcu3_exec0 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec0 =
  {
  (''g.2#0'', ''g.4#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.4#0'', ''t1.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec1 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec1 =
  {
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec2 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec2 =
  {
  (''g.2#0'', ''g.3#0''),
  (''g.2#0'', ''g.4#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.3#0'', ''t0.3#0''),
  (''g.4#0'', ''t1.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec3 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec3 =
  {
  (''g.2#0'', ''g.3#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.3#0'', ''t0.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec4 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec4 =
  {
  (''g.2#0'', ''g.4#0''),
  (''g.2#0'', ''g.5#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.4#0'', ''t1.3#0''),
  (''g.5#0'', ''t2.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec5 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec5 =
  {
  (''g.2#0'', ''g.5#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.5#0'', ''t2.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec6 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec6 =
  {
  (''g.2#0'', ''g.3#0''),
  (''g.2#0'', ''g.4#0''),
  (''g.2#0'', ''g.5#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.3#0'', ''t0.3#0''),
  (''g.4#0'', ''t1.3#0''),
  (''g.5#0'', ''t2.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3_exec7 :: "(string \<times> string) set" where
  "\<Phi>_rcu3_exec7 =
  {
  (''g.2#0'', ''g.3#0''),
  (''g.2#0'', ''g.5#0''),
  (''g.2#0'', ''t0.3#0''),
  (''g.2#0'', ''t1.3#0''),
  (''g.2#0'', ''t2.3#0''),
  (''g.3#0'', ''t0.3#0''),
  (''g.5#0'', ''t2.3#0''),
  (''g.6#0'', ''g.7#0'')
  }"

definition \<Phi>_rcu3 :: "(string \<times> string) set set" where
  "\<Phi>_rcu3 =
  { \<Phi>_rcu3_exec0,
    \<Phi>_rcu3_exec1,
    \<Phi>_rcu3_exec2,
    \<Phi>_rcu3_exec3,
    \<Phi>_rcu3_exec4,
    \<Phi>_rcu3_exec5,
    \<Phi>_rcu3_exec6,
    \<Phi>_rcu3_exec7 }"

end
