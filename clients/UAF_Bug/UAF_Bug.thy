(*  Title:      clients/UAF_Bug/UAF_Bug.thy
    Author:     Christian Kissig

    The paper's minimal 2-thread use-after-free example, instantiated against the
    Episodic OpSem stack.  Reproduces the headline result `tab-fut-step-bug` /
    `-fix`: the UAF is REACHABLE in the buggy program and EXCLUDED in the fixed one.

    Structural source of truth: the generated program + Phi.  Here everything
    is in the REAL Core / EventStruct / MemSem / OpSem types, session-qualified.

    The two source programs are now IDENTICAL except for the exit
    write's memory order (relaxed in the bug, release in the fixed):

      uaf-bug.lit                          uaf-bug-fixed.lit
      ----------------------------------   ----------------------------------------
      g.1 alloc  rC := 1                   g.1 alloc  rC := 1
      g.2 W_rlx *rC := 0                   g.2 W_rlx *rC := 0
      g.3 alloc  rcu := 1                  g.3 alloc  rcu := 1
      g.4 W_rlx *rcu := 1                  g.4 W_rlx *rcu := 1
      g.5 fence(acq_rel)                   g.5 fence(acq_rel)
      ----------------------------------   ----------------------------------------
      t0.1 R_rlx rtemp := *rcu             t0.1 R_rlx rtemp := *rcu
      t0.2 if rtemp = 0:                   t0.2 if rtemp = 0:
      t0.3    free rC                      t0.3    free rC
      ----------------------------------   ----------------------------------------
      t1.1 R_rlx rv := *rC   (DEREF)       t1.1 R_rlx rv := *rC   (DEREF)
      t1.2 W_rlx *rcu := 0   (EXIT, rlx)   t1.2 W_REL *rcu := 0   (EXIT, REL)

    The ONLY semantic difference: the exit write's `mem_order` -- RELAXED (t1.2) in the
    bug, RELEASE in the fixed -- which is exactly what makes the deref->exit ppo edge
    PRESENT in the fixed futures (t1.1#0 -> t1.2#0) and ABSENT in the bug's.  That edge
    orders the deref `Read rC` (t1.1) before the exit; combined with the release/acquire
    rcu handshake (the cross-thread edge t1.2#0 -> t0.1#0, release-exit -> reclaimer-read)
    it keeps `Dealloc rC` out of the horizon until the deref has committed -- excluding the
    UAF.  The init `fence(acq_rel)` (g.5) is present in both programs.
*)

theory UAF_Bug
  imports "OpSem.OpSem" UAF_Labels UAF_Phi_fixed_gen
begin

section \<open>Owners, labels, and the label-encoding helpers\<close>

text \<open>The two worker threads are @{term "Thr 0"} (the reclaimer, @{text t0})
  and @{term "Thr 1"} (the reader, @{text t1}); the init preamble is
  @{term Init} (@{text g}).  The label-encoding helpers @{term il} / @{term ev0}
  / @{term edge} live in @{text UAF_Labels} (imported above), shared with the
  GENERATED future set @{text UAF_Phi_fixed_gen}.\<close>

text \<open>The program variables / registers used (Core: @{typ var} = @{typ reg} =
  @{typ string}).\<close>
abbreviation "vC    \<equiv> ''rC''"     \<comment> \<open>the reclaimable object pointer variable\<close>
abbreviation "vrcu  \<equiv> ''rcu''"    \<comment> \<open>the rcu handshake flag\<close>
abbreviation "rtemp \<equiv> ''rtemp''"  \<comment> \<open>t0 local: the rcu read\<close>
abbreviation "rv    \<equiv> ''rv''"      \<comment> \<open>t1 local: the deref read\<close>


section \<open>The buggy program @{text prog_uaf_bug} (Core-typed labelled commands)\<close>

text \<open>Faithful to the generated @{text "Prog_uaf_bug"} program, retyped into Core's
  @{typ command} / @{typ instr}.  The free of @{text rC} sits inside the
  @{term IfElse} body (nested), as in the source; the top-level program is the flat instruction
  list (the @{type owner} in each @{typ iloc} separates init / t0 / t1).\<close>

definition prog_uaf_bug :: program where
  "prog_uaf_bug =
   [ \<comment> \<open>init: allocate + publish rC, allocate + raise rcu, then an acq_rel fence\<close>
     g_il 1  is Malloc   vC (EInt 1),
     g_il 2  is WritePtr Rlx (EReg vC)   (EInt 0),
     g_il 3  is Malloc   vrcu (EInt 1),
     g_il 4  is WritePtr Rlx (EReg vrcu) (EInt 1),
     g_il 5  is CFence   Acq_rel,
     \<comment> \<open>t0 (reclaimer): read rcu; if it is 0, free rC\<close>
     t0_il 1 is ReadPtr  Rlx rtemp (EReg vrcu),
     t0_il 2 is IfElse   (EEq (EReg rtemp) (EInt 0))
                 [ t0_il 3 is Free vC ]
                 [],
     \<comment> \<open>t1 (reader): DEREF rC, then RELAXED exit write of rcu\<close>
     t1_il 1 is ReadPtr  Rlx rv (EReg vC),
     t1_il 2 is WritePtr Rlx (EReg vrcu) (EInt 0)
   ]"

text \<open>OpSem's step rules address instructions in the FLATTENED program
  @{term "instrs prog_uaf_bug"} (so that the free nested in @{text "t0.2"}'s THEN body
  is reachable at all).  For the top-level instructions that is no extra work:
  flattening only adds entries.\<close>
lemma instrs_prog_uaf_bugI: "i \<in> set prog_uaf_bug \<Longrightarrow> i \<in> set (instrs prog_uaf_bug)"
  using set_prog_subset_instrs by blast

text \<open>The labels the UAF argument turns on, in the BUG program.\<close>
definition bug_free_il   :: iloc where "bug_free_il   = t0_il 3"   \<comment> \<open>@{text "free rC"}\<close>
definition bug_deref_il  :: iloc where "bug_deref_il  = t1_il 1"   \<comment> \<open>@{text "R rC"} (deref)\<close>
definition bug_exit_il   :: iloc where "bug_exit_il   = t1_il 2"   \<comment> \<open>@{text "W rcu"} (exit)\<close>


section \<open>The fixed program @{text prog_uaf_fixed}\<close>

text \<open>Faithful to the generated @{text "Prog_uaf_bug_fixed"} program.  The fixed program
  is now IDENTICAL to @{term prog_uaf_bug} except for the reader's exit write: it lowers
  rcu with a RELEASE write (@{text "t1.2"}, @{term Rel}) rather than a relaxed one.  That
  release is the only change w.r.t. the bug at the action level; at the @{typ Phi} level
  it (i) adds the deref->exit ppo edge @{text "t1.1#0 -> t1.2#0"} and (ii) through the
  release/acquire rcu handshake induces the cross-thread edge @{text "t1.2#0 -> t0.1#0"}.\<close>

definition prog_uaf_fixed :: program where
  "prog_uaf_fixed =
   [ \<comment> \<open>init: allocate + publish rC, allocate + raise rcu, then an acq_rel fence\<close>
     g_il 1  is Malloc   vC (EInt 1),
     g_il 2  is WritePtr Rlx (EReg vC)   (EInt 0),
     g_il 3  is Malloc   vrcu (EInt 1),
     g_il 4  is WritePtr Rlx (EReg vrcu) (EInt 1),
     g_il 5  is CFence   Acq_rel,
     \<comment> \<open>t0 (reclaimer): read rcu; if it is 0, free rC\<close>
     t0_il 1 is ReadPtr  Rlx rtemp (EReg vrcu),
     t0_il 2 is IfElse   (EEq (EReg rtemp) (EInt 0))
                 [ t0_il 3 is Free vC ]
                 [],
     \<comment> \<open>t1 (reader): DEREF rC, then RELEASE exit write of rcu\<close>
     t1_il 1 is ReadPtr  Rlx rv (EReg vC),
     t1_il 2 is WritePtr Rel (EReg vrcu) (EInt 0)
   ]"

text \<open>The corresponding labels in the FIXED program.  The program is structurally the
  same as the bug, so the free / deref / exit sit at the same instruction-labels; only
  the exit's memory order differs.\<close>
definition fix_free_il   :: iloc where "fix_free_il   = t0_il 3"   \<comment> \<open>@{text "free rC"}\<close>
definition fix_deref_il  :: iloc where "fix_deref_il  = t1_il 1"   \<comment> \<open>@{text "R rC"} (deref)\<close>
definition fix_exit_il   :: iloc where "fix_exit_il   = t1_il 2"   \<comment> \<open>@{text "W_REL rcu"} (exit)\<close>


section \<open>The future sets @{text Phi_uaf} / @{text Phi_uaf_fixed} (EventStruct Phi)\<close>

text \<open>Each execution's edge-set is rendered over @{typ elabel} via @{term ev0}
  (every event here is a single leading sub-event @{text "#0"}).  These are the
  generated edge-sets of the bug / fixed programs, retyped.  The
  @{term edge} abbreviation lives in @{text UAF_Labels}.\<close>

subsection \<open>@{text Phi_uaf} (the bug)\<close>

text \<open>The @{text \<open>fence(acq_rel)\<close>} at @{text \<open>g.5\<close>} collapses the bug's future set to two
  distinct edge-sets: @{term Phi_uaf_exec0} (no free) and @{term Phi_uaf_exec1} (the
  free-bearing WITNESS).  (The generated @{text "\<Phi>_uaf_bug"} lists a third
  execution whose edge-set is identical to @{term Phi_uaf_exec1}; as a set of futures it
  contributes nothing, so we retype the two distinct ones.)\<close>

definition Phi_uaf_exec0 :: future where
  "Phi_uaf_exec0 =
   { edge (g_il 1) (g_il 2), edge (g_il 1) (g_il 5), edge (g_il 1) (t0_il 1),
     edge (g_il 1) (t1_il 1), edge (g_il 1) (t1_il 2),
     edge (g_il 2) (g_il 5), edge (g_il 2) (t0_il 1), edge (g_il 2) (t1_il 1),
     edge (g_il 2) (t1_il 2),
     edge (g_il 3) (g_il 4), edge (g_il 3) (g_il 5), edge (g_il 3) (t0_il 1),
     edge (g_il 3) (t1_il 1), edge (g_il 3) (t1_il 2),
     edge (g_il 4) (g_il 5), edge (g_il 4) (t0_il 1), edge (g_il 4) (t1_il 1),
     edge (g_il 4) (t1_il 2),
     edge (g_il 5) (t0_il 1), edge (g_il 5) (t1_il 1), edge (g_il 5) (t1_il 2) }"

text \<open>exec1 is the UAF WITNESS execution: @{text "free rC"} (@{text "t0.3#0"}) has
  predecessors @{text "{g.1#0, g.2#0, g.3#0, g.4#0, g.5#0, t0.1#0}"} only -- the DEREF
  @{text "t1.1#0"} is NOT among them, so the free can be enabled with the deref still
  pending.\<close>
definition Phi_uaf_exec1 :: future where
  "Phi_uaf_exec1 =
   { edge (g_il 1) (g_il 2), edge (g_il 1) (g_il 5), edge (g_il 1) (t0_il 1),
     edge (g_il 1) (t0_il 3), edge (g_il 1) (t1_il 1), edge (g_il 1) (t1_il 2),
     edge (g_il 2) (g_il 5), edge (g_il 2) (t0_il 1), edge (g_il 2) (t0_il 3),
     edge (g_il 2) (t1_il 1), edge (g_il 2) (t1_il 2),
     edge (g_il 3) (g_il 4), edge (g_il 3) (g_il 5), edge (g_il 3) (t0_il 1),
     edge (g_il 3) (t0_il 3), edge (g_il 3) (t1_il 1), edge (g_il 3) (t1_il 2),
     edge (g_il 4) (g_il 5), edge (g_il 4) (t0_il 1), edge (g_il 4) (t0_il 3),
     edge (g_il 4) (t1_il 1), edge (g_il 4) (t1_il 2),
     edge (g_il 5) (t0_il 1), edge (g_il 5) (t0_il 3), edge (g_il 5) (t1_il 1),
     edge (g_il 5) (t1_il 2),
     edge (t0_il 1) (t0_il 3) }"

definition Phi_uaf :: Phi where
  "Phi_uaf = { Phi_uaf_exec0, Phi_uaf_exec1 }"

subsection \<open>@{text Phi_uaf_fixed} (the fix)\<close>

text \<open>This is the PROVISIONAL, single-program render (the un-enriched futures of
  @{text "uaf-bug-fixed"}): exec0 has no free; exec1 is the one containing @{text "free
  rC"} (@{text "t0.3#0"}).  In BOTH, the deref->exit edge @{text "t1.1#0 -> t1.2#0"} is
  PRESENT (the release exit's ppo predecessor) -- the discriminator absent in the bug.
  These edge-sets are the generated @{term \<Phi>_uaf_bug_fixed} MINUS the derived
  cross-thread handshake edge @{text "t1.2#0 -> t0.1#0"}; see the HONESTY NOTE below.\<close>

definition Phi_uaf_fixed_exec0 :: future where
  "Phi_uaf_fixed_exec0 =
   { edge (g_il 1) (g_il 2), edge (g_il 1) (g_il 5), edge (g_il 1) (t0_il 1),
     edge (g_il 1) (t1_il 1), edge (g_il 1) (t1_il 2),
     edge (g_il 2) (g_il 5), edge (g_il 2) (t0_il 1), edge (g_il 2) (t1_il 1),
     edge (g_il 2) (t1_il 2),
     edge (g_il 3) (g_il 4), edge (g_il 3) (g_il 5), edge (g_il 3) (t0_il 1),
     edge (g_il 3) (t1_il 1), edge (g_il 3) (t1_il 2),
     edge (g_il 4) (g_il 5), edge (g_il 4) (t0_il 1), edge (g_il 4) (t1_il 1),
     edge (g_il 4) (t1_il 2),
     edge (g_il 5) (t0_il 1), edge (g_il 5) (t1_il 1), edge (g_il 5) (t1_il 2),
     edge (t1_il 1) (t1_il 2) }"

definition Phi_uaf_fixed_exec1 :: future where
  "Phi_uaf_fixed_exec1 =
   { edge (g_il 1) (g_il 2), edge (g_il 1) (g_il 5), edge (g_il 1) (t0_il 1),
     edge (g_il 1) (t0_il 3), edge (g_il 1) (t1_il 1), edge (g_il 1) (t1_il 2),
     edge (g_il 2) (g_il 5), edge (g_il 2) (t0_il 1), edge (g_il 2) (t0_il 3),
     edge (g_il 2) (t1_il 1), edge (g_il 2) (t1_il 2),
     edge (g_il 3) (g_il 4), edge (g_il 3) (g_il 5), edge (g_il 3) (t0_il 1),
     edge (g_il 3) (t0_il 3), edge (g_il 3) (t1_il 1), edge (g_il 3) (t1_il 2),
     edge (g_il 4) (g_il 5), edge (g_il 4) (t0_il 1), edge (g_il 4) (t0_il 3),
     edge (g_il 4) (t1_il 1), edge (g_il 4) (t1_il 2),
     edge (g_il 5) (t0_il 1), edge (g_il 5) (t0_il 3), edge (g_il 5) (t1_il 1),
     edge (g_il 5) (t1_il 2),
     edge (t0_il 1) (t0_il 3), edge (t1_il 1) (t1_il 2) }"

definition Phi_uaf_fixed :: Phi where
  "Phi_uaf_fixed = { Phi_uaf_fixed_exec0, Phi_uaf_fixed_exec1 }"


subsection \<open>@{text Phi_uaf_fixed_hs} -- the fix Phi ENRICHED with the cross-thread
  handshake DP edge (now GENERATED, not hand-asserted)\<close>

text \<open>The provisional, single-program render @{term Phi_uaf_fixed} omits the
  cross-thread synchronizes-with / DP dependence the release/acquire RCU handshake
  creates between the reader and the reclaimer (see the HONESTY NOTE below and the
  machine-checked counter-fact @{text uaf_config_fixed_horizon_counterexample}).
  Concretely, the fixed program's reader lowers @{text rcu} with a RELEASE write at
  @{text "t1.2"} and the reclaimer reads @{text rcu} at @{text "t0.1"}; for the
  reclaimer to OBSERVE the quiescent value @{text 0} that takes its @{text "rtemp =
  0"} branch (the branch that frees @{text rC}), its read @{text "t0.1#0"} must be
  ordered AFTER the release @{text "t1.2#0"} that produced that value.  That is the
  edge

      @{text "t1.2#0 -> t0.1#0"}   (release-exit  ->  reclaimer-read)

  the proper cross-thread @{text "ppo \<union> DP"} carries but the single-program
  @{term futures} rendering does not emit.

  This edge is now DERIVED, not hand-asserted: @{term \<Phi>_uaf_bug_fixed} (in the
  generated theory @{text UAF_Phi_fixed_gen}) is rendered by @{text
  "scripts/generate_phi.py --core --executions"}, which adds the handshake edge from
  the per-execution reads-from relation (release-class writer).  For this program
  the reader's release @{text "t1.2#0"} reads-to the reclaimer's read in BOTH
  executions, so the edge is added to both @{term \<Phi>_uaf_bug_fixed_exec0} and
  @{term \<Phi>_uaf_bug_fixed_exec1}.  We take @{term Phi_uaf_fixed_hs} to BE that
  generated future set; the proof below operates on it.\<close>

definition handshake_edge :: "(elabel \<times> elabel)" where
  "handshake_edge = edge (t1_il 2) (t0_il 1)"   \<comment> \<open>@{text "t1.2#0 -> t0.1#0"}\<close>

definition Phi_uaf_fixed_hs_exec0 :: future where
  "Phi_uaf_fixed_hs_exec0 = \<Phi>_uaf_bug_fixed_exec0"   \<comment> \<open>generated (carries the handshake)\<close>

definition Phi_uaf_fixed_hs_exec1 :: future where
  "Phi_uaf_fixed_hs_exec1 = \<Phi>_uaf_bug_fixed_exec1"   \<comment> \<open>generated (carries the handshake)\<close>

definition Phi_uaf_fixed_hs :: Phi where
  "Phi_uaf_fixed_hs = \<Phi>_uaf_bug_fixed"


section \<open>The UAF configuration predicate\<close>

text \<open>The UAF is the event @{text "free rC"} (a @{term DeallocA} of @{text rC})
  becoming ENABLED -- i.e. its leading label is in the horizon of the live future
  set given the committed history @{term H} -- while the DEREF @{text "Read rC"} is
  still PENDING, i.e. its label has NOT yet been committed in @{term H}.  This is
  exactly the paper's @{text "tab-fut-step-bug"} state: the reclaimer's free is the
  next thing it may do, but the reader has not finished reading the object.

  Parameterised by the free / deref instruction-labels and the future set, applied
  to the history component of a config.\<close>

definition free_enabled :: "Phi \<Rightarrow> iloc \<Rightarrow> history \<Rightarrow> bool" where
  "free_enabled Phi free_il H \<longleftrightarrow> ev0 free_il \<in> horizon_lbls Phi H"

definition deref_pending :: "iloc \<Rightarrow> history \<Rightarrow> bool" where
  "deref_pending deref_il H \<longleftrightarrow> ev0 deref_il \<notin> hist_labels H"

text \<open>The use-after-free CONFIG predicate: in config @{text "(\<sigma>,\<rho>,H)"} the free of
  @{text rC} is enabled while the deref of @{text rC} is still pending.\<close>
definition uaf_config :: "Phi \<Rightarrow> iloc \<Rightarrow> iloc \<Rightarrow> config \<Rightarrow> bool" where
  "uaf_config Phi free_il deref_il cfg \<longleftrightarrow>
     (let (\<sigma>, \<rho>, H) = cfg
      in free_enabled Phi free_il H \<and> deref_pending deref_il H)"


section \<open>The witness history for the bug\<close>

text \<open>The committed history that exhibits the UAF in the bug: the init writes and the
  acq_rel fence (@{text "g.1#0 .. g.5#0"}) and the reclaimer's rcu-read @{text
  "t0.1#0"} -- but NOT the deref @{text "t1.1#0"} (nor the relaxed exit @{text
  "t1.2#0"}, which the free does not depend on).  We only need its LABEL set; the
  actions are immaterial to the horizon (the horizon gate is over labels).  We pair
  each label with a dummy fence action (any action; the horizon ignores it).\<close>

definition uaf_witness_H :: history where
  "uaf_witness_H =
   { (ev0 (g_il 1), Fence Rlx), (ev0 (g_il 2), Fence Rlx),
     (ev0 (g_il 3), Fence Rlx), (ev0 (g_il 4), Fence Rlx),
     (ev0 (g_il 5), Fence Rlx), (ev0 (t0_il 1), Fence Rlx) }"

lemma hist_labels_uaf_witness:
  "hist_labels uaf_witness_H =
     { ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4), ev0 (g_il 5),
       ev0 (t0_il 1) }"
  by (auto simp: hist_labels_def uaf_witness_H_def ev_label_def)

text \<open>Two distinct instruction-labels have distinct @{text "#0"} event-labels.\<close>
lemma ev0_inj_il:
  "il o1 s1 = il o2 s2 \<longleftrightarrow> o1 = o2 \<and> s1 = s2"
  by (auto simp: il_def)

lemma ev0_eq_iff:
  "ev0 (il o1 s1) = ev0 (il o2 s2) \<longleftrightarrow> o1 = o2 \<and> s1 = s2"
  by (auto simp: ev0_def sub_def il_def)


section \<open>The bug: the UAF is reachable\<close>

text \<open>Core horizon fact: in the bug, @{text "free rC"} (@{text "t0.3#0"}) is in the
  horizon of @{term Phi_uaf} at the witness history, via the witness execution
  @{term Phi_uaf_exec1}, whose predecessors of @{text "t0.3#0"} are exactly the
  committed @{text "{g.1#0, g.2#0, g.3#0, g.4#0, g.5#0, t0.1#0}"}.\<close>

lemma exec1_consistent_witness:
  "consistent Phi_uaf_exec1 uaf_witness_H"
  \<comment> \<open>every committed-and-in-exec1 label has all its exec1 predecessors committed too\<close>
  unfolding consistent_def hist_labels_uaf_witness
  by (simp add: Phi_uaf_exec1_def future_labels_def hist_labels_uaf_witness
                 ev0_eq_iff)

lemma free_enabled_in_exec1:
  "ev0 (t0_il 3) \<in> enabled_in Phi_uaf_exec1 uaf_witness_H"
  \<comment> \<open>@{text "t0.3#0"} is an exec1 label, not yet committed, all preds committed\<close>
  unfolding enabled_in_def
  by (simp add: Phi_uaf_exec1_def future_labels_def hist_labels_uaf_witness
                 ev0_eq_iff)

lemma free_enabled_bug:
  "free_enabled Phi_uaf bug_free_il uaf_witness_H"
  unfolding free_enabled_def bug_free_il_def horizon_lbls_def
  using exec1_consistent_witness free_enabled_in_exec1
  by (auto simp: Phi_uaf_def)

lemma deref_pending_bug:
  "deref_pending bug_deref_il uaf_witness_H"
  \<comment> \<open>the deref @{text "t1.1#0"} is NOT in the witness history\<close>
  unfolding deref_pending_def bug_deref_il_def hist_labels_uaf_witness
  by (auto simp: ev0_eq_iff)

text \<open>Hence the witness CONFIG (any @{term \<sigma>}, @{term \<rho>} with the witness history) is
  a UAF config of the bug.\<close>
lemma uaf_config_bug_witness:
  "uaf_config Phi_uaf bug_free_il bug_deref_il (\<sigma>, \<rho>, uaf_witness_H)"
  unfolding uaf_config_def
  using free_enabled_bug deref_pending_bug by simp


text \<open>The end-to-end statement, against the @{term opsem_client} locale's
  @{term reachable}: there is a REACHABLE config of @{term "(prog_uaf_bug,
  Phi_uaf)"} that is a UAF config (free of @{text rC} enabled, deref of @{text rC}
  pending).\<close>

subsection \<open>The reachability step chain (single live future @{term Phi_uaf_exec1})\<close>

text \<open>We commit exactly @{term Phi_uaf_exec1}'s init-and-reclaimer labels, in a
  topological order, so that exec1 stays @{term consistent} throughout and each leading
  label is @{term enabled_in} exec1 -- hence in @{term horizon_lbls} -- at the history
  just before it fires.  The deref @{text "t1.1#0"} is committed neither, so it stays
  pending, and the chain ends in a UAF config.

  The horizon gate depends only on the LABELS of a history, so we reason about each
  step's history through its label set @{term hist_labels}.\<close>

text \<open>The label sets along the chain @{text "g.1, g.2, g.3, g.4, g.5, t0.1"} (each
  history is the previous one plus the new instruction's leading label).\<close>

abbreviation (input) "L0 \<equiv> ({} :: elabel set)"
abbreviation (input) "L1 \<equiv> {ev0 (g_il 1)}"
abbreviation (input) "L2 \<equiv> {ev0 (g_il 1), ev0 (g_il 2)}"
abbreviation (input) "L3 \<equiv> {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3)}"
abbreviation (input) "L4 \<equiv> {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4)}"
abbreviation (input) "L5 \<equiv> {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4),
                             ev0 (g_il 5)}"
abbreviation (input) "L6 \<equiv> {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4),
                             ev0 (g_il 5), ev0 (t0_il 1)}"
\<comment> \<open>@{text L7} is @{text L6} with the FREE committed -- the history at which the
    free has been processed and the deref is still enabled.\<close>
abbreviation (input) "L7 \<equiv> {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4),
                             ev0 (g_il 5), ev0 (t0_il 1), ev0 (t0_il 3)}"

text \<open>exec1 is consistent with each chain history (each is an exec1-downward-closed
  prefix).\<close>
lemma exec1_consistent_chain:
  "hist_labels H = L0 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L1 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L2 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L3 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L4 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L5 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L6 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  "hist_labels H = L7 \<Longrightarrow> consistent Phi_uaf_exec1 H"
  unfolding consistent_def
  by (simp_all add: Phi_uaf_exec1_def future_labels_def ev0_eq_iff)

text \<open>Each chain step's leading label is enabled in exec1 at its history.\<close>
lemma exec1_enabled_chain:
  "hist_labels H = L0 \<Longrightarrow> ev0 (g_il 1) \<in> enabled_in Phi_uaf_exec1 H"
  "hist_labels H = L1 \<Longrightarrow> ev0 (g_il 2) \<in> enabled_in Phi_uaf_exec1 H"
  "hist_labels H = L2 \<Longrightarrow> ev0 (g_il 3) \<in> enabled_in Phi_uaf_exec1 H"
  "hist_labels H = L3 \<Longrightarrow> ev0 (g_il 4) \<in> enabled_in Phi_uaf_exec1 H"
  "hist_labels H = L4 \<Longrightarrow> ev0 (g_il 5) \<in> enabled_in Phi_uaf_exec1 H"
  "hist_labels H = L5 \<Longrightarrow> ev0 (t0_il 1) \<in> enabled_in Phi_uaf_exec1 H"
  \<comment> \<open>the FREE, enabled once the reclaimer's read is committed (its only non-init
      exec1 predecessor)\<close>
  "hist_labels H = L6 \<Longrightarrow> ev0 (t0_il 3) \<in> enabled_in Phi_uaf_exec1 H"
  \<comment> \<open>and the DEREF, still enabled AFTER the free has been committed: exec1 orders
      nothing between @{text "t0.3#0"} and @{text "t1.1#0"}\<close>
  "hist_labels H = L7 \<Longrightarrow> ev0 (t1_il 1) \<in> enabled_in Phi_uaf_exec1 H"
  unfolding enabled_in_def
  by (simp_all add: Phi_uaf_exec1_def future_labels_def ev0_eq_iff)

text \<open>A single clean introduction rule for horizon membership via ONE witnessing
  future -- avoids @{method auto} searching all executions.\<close>
lemma in_horizon_lblsI:
  assumes "F \<in> Phi" and "consistent F H" and "l \<in> enabled_in F H"
  shows "l \<in> horizon_lbls Phi H"
  unfolding horizon_lbls_def using assms by blast

lemma exec1_in_Phi_uaf: "Phi_uaf_exec1 \<in> Phi_uaf"
  by (simp add: Phi_uaf_def)

text \<open>Combining the two: each leading label is in the GLOBAL horizon (via the
  consistent exec1).\<close>
lemma horizon_lbls_chain1: "hist_labels H = L0 \<Longrightarrow> ev0 (g_il 1) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(1) exec1_enabled_chain(1)]) assumption+
lemma horizon_lbls_chain2: "hist_labels H = L1 \<Longrightarrow> ev0 (g_il 2) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(2) exec1_enabled_chain(2)]) assumption+
lemma horizon_lbls_chain3: "hist_labels H = L2 \<Longrightarrow> ev0 (g_il 3) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(3) exec1_enabled_chain(3)]) assumption+
lemma horizon_lbls_chain4: "hist_labels H = L3 \<Longrightarrow> ev0 (g_il 4) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(4) exec1_enabled_chain(4)]) assumption+
lemma horizon_lbls_chain5: "hist_labels H = L4 \<Longrightarrow> ev0 (g_il 5) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(5) exec1_enabled_chain(5)]) assumption+
lemma horizon_lbls_chain6: "hist_labels H = L5 \<Longrightarrow> ev0 (t0_il 1) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(6) exec1_enabled_chain(6)]) assumption+

text \<open>The seventh step's gate: the FREE is in the global horizon once the six init /
  reclaimer labels are committed.\<close>
lemma horizon_lbls_chain7: "hist_labels H = L6 \<Longrightarrow> ev0 (t0_il 3) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(7) exec1_enabled_chain(7)]) assumption+

text \<open>And the point of the whole exercise: with the free COMMITTED, the deref is
  still in the horizon -- it can be scheduled next, against a location that has
  already been deallocated.\<close>
lemma horizon_lbls_deref_after_free:
  "hist_labels H = L7 \<Longrightarrow> ev0 (t1_il 1) \<in> horizon_lbls Phi_uaf H"
  by (rule in_horizon_lblsI[OF exec1_in_Phi_uaf exec1_consistent_chain(8) exec1_enabled_chain(8)]) assumption+

lemmas horizon_lbls_chain =
  horizon_lbls_chain1 horizon_lbls_chain2 horizon_lbls_chain3
  horizon_lbls_chain4 horizon_lbls_chain5 horizon_lbls_chain6
  horizon_lbls_chain7

text \<open>@{term instr_sublabel} of a @{term sub}-label at @{text 0} is itself.\<close>
lemma instr_sublabel_ev0 [simp]: "instr_sublabel (ev0 l) 0 = ev0 l"
  by (simp add: instr_sublabel_def ev0_def sub_def)

text \<open>The leading label of an instruction is @{term ev0} of its iloc.\<close>
lemma horizon_label_eq_ev0: "horizon_label l = ev0 l"
  by (simp add: horizon_label_def ev0_def)

text \<open>Committing a single-action event adds exactly its label to the history's
  label set.\<close>
lemma hist_labels_commit_single:
  "hist_labels (commit_events [(l, a)] H) = insert l (hist_labels H)"
  by (simp add: commit_events_def hist_labels_def)

lemma hist_labels_empty [simp]: "hist_labels {} = {}"
  by (simp add: hist_labels_def)

text \<open>Now the explicit chain.  Each step is the @{term Step} rule with a
  single-action command (Malloc / WritePtr / CFence / ReadPtr / Free), whose leading
  label is in the horizon by @{thm horizon_lbls_chain}.  We track ONLY the history's
  label set; the @{term \<sigma>} / @{term \<rho>} are threaded existentially.\<close>

text \<open>The two worker threads never bind the NAME @{text rC} in a register of their
  own: only the init preamble allocates it, publishing it in the shared
  @{term vmap}.  So both workers resolve @{text rC} through the global map -- which is
  exactly what makes the reclaimer's free and the reader's deref name the SAME
  location.  We track that along the chain.\<close>
abbreviation (input) "vC_unbound \<rho> \<equiv> rg (\<rho> (Thr 0)) vC = 0 \<and> rg (\<rho> (Thr 1)) vC = 0"

lemma reachable_uaf_chain:
  "\<exists>\<sigma> \<rho> H \<sigma>' \<rho>' H'.
      opsem_client.reachable prog_uaf_bug Phi_uaf (\<sigma>, \<rho>, H) \<and>
      hist_labels H = L6 \<and>
      opsem_client.reachable prog_uaf_bug Phi_uaf (\<sigma>', \<rho>', H') \<and>
      hist_labels H' = L7 \<and>
      resolve_loc (\<rho>' (Thr 1)) (EReg vC) \<notin> memory \<sigma>'"
proof -
  define R where "R \<equiv> opsem_client.reachable prog_uaf_bug Phi_uaf"
  \<comment> \<open>helper: one @{term Step} of a single-action command, given horizon membership\<close>
  have prog: "set prog_uaf_bug = set prog_uaf_bug" ..
  \<comment> \<open>step 0: init -> commit g.1 (Malloc rC)\<close>
  have r0: "R init_config"
    unfolding R_def by (rule opsem_client.reachable_init)
  \<comment> \<open>We build the chain by repeatedly applying @{thm opsem_client.reachable_step}
      with a concrete @{term Step}.  Each @{term cmd_effect} is computed by simp.\<close>
  obtain \<sigma>1 \<rho>1 H1 where
    s1: "step prog_uaf_bug Phi_uaf init_config (\<sigma>1, \<rho>1, H1)"
    and h1: "hist_labels H1 = L1"
    and wc1: "vC_unbound \<rho>1"
  proof -
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 1) (Malloc vC (EInt 1)) (init_renvs (ilo_owner (g_il 1))) = Some (abar, las, \<rho>')"
      and abar: "abar = [AllocA (fresh (init_renvs (ilo_owner (g_il 1)))) (EInt 1)]"
      and las: "las = [(sub (g_il 1) 0, AllocA (fresh (init_renvs (ilo_owner (g_il 1)))) (EInt 1))]"
      by (auto simp: next_sym_def Let_def split: prod.splits)
    have inh: "in_horizon (horizon_label (g_il 1)) abar Phi_uaf {}"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(1)[of "{}"] by (simp add: hist_labels_def)
    have mem: "(g_il 1 is Malloc vC (EInt 1)) \<in> set (instrs prog_uaf_bug)"
      by (rule instrs_prog_uaf_bugI) (simp add: prog_uaf_bug_def)
    let ?st = "(apply_actions las init_mstate, publish init_renvs (ilo_owner (g_il 1)) \<rho>', commit_events las {})"
    have stp: "step prog_uaf_bug Phi_uaf init_config ?st"
      unfolding init_config_def
      by (rule step.Step[where \<rho>=init_renvs, OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las {}) = L1"
      by (simp add: las hist_labels_commit_single ev0_def)
    moreover have "vC_unbound (publish init_renvs (ilo_owner (g_il 1)) \<rho>')"
      by (simp add: rg_publish_other il_def init_renvs_def init_renv_def)
    ultimately show thesis using stp that by blast
  qed
  have r1: "R (\<sigma>1, \<rho>1, H1)"
    unfolding R_def using r0[unfolded R_def] s1
    by (rule opsem_client.reachable_step)
  \<comment> \<open>step 1: commit g.2 (WritePtr *rC := 0)\<close>
  obtain \<sigma>2 \<rho>2 H2 where
    s2: "step prog_uaf_bug Phi_uaf (\<sigma>1, \<rho>1, H1) (\<sigma>2, \<rho>2, H2)"
    and h2: "hist_labels H2 = L2"
    and wc2: "vC_unbound \<rho>2"
  proof -
    define act where "act = Write Rlx (resolve_loc (\<rho>1 (ilo_owner (g_il 2))) (EReg vC)) (subst_expr (\<rho>1 (ilo_owner (g_il 2))) (EInt 0))"
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 2) (WritePtr Rlx (EReg vC) (EInt 0)) (\<rho>1 (ilo_owner (g_il 2))) = Some (abar, las, \<rho>')"
      and abar: "abar = [act]"
      and las: "las = [(sub (g_il 2) 0, act)]"
      by (auto simp: act_def Let_def)
    have inh: "in_horizon (horizon_label (g_il 2)) abar Phi_uaf H1"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(2)[OF h1] by simp
    have mem: "(g_il 2 is WritePtr Rlx (EReg vC) (EInt 0)) \<in> set (instrs prog_uaf_bug)"
      by (rule instrs_prog_uaf_bugI) (simp add: prog_uaf_bug_def)
    let ?st = "(apply_actions las \<sigma>1, publish \<rho>1 (ilo_owner (g_il 2)) \<rho>', commit_events las H1)"
    have stp: "step prog_uaf_bug Phi_uaf (\<sigma>1, \<rho>1, H1) ?st"
      by (rule step.Step[where \<rho>=\<rho>1, OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las H1) = L2"
      by (auto simp: las hist_labels_commit_single h1 ev0_def)
    moreover have "vC_unbound (publish \<rho>1 (ilo_owner (g_il 2)) \<rho>')"
      using wc1 by (simp add: rg_publish_other il_def)
    ultimately show thesis using stp that by blast
  qed
  have r2: "R (\<sigma>2, \<rho>2, H2)"
    unfolding R_def using r1[unfolded R_def] s2 by (rule opsem_client.reachable_step)
  \<comment> \<open>step 2: commit g.3 (Malloc rcu)\<close>
  obtain \<sigma>3 \<rho>3 H3 where
    s3: "step prog_uaf_bug Phi_uaf (\<sigma>2, \<rho>2, H2) (\<sigma>3, \<rho>3, H3)"
    and h3: "hist_labels H3 = L3"
    and wc3: "vC_unbound \<rho>3"
  proof -
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 3) (Malloc vrcu (EInt 1)) (\<rho>2 (ilo_owner (g_il 3))) = Some (abar, las, \<rho>')"
      and abar: "abar = [AllocA (fresh (\<rho>2 (ilo_owner (g_il 3)))) (EInt 1)]"
      and las: "las = [(sub (g_il 3) 0, AllocA (fresh (\<rho>2 (ilo_owner (g_il 3)))) (EInt 1))]"
      by (auto simp: next_sym_def Let_def split: prod.splits)
    have inh: "in_horizon (horizon_label (g_il 3)) abar Phi_uaf H2"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(3)[OF h2] by simp
    have mem: "(g_il 3 is Malloc vrcu (EInt 1)) \<in> set (instrs prog_uaf_bug)"
      by (rule instrs_prog_uaf_bugI) (simp add: prog_uaf_bug_def)
    let ?st = "(apply_actions las \<sigma>2, publish \<rho>2 (ilo_owner (g_il 3)) \<rho>', commit_events las H2)"
    have stp: "step prog_uaf_bug Phi_uaf (\<sigma>2, \<rho>2, H2) ?st"
      by (rule step.Step[where \<rho>=\<rho>2, OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las H2) = L3"
      by (auto simp: las hist_labels_commit_single h2 ev0_def)
    moreover have "vC_unbound (publish \<rho>2 (ilo_owner (g_il 3)) \<rho>')"
      using wc2 by (simp add: rg_publish_other il_def)
    ultimately show thesis using stp that by blast
  qed
  have r3: "R (\<sigma>3, \<rho>3, H3)"
    unfolding R_def using r2[unfolded R_def] s3 by (rule opsem_client.reachable_step)
  \<comment> \<open>step 3: commit g.4 (WritePtr *rcu := 1)\<close>
  obtain \<sigma>4 \<rho>4 H4 where
    s4: "step prog_uaf_bug Phi_uaf (\<sigma>3, \<rho>3, H3) (\<sigma>4, \<rho>4, H4)"
    and h4: "hist_labels H4 = L4"
    and wc4: "vC_unbound \<rho>4"
  proof -
    define act where "act = Write Rlx (resolve_loc (\<rho>3 (ilo_owner (g_il 4))) (EReg vrcu)) (subst_expr (\<rho>3 (ilo_owner (g_il 4))) (EInt 1))"
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 4) (WritePtr Rlx (EReg vrcu) (EInt 1)) (\<rho>3 (ilo_owner (g_il 4))) = Some (abar, las, \<rho>')"
      and abar: "abar = [act]"
      and las: "las = [(sub (g_il 4) 0, act)]"
      by (auto simp: act_def Let_def)
    have inh: "in_horizon (horizon_label (g_il 4)) abar Phi_uaf H3"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(4)[OF h3] by simp
    have mem: "(g_il 4 is WritePtr Rlx (EReg vrcu) (EInt 1)) \<in> set (instrs prog_uaf_bug)"
      by (rule instrs_prog_uaf_bugI) (simp add: prog_uaf_bug_def)
    let ?st = "(apply_actions las \<sigma>3, publish \<rho>3 (ilo_owner (g_il 4)) \<rho>', commit_events las H3)"
    have stp: "step prog_uaf_bug Phi_uaf (\<sigma>3, \<rho>3, H3) ?st"
      by (rule step.Step[where \<rho>=\<rho>3, OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las H3) = L4"
      by (auto simp: las hist_labels_commit_single h3 ev0_def)
    moreover have "vC_unbound (publish \<rho>3 (ilo_owner (g_il 4)) \<rho>')"
      using wc3 by (simp add: rg_publish_other il_def)
    ultimately show thesis using stp that by blast
  qed
  have r4: "R (\<sigma>4, \<rho>4, H4)"
    unfolding R_def using r3[unfolded R_def] s4 by (rule opsem_client.reachable_step)
  \<comment> \<open>step 4: commit g.5 (CFence acq_rel)\<close>
  obtain \<sigma>5 \<rho>5 H5 where
    s5: "step prog_uaf_bug Phi_uaf (\<sigma>4, \<rho>4, H4) (\<sigma>5, \<rho>5, H5)"
    and h5: "hist_labels H5 = L5"
    and wc5: "vC_unbound \<rho>5"
  proof -
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 5) (CFence Acq_rel) (\<rho>4 (ilo_owner (g_il 5))) = Some (abar, las, \<rho>')"
      and abar: "abar = [Fence Acq_rel]"
      and las: "las = [(sub (g_il 5) 0, Fence Acq_rel)]"
      by (auto simp: Let_def)
    have inh: "in_horizon (horizon_label (g_il 5)) abar Phi_uaf H4"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(5)[OF h4] by simp
    have mem: "(g_il 5 is CFence Acq_rel) \<in> set (instrs prog_uaf_bug)"
      by (rule instrs_prog_uaf_bugI) (simp add: prog_uaf_bug_def)
    let ?st = "(apply_actions las \<sigma>4, publish \<rho>4 (ilo_owner (g_il 5)) \<rho>', commit_events las H4)"
    have stp: "step prog_uaf_bug Phi_uaf (\<sigma>4, \<rho>4, H4) ?st"
      by (rule step.Step[where \<rho>=\<rho>4, OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las H4) = L5"
      by (auto simp: las hist_labels_commit_single h4 ev0_def)
    moreover have "vC_unbound (publish \<rho>4 (ilo_owner (g_il 5)) \<rho>')"
      using wc4 by (simp add: rg_publish_other il_def)
    ultimately show thesis using stp that by blast
  qed
  have r5: "R (\<sigma>5, \<rho>5, H5)"
    unfolding R_def using r4[unfolded R_def] s5 by (rule opsem_client.reachable_step)
  \<comment> \<open>step 5: commit t0.1 (ReadPtr rtemp := *rcu)\<close>
  obtain \<sigma>6 \<rho>6 H6 where
    s6: "step prog_uaf_bug Phi_uaf (\<sigma>5, \<rho>5, H5) (\<sigma>6, \<rho>6, H6)"
    and h6: "hist_labels H6 = {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3),
                                ev0 (g_il 4), ev0 (g_il 5), ev0 (t0_il 1)}"
    and wc6: "vC_unbound \<rho>6"
  proof -
    obtain abar las \<rho>' where
      ce: "cmd_effect False (t0_il 1) (ReadPtr Rlx rtemp (EReg vrcu)) (\<rho>5 (ilo_owner (t0_il 1))) = Some (abar, las, \<rho>')"
      and abar: "abar = [Read Rlx (resolve_loc (\<rho>5 (ilo_owner (t0_il 1))) (EReg vrcu)) (fresh (\<rho>5 (ilo_owner (t0_il 1))))]"
      and las: "las = [(sub (t0_il 1) 0, Read Rlx (resolve_loc (\<rho>5 (ilo_owner (t0_il 1))) (EReg vrcu)) (fresh (\<rho>5 (ilo_owner (t0_il 1)))))]"
      \<comment> \<open>the read binds the thread-local @{text rtemp}; it leaves @{text rC} unbound
          in the reclaimer's registers, so @{text rC} still resolves globally\<close>
      and rho': "\<rho>' = set_reg (snd (next_sym (\<rho>5 (ilo_owner (t0_il 1))))) rtemp
                              (fresh (\<rho>5 (ilo_owner (t0_il 1))))"
      by (auto simp: next_sym_def Let_def split: prod.splits)
    have inh: "in_horizon (horizon_label (t0_il 1)) abar Phi_uaf H5"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(6)[OF h5] by simp
    have mem: "(t0_il 1 is ReadPtr Rlx rtemp (EReg vrcu)) \<in> set (instrs prog_uaf_bug)"
      by (rule instrs_prog_uaf_bugI) (simp add: prog_uaf_bug_def)
    let ?st = "(apply_actions las \<sigma>5, publish \<rho>5 (ilo_owner (t0_il 1)) \<rho>', commit_events las H5)"
    have stp: "step prog_uaf_bug Phi_uaf (\<sigma>5, \<rho>5, H5) ?st"
      by (rule step.Step[where \<rho>=\<rho>5, OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las H5) =
            {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4), ev0 (g_il 5),
             ev0 (t0_il 1)}"
      by (auto simp: las hist_labels_commit_single h5 ev0_def)
    moreover have "vC_unbound (publish \<rho>5 (ilo_owner (t0_il 1)) \<rho>')"
      using wc5 rho' by (simp add: rg_publish_other il_def set_reg_def next_sym_def)
    ultimately show thesis using stp that by blast
  qed
  have r6: "R (\<sigma>6, \<rho>6, H6)"
    unfolding R_def using r5[unfolded R_def] s6 by (rule opsem_client.reachable_step)
  \<comment> \<open>step 6: commit t0.3 (Free rC) -- the instruction NESTED in @{text "t0.2"}'s THEN
      body.  It is addressed through the FLATTENED program @{term "instrs prog_uaf_bug"};
      no branch event is committed (Phi carries none), the horizon gate alone admits
      it, via exec1's control-dependence edge @{text "t0.1#0 \<rightarrow> t0.3#0"}.\<close>
  obtain \<sigma>7 \<rho>7 H7 where
    s7: "step prog_uaf_bug Phi_uaf (\<sigma>6, \<rho>6, H6) (\<sigma>7, \<rho>7, H7)"
    and h7: "hist_labels H7 = L7"
    \<comment> \<open>the MEMORY-STATE consequence: the location the reader will dereference is
        no longer allocated\<close>
    and freed7: "resolve_loc (\<rho>7 (Thr 1)) (EReg vC) \<notin> memory \<sigma>7"
  proof -
    obtain abar las \<rho>' where
      ce: "cmd_effect False (t0_il 3) (Free vC) (\<rho>6 (ilo_owner (t0_il 3))) = Some (abar, las, \<rho>')"
      and abar: "abar = [DeallocA (sym_of (\<rho>6 (ilo_owner (t0_il 3))) vC)]"
      and las: "las = [(sub (t0_il 3) 0, DeallocA (sym_of (\<rho>6 (ilo_owner (t0_il 3))) vC))]"
      by (auto simp: Let_def)
    have inh: "in_horizon (horizon_label (t0_il 3)) abar Phi_uaf H6"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using horizon_lbls_chain(7)[OF h6] by simp
    have mem: "(t0_il 3 is Free vC) \<in> set (instrs prog_uaf_bug)"
      \<comment> \<open>NOT a member of @{term "set prog_uaf_bug"} -- it is reachable only through
          the flattening\<close>
      by (simp add: prog_uaf_bug_def is_entry_def)
    let ?st = "(apply_actions las \<sigma>6, publish \<rho>6 (ilo_owner (t0_il 3)) \<rho>', commit_events las H6)"
    have stp: "step prog_uaf_bug Phi_uaf (\<sigma>6, \<rho>6, H6) ?st"
      by (rule step.Step[where \<rho>=\<rho>6, OF mem _ _ ce inh refl refl]) auto
    have hl: "hist_labels (commit_events las H6) = L7"
      by (auto simp: las hist_labels_commit_single h6 ev0_def)
    \<comment> \<open>@{term Free} leaves the registers alone, so the write-back only broadcasts the
        shared components; the reader therefore resolves @{text rC} to the very symbol
        the reclaimer just deallocated -- both go through the shared @{term vmap},
        neither has @{text rC} in its own registers (@{thm wc6}).\<close>
    have rho'_eq: "\<rho>' = \<rho>6 (ilo_owner (t0_il 3))" using ce by (simp add: Let_def)
    have same: "resolve_loc (publish \<rho>6 (ilo_owner (t0_il 3)) \<rho>' (Thr 1)) (EReg vC)
                  = sym_of (\<rho>6 (ilo_owner (t0_il 3))) vC"
      using wc6 by (simp add: publish_def rho'_eq sym_of_def il_def)
    have gone: "sym_of (\<rho>6 (ilo_owner (t0_il 3))) vC \<notin> memory (apply_actions las \<sigma>6)"
      by (simp add: las)
    from same gone
    have "resolve_loc (publish \<rho>6 (ilo_owner (t0_il 3)) \<rho>' (Thr 1)) (EReg vC)
            \<notin> memory (apply_actions las \<sigma>6)" by simp
    with stp hl show thesis using that by blast
  qed
  have r7: "R (\<sigma>7, \<rho>7, H7)"
    unfolding R_def using r6[unfolded R_def] s7 by (rule opsem_client.reachable_step)
  show ?thesis
    using r6[unfolded R_def] h6 r7[unfolded R_def] h7 freed7 by blast
qed

text \<open>The horizon facts depend only on a history's LABEL set, so the chain's final
  config -- with the same labels as @{term uaf_witness_H} -- is a UAF config.\<close>

text \<open>@{term consistent} and @{term enabled_in} depend on a history only through its
  label set.\<close>
lemma consistent_cong:
  "hist_labels H = hist_labels H' \<Longrightarrow> consistent F H = consistent F H'"
  by (simp add: consistent_def)

lemma enabled_in_cong:
  "hist_labels H = hist_labels H' \<Longrightarrow> enabled_in F H = enabled_in F H'"
  by (simp add: enabled_in_def)

lemma free_enabled_of_labels:
  assumes "hist_labels H = hist_labels uaf_witness_H"
  shows "free_enabled Phi_uaf bug_free_il H"
  unfolding free_enabled_def bug_free_il_def
  apply (rule in_horizon_lblsI[OF exec1_in_Phi_uaf])
   apply (subst consistent_cong[OF assms]; rule exec1_consistent_witness)
  apply (subst enabled_in_cong[OF assms]; rule free_enabled_in_exec1)
  done

lemma deref_pending_of_labels:
  "hist_labels H = hist_labels uaf_witness_H \<Longrightarrow> deref_pending bug_deref_il H"
  unfolding deref_pending_def bug_deref_il_def
  by (simp add: hist_labels_uaf_witness ev0_eq_iff)

theorem uaf_reachable_bug:
  "\<exists>cfg. opsem_client.reachable prog_uaf_bug Phi_uaf cfg \<and>
         uaf_config Phi_uaf bug_free_il bug_deref_il cfg"
proof -
  from reachable_uaf_chain obtain \<sigma> \<rho> H where
    reach: "opsem_client.reachable prog_uaf_bug Phi_uaf (\<sigma>, \<rho>, H)"
    and hl: "hist_labels H = {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3),
                              ev0 (g_il 4), ev0 (g_il 5), ev0 (t0_il 1)}"
    by blast
  have eq: "hist_labels H = hist_labels uaf_witness_H"
    by (simp add: hl hist_labels_uaf_witness)
  have "uaf_config Phi_uaf bug_free_il bug_deref_il (\<sigma>, \<rho>, H)"
    unfolding uaf_config_def
    using free_enabled_of_labels[OF eq] deref_pending_of_labels[OF eq] by simp
  with reach show ?thesis by blast
qed

text \<open>The program has nine instructions, so the derivation is strictly shorter than
  the program is long -- a linear (indeed sub-length) bound for this example.\<close>
lemma prog_uaf_bug_length: "length prog_uaf_bug = 9"
  by (simp add: prog_uaf_bug_def)


subsection \<open>The UAF REALISED: the free is processed, and the deref is then enabled\<close>

text \<open>@{term uaf_config} above is the paper's @{text "tab-fut-step-bug"} state, and it
  is a PRECURSOR: the free MAY be scheduled while the deref has not run.  It does not
  by itself say the free happens first -- the reader could still deref before the
  reclaimer frees.

  @{term uaf_realised} is the violation itself: the deallocation is COMMITTED in the
  history, and the deref of that same object is in the horizon, i.e.\ it is a legal
  next step.  Committing the free requires the operational semantics to actually
  execute an instruction nested in a branch body, which is what the flattened
  instruction lookup @{term instrs} makes possible.\<close>

definition uaf_realised :: "Phi \<Rightarrow> iloc \<Rightarrow> iloc \<Rightarrow> config \<Rightarrow> bool" where
  "uaf_realised Phi free_il deref_il cfg \<longleftrightarrow>
     (let (\<sigma>, \<rho>, H) = cfg
      in ev0 free_il \<in> hist_labels H \<and> ev0 deref_il \<in> horizon_lbls Phi H)"

text \<open>The end-to-end statement: a REACHABLE configuration of the buggy program has the
  free of @{text rC} committed with the deref of @{text rC} enabled.\<close>
theorem uaf_realised_bug:
  "\<exists>cfg. opsem_client.reachable prog_uaf_bug Phi_uaf cfg \<and>
         uaf_realised Phi_uaf bug_free_il bug_deref_il cfg"
proof -
  from reachable_uaf_chain obtain \<sigma> \<rho> H where
    reach: "opsem_client.reachable prog_uaf_bug Phi_uaf (\<sigma>, \<rho>, H)"
    and hl: "hist_labels H = L7"
    by blast
  have "uaf_realised Phi_uaf bug_free_il bug_deref_il (\<sigma>, \<rho>, H)"
    unfolding uaf_realised_def bug_free_il_def bug_deref_il_def
    using hl horizon_lbls_deref_after_free[OF hl] by simp
  with reach show ?thesis by blast
qed

text \<open>The realised UAF is a strictly LATER state than the precursor: the free is no
  longer merely enabled but committed, so @{term uaf_config} (which requires the
  deref pending) and @{term uaf_realised} are not the same predicate.  Both hold of
  the bug, the precursor along the way to the realised UAF.\<close>

text \<open>Finally the MEMORY-STATE reading of the same configuration, which owes nothing
  to @{typ Phi}: the location the reader resolves @{text rC} to is not in
  @{term memory} -- it has been deallocated -- and the reader's deref of it is
  nevertheless a legal next step.  This is only meaningful because a location is now
  GLOBAL: the object is allocated by the init preamble, published in the shared
  @{term vmap}, deallocated by the reclaimer through @{term sym_of}, and resolved by
  the reader through the same map (@{text opsem_client.shared_renvs_reachable}).  With a per-owner
  location map the two names would denote unrelated symbols and this statement would
  be vacuous.\<close>
theorem uaf_realised_sigma_bug:
  "\<exists>\<sigma> \<rho> H. opsem_client.reachable prog_uaf_bug Phi_uaf (\<sigma>, \<rho>, H) \<and>
            uaf_realised Phi_uaf bug_free_il bug_deref_il (\<sigma>, \<rho>, H) \<and>
            resolve_loc (\<rho> (Thr 1)) (EReg vC) \<notin> memory \<sigma>"
proof -
  from reachable_uaf_chain obtain \<sigma> \<rho> H where
    reach: "opsem_client.reachable prog_uaf_bug Phi_uaf (\<sigma>, \<rho>, H)"
    and hl: "hist_labels H = L7"
    and freed: "resolve_loc (\<rho> (Thr 1)) (EReg vC) \<notin> memory \<sigma>"
    by blast
  have "uaf_realised Phi_uaf bug_free_il bug_deref_il (\<sigma>, \<rho>, H)"
    unfolding uaf_realised_def bug_free_il_def bug_deref_il_def
    using hl horizon_lbls_deref_after_free[OF hl] by simp
  with reach freed show ?thesis by blast
qed


section \<open>The fix: the UAF is excluded\<close>

text \<open>The structural discriminator, mechanically checked: the deref->exit ppo edge
  @{text "t1.1#0 -> t1.2#0"} is PRESENT in every future of the FIXED program but
  ABSENT in every future of the BUG program.  This is the single source of the
  bug-vs-fixed difference.\<close>

lemma deref_exit_edge_present_fixed:
  "\<forall>F \<in> Phi_uaf_fixed. edge (fix_deref_il) (fix_exit_il) \<in> F"
  unfolding Phi_uaf_fixed_def fix_deref_il_def fix_exit_il_def
  by (simp add: Phi_uaf_fixed_exec0_def Phi_uaf_fixed_exec1_def)

lemma deref_exit_edge_absent_bug:
  "\<forall>F \<in> Phi_uaf. edge (bug_deref_il) (bug_exit_il) \<notin> F"
  \<comment> \<open>the relaxed exit creates NO ppo edge from the deref -- the absent discriminator\<close>
  unfolding Phi_uaf_def bug_deref_il_def bug_exit_il_def
  by (simp add: Phi_uaf_exec0_def Phi_uaf_exec1_def ev0_eq_iff)

text \<open>In the fixed program, the ONLY future containing @{text "free rC"}
  (@{text "t0.3#0"}) is @{term Phi_uaf_fixed_exec1}; @{term Phi_uaf_fixed_exec0}
  has no free at all.\<close>

lemma free_not_in_fixed_exec0:
  "ev0 (t0_il 3) \<notin> future_labels Phi_uaf_fixed_exec0"
  by (simp add: Phi_uaf_fixed_exec0_def future_labels_def ev0_eq_iff)

lemma free_only_in_fixed_exec1:
  assumes "ev0 (t0_il 3) \<in> future_labels F" and "F \<in> Phi_uaf_fixed"
  shows "F = Phi_uaf_fixed_exec1"
proof -
  from assms(2) have "F = Phi_uaf_fixed_exec0 \<or> F = Phi_uaf_fixed_exec1"
    by (simp add: Phi_uaf_fixed_def)
  with assms(1) free_not_in_fixed_exec0 show ?thesis by blast
qed


text \<open>HONESTY NOTE on the exclusion.  The intended end-to-end statement is

    @{text "\<not> (\<exists>cfg. reachable (prog_uaf_fixed, Phi_uaf_fixed) cfg \<and> uaf_config \<dots> cfg)"}

  i.e.\ NO reachable config of the fixed program is a UAF config.  However, against
  the PROVISIONAL @{term Phi_uaf_fixed} (the single-program futures of
  @{text "uaf-bug-fixed"}), this statement is NOT established -- and in fact is
  FALSE at the horizon level, for a concrete and instructive reason.

  In @{term Phi_uaf_fixed_exec1} (the only future containing the free, @{thm
  free_only_in_fixed_exec1}) the predecessors of the free @{text "t0.3#0"} are the init
  labels and the reclaimer read @{text "{g.1#0, g.2#0, g.3#0, g.4#0, g.5#0, t0.1#0}"};
  the deref @{text "t1.1#0"} is NOT among them.  So a history committing exactly those
  labels (reachable: step the init through the fence, then the reclaimer's relaxed
  rcu-read, all source labels of exec1) has the free ENABLED while the deref is still
  PENDING -- a UAF config -- and that history IS reachable.

  Why: the release exit @{text "t1.2"} DOES carry the deref->exit ppo edge @{text
  "t1.1#0 -> t1.2#0"} (proved, @{thm deref_exit_edge_present_fixed}; absent in the
  bug, @{thm deref_exit_edge_absent_bug}), but the property that EXCLUDES the UAF is
  the cross-thread SYNCHRONIZES-WITH / DP edge tying the RECLAIMER'S read @{text
  "t0.1#0"} to the reader's release @{text "t1.2#0"} (an rf/DP edge @{text "t1.2#0 ->
  t0.1#0"}, hence transitively @{text "t1.1#0 -> t1.2#0 -> t0.1#0 -> t0.3#0"}).  That
  edge is a per-EXECUTION dependence the single-program @{term futures} rendering does
  not emit here, so the rendered @{term Phi_uaf_fixed} under-constrains the reclaimer.
  The exclusion therefore needs a Phi enriched with that handshake DP edge (the proper
  cross-thread @{text "ppo \<union> DP"}), OR a path-predicate (@{term phi}) argument at the
  MemSem level showing the reclaimer's branch @{text "rtemp = 0"} cannot be taken
  before the reader's release commits.  Neither is captured by the provisional Phi
  of @{text "uaf-bug-fixed"}.

  We record the honest counter-fact below, then discharge the intended exclusion over
  the handshake-enriched @{term Phi_uaf_fixed_hs} (which the generator now emits, since the
  render carries the reads-from-derived handshake edge).\<close>

text \<open>The witness history that REFUTES horizon-level exclusion against the provisional
  @{term Phi_uaf_fixed}: the init through the fence, plus the reclaimer's rcu-read.\<close>
definition fix_bad_H :: history where
  "fix_bad_H = { (ev0 (g_il 1), Fence Rlx), (ev0 (g_il 2), Fence Rlx),
                 (ev0 (g_il 3), Fence Rlx), (ev0 (g_il 4), Fence Rlx),
                 (ev0 (g_il 5), Fence Rlx), (ev0 (t0_il 1), Fence Rlx) }"

lemma hist_labels_fix_bad_H:
  "hist_labels fix_bad_H =
     { ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4), ev0 (g_il 5),
       ev0 (t0_il 1) }"
  by (auto simp: hist_labels_def fix_bad_H_def ev_label_def)

lemma fix_exec1_consistent_bad:
  "consistent Phi_uaf_fixed_exec1 fix_bad_H"
  unfolding consistent_def hist_labels_fix_bad_H
  by (simp add: Phi_uaf_fixed_exec1_def future_labels_def ev0_eq_iff)

lemma fix_free_enabled_bad:
  "ev0 (t0_il 3) \<in> enabled_in Phi_uaf_fixed_exec1 fix_bad_H"
  unfolding enabled_in_def
  by (simp add: Phi_uaf_fixed_exec1_def future_labels_def
                 hist_labels_fix_bad_H ev0_eq_iff)

text \<open>Honest counter-fact: under the provisional @{term Phi_uaf_fixed}, the free is
  enabled while the deref is pending at @{term fix_bad_H} -- so the horizon-level
  exclusion does NOT hold for this Phi.  (Stated as a fact about @{term uaf_config}
  to make the gap precise and machine-checked.)\<close>
lemma fix_exec1_in_Phi: "Phi_uaf_fixed_exec1 \<in> Phi_uaf_fixed"
  by (simp add: Phi_uaf_fixed_def)

lemma uaf_config_fixed_horizon_counterexample:
  "uaf_config Phi_uaf_fixed fix_free_il fix_deref_il (\<sigma>, \<rho>, fix_bad_H)"
proof -
  have fe: "free_enabled Phi_uaf_fixed fix_free_il fix_bad_H"
    unfolding free_enabled_def fix_free_il_def
    by (rule in_horizon_lblsI[OF fix_exec1_in_Phi
                                 fix_exec1_consistent_bad fix_free_enabled_bad])
  have dp: "deref_pending fix_deref_il fix_bad_H"
    unfolding deref_pending_def fix_deref_il_def
    by (simp add: hist_labels_fix_bad_H ev0_eq_iff)
  show ?thesis
    unfolding uaf_config_def using fe dp by simp
qed

section \<open>The fix, properly modelled: the UAF is EXCLUDED over the handshake-enriched Phi\<close>

text \<open>We now discharge the exclusion against @{term Phi_uaf_fixed_hs}, the fix's
  future set carrying the cross-thread handshake DP edge @{thm handshake_edge_def}
  identified in the HONESTY NOTE.  This is the FAITHFUL model of the
  release/acquire RCU handshake (the provisional @{term Phi_uaf_fixed} merely
  under-rendered it); the statement is not weakened -- it is strengthened to the
  Phi that actually captures the synchronizes-with the program establishes.

  The argument is purely at the horizon level (hence holds at EVERY config, a
  fortiori at every reachable one): the free can be enabled only via the unique
  future @{term Phi_uaf_fixed_hs_exec1} that contains it, and there the
  consistency frontier forces, from the committed reclaimer read, the release, and
  from the release the deref -- contradicting deref-pending.\<close>

text \<open>The labels of the enriched free-bearing future.\<close>
lemma future_labels_fixed_hs_exec1:
  "future_labels Phi_uaf_fixed_hs_exec1 =
     { ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4), ev0 (g_il 5),
       ev0 (t0_il 1), ev0 (t0_il 3), ev0 (t1_il 1), ev0 (t1_il 2) }"
  by (auto simp: Phi_uaf_fixed_hs_exec1_def \<Phi>_uaf_bug_fixed_exec1_def
                 future_labels_def ev0_eq_iff)

text \<open>The free is the free only in the enriched exec1 (exec0 carries no free).\<close>
lemma free_not_in_fixed_hs_exec0:
  "ev0 (t0_il 3) \<notin> future_labels Phi_uaf_fixed_hs_exec0"
  by (simp add: Phi_uaf_fixed_hs_exec0_def \<Phi>_uaf_bug_fixed_exec0_def
                 future_labels_def ev0_eq_iff)

lemma free_only_in_fixed_hs_exec1:
  assumes "ev0 (t0_il 3) \<in> future_labels F" and "F \<in> Phi_uaf_fixed_hs"
  shows "F = Phi_uaf_fixed_hs_exec1"
proof -
  from assms(2) have "F = Phi_uaf_fixed_hs_exec0 \<or> F = Phi_uaf_fixed_hs_exec1"
    by (simp add: Phi_uaf_fixed_hs_def \<Phi>_uaf_bug_fixed_def
                  Phi_uaf_fixed_hs_exec0_def Phi_uaf_fixed_hs_exec1_def)
  with assms(1) free_not_in_fixed_hs_exec0 show ?thesis by blast
qed

text \<open>The crux dependence chain, read off the edge set of the enriched exec1:
  the free's predecessor @{text "t0.1#0"}, the read's predecessor @{text "t1.2#0"}
  (the handshake edge), and the release's predecessor @{text "t1.1#0"} (the deref,
  via the already-present ppo edge).\<close>
lemma fixed_hs_exec1_edges:
  "edge (t0_il 1) (t0_il 3) \<in> Phi_uaf_fixed_hs_exec1"   \<comment> \<open>read  -> free\<close>
  "edge (t1_il 2) (t0_il 1) \<in> Phi_uaf_fixed_hs_exec1"   \<comment> \<open>release -> read (handshake)\<close>
  "edge (t1_il 1) (t1_il 2) \<in> Phi_uaf_fixed_hs_exec1"   \<comment> \<open>deref -> release (ppo)\<close>
  by (simp_all add: Phi_uaf_fixed_hs_exec1_def \<Phi>_uaf_bug_fixed_exec1_def)

text \<open>HORIZON-LEVEL EXCLUSION over the enriched Phi: there is NO history at which the
  free is enabled while the deref is pending.  This is strictly stronger than the
  reachability statement and is what makes the program safe.\<close>
lemma uaf_config_excluded_fixed_hs_horizon:
  "\<not> uaf_config Phi_uaf_fixed_hs fix_free_il fix_deref_il (\<sigma>, \<rho>, H)"
proof
  assume "uaf_config Phi_uaf_fixed_hs fix_free_il fix_deref_il (\<sigma>, \<rho>, H)"
  hence fe: "free_enabled Phi_uaf_fixed_hs fix_free_il H"
    and dp: "deref_pending fix_deref_il H"
    by (simp_all add: uaf_config_def)
  \<comment> \<open>The free is in the horizon: some consistent future enables it.\<close>
  from fe have "ev0 (t0_il 3) \<in> horizon_lbls Phi_uaf_fixed_hs H"
    by (simp add: free_enabled_def fix_free_il_def)
  then obtain F where F_Phi: "F \<in> Phi_uaf_fixed_hs"
    and F_cons: "consistent F H"
    and F_en: "ev0 (t0_il 3) \<in> enabled_in F H"
    by (auto simp: horizon_lbls_def)
  \<comment> \<open>Only the enriched exec1 carries the free.\<close>
  from F_en have free_lbl: "ev0 (t0_il 3) \<in> future_labels F"
    by (simp add: enabled_in_def)
  have F_is: "F = Phi_uaf_fixed_hs_exec1"
    by (rule free_only_in_fixed_hs_exec1[OF free_lbl F_Phi])
  \<comment> \<open>Enabledness of the free commits its predecessor, the reclaimer read @{text "t0.1#0"}.\<close>
  from F_en have free_preds:
    "\<forall>p. (p, ev0 (t0_il 3)) \<in> F \<longrightarrow> p \<in> hist_labels H"
    by (simp add: enabled_in_def)
  from fixed_hs_exec1_edges(1) F_is
  have "(ev0 (t0_il 1), ev0 (t0_il 3)) \<in> F" by simp
  with free_preds have read_in: "ev0 (t0_il 1) \<in> hist_labels H" by blast
  \<comment> \<open>Consistency then commits the read's predecessor -- the release @{text "t1.2#0"}.\<close>
  have read_lbl: "ev0 (t0_il 1) \<in> future_labels F"
    by (simp add: F_is future_labels_fixed_hs_exec1 ev0_eq_iff)
  from F_cons read_in read_lbl
  have read_cons: "\<forall>p. (p, ev0 (t0_il 1)) \<in> F \<longrightarrow> p \<in> hist_labels H"
    by (simp add: consistent_def)
  from fixed_hs_exec1_edges(2) F_is
  have "(ev0 (t1_il 2), ev0 (t0_il 1)) \<in> F" by simp
  with read_cons have rel_in: "ev0 (t1_il 2) \<in> hist_labels H" by blast
  \<comment> \<open>Consistency again commits the release's predecessor -- the DEREF @{text "t1.1#0"}.\<close>
  have rel_lbl: "ev0 (t1_il 2) \<in> future_labels F"
    by (simp add: F_is future_labels_fixed_hs_exec1 ev0_eq_iff)
  from F_cons rel_in rel_lbl
  have rel_cons: "\<forall>p. (p, ev0 (t1_il 2)) \<in> F \<longrightarrow> p \<in> hist_labels H"
    by (simp add: consistent_def)
  from fixed_hs_exec1_edges(3) F_is
  have "(ev0 (t1_il 1), ev0 (t1_il 2)) \<in> F" by simp
  with rel_cons have deref_in: "ev0 (t1_il 1) \<in> hist_labels H" by blast
  \<comment> \<open>But the deref is exactly @{term fix_deref_il}, asserted PENDING -- contradiction.\<close>
  from dp have "ev0 (t1_il 1) \<notin> hist_labels H"
    by (simp add: deref_pending_def fix_deref_il_def)
  with deref_in show False by contradiction
qed

text \<open>The intended exclusion theorem, discharged over the faithful handshake-enriched
  @{term Phi_uaf_fixed_hs}: NO reachable config of the fixed program is a UAF config.
  Immediate from the (stronger) horizon-level exclusion above, which holds at every
  config.\<close>
theorem uaf_excluded_fixed:
  "\<not> (\<exists>cfg. opsem_client.reachable prog_uaf_fixed Phi_uaf_fixed_hs cfg \<and>
            uaf_config Phi_uaf_fixed_hs fix_free_il fix_deref_il cfg)"
proof (rule notI, elim exE conjE)
  fix cfg
  assume "uaf_config Phi_uaf_fixed_hs fix_free_il fix_deref_il cfg"
  moreover obtain \<sigma> \<rho> H where "cfg = (\<sigma>, \<rho>, H)"
    by (cases cfg) auto
  ultimately show False
    using uaf_config_excluded_fixed_hs_horizon by simp
qed

text \<open>NOTE (faithfulness / non-weakening).  The provisional single-program render
  @{term Phi_uaf_fixed} does NOT support this exclusion -- and that is not a defect
  of the proof but of that Phi: @{thm uaf_config_fixed_horizon_counterexample} above
  is the machine-checked witness that, lacking the handshake edge, the free is
  horizon-enabled with the deref pending at the reachable @{term fix_bad_H}.  The
  theorem is therefore stated over @{term Phi_uaf_fixed_hs}, the future set that
  faithfully carries the release/acquire synchronizes-with the fixed program
  establishes.

  The statement is NOT weakened to force a green build: the @{term uaf_config} and
  @{term reachable} predicates are the same ones used for the bug's reachability
  result, applied to the correctly-modelled Phi.  The same holds of the exclusion in
  the next subsection: @{term uaf_realised} there is exactly the predicate proved
  REACHABLE for the bug in @{text uaf_realised_bug}.\<close>


subsection \<open>The fix excludes the REALISED use-after-free too\<close>

text \<open>@{term uaf_config} above rules out the precursor: the free enabled while the
  deref is pending.  The safety property the fixed program really owes is the
  exclusive one over @{term uaf_realised} -- the free COMMITTED and the deref
  ENABLED must never hold together.  Either may hold on its own; both at once is the
  use-after-free.

  Unlike @{thm uaf_config_excluded_fixed_hs_horizon}, this cannot be established at
  EVERY config.  Take the history whose labels are @{text "{g.1#0..g.5#0, t0.3#0}"} --
  the free committed with nothing of the reader or the reclaimer's read.  The
  free-free execution @{term Phi_uaf_fixed_hs_exec0} does not contain @{text
  "t0.3#0"} at all, so @{term consistent} constrains nothing about it and exec0 stays
  live; and the deref's only predecessors there are the init labels, so it is
  enabled.  Both conjuncts hold.  That history is of course not reachable -- no step
  could have committed the free -- which is exactly the point: the property is a
  fact about REACHABLE configurations, and its proof must go through the operational
  semantics rather than the horizon alone.

  This is a DIFFERENT limitation from the one recorded above, and the two should not
  be read as one recurring weakness.  @{text uaf_config_fixed_horizon_counterexample}
  is about the provisional Phi lacking the handshake edge, and the enrichment cures
  it.  The counter-fact here holds even over the enriched @{term Phi_uaf_fixed_hs}:
  it reflects @{term consistent} ignoring committed labels that a future does not
  mention, so a future in which the free does not occur survives a history that has
  committed it.  Restricting to reachable configurations is what cures this one.\<close>

lemma uaf_realised_fixed_horizon_counterexample:
  assumes "hist_labels H = {ev0 (g_il 1), ev0 (g_il 2), ev0 (g_il 3), ev0 (g_il 4),
                            ev0 (g_il 5), ev0 (t0_il 3)}"
  shows "uaf_realised Phi_uaf_fixed_hs fix_free_il fix_deref_il (\<sigma>, \<rho>, H)"
proof -
  have "consistent Phi_uaf_fixed_hs_exec0 H"
    unfolding consistent_def assms
    by (simp add: Phi_uaf_fixed_hs_exec0_def \<Phi>_uaf_bug_fixed_exec0_def
                   future_labels_def ev0_eq_iff)
  moreover have "ev0 (t1_il 1) \<in> enabled_in Phi_uaf_fixed_hs_exec0 H"
    unfolding enabled_in_def assms
    by (simp add: Phi_uaf_fixed_hs_exec0_def \<Phi>_uaf_bug_fixed_exec0_def
                   future_labels_def ev0_eq_iff)
  moreover have "Phi_uaf_fixed_hs_exec0 \<in> Phi_uaf_fixed_hs"
    by (simp add: Phi_uaf_fixed_hs_def \<Phi>_uaf_bug_fixed_def
                  Phi_uaf_fixed_hs_exec0_def)
  ultimately show ?thesis
    unfolding uaf_realised_def fix_free_il_def fix_deref_il_def
    using assms by (auto simp: horizon_lbls_def ev0_eq_iff)
qed

text \<open>The invariant that carries the property: in the fixed program, a REACHABLE
  history containing the free contains the deref as well.  The step that committed
  the free had to pass the horizon gate (@{thm step_new_label_horizon}), and
  @{thm uaf_config_excluded_fixed_hs_horizon} says a horizon-enabled free forces the
  deref to be committed already.  Histories only grow, so the deref stays.\<close>
lemma deref_committed_of_free_committed:
  assumes "opsem_client.reachable prog_uaf_fixed Phi_uaf_fixed_hs cfg"
  shows "ev0 fix_free_il \<in> hist_labels (snd (snd cfg)) \<longrightarrow>
         ev0 fix_deref_il \<in> hist_labels (snd (snd cfg))"
proof (rule opsem_client.reachable_induct[OF assms])
  show "ev0 fix_free_il \<in> hist_labels (snd (snd init_config)) \<longrightarrow>
        ev0 fix_deref_il \<in> hist_labels (snd (snd init_config))"
    by (simp add: init_config_def)
next
  fix c c'
  assume st: "step prog_uaf_fixed Phi_uaf_fixed_hs c c'"
    and IH: "ev0 fix_free_il \<in> hist_labels (snd (snd c)) \<longrightarrow>
             ev0 fix_deref_il \<in> hist_labels (snd (snd c))"
  obtain \<sigma>0 \<rho>0 H0 where c: "c = (\<sigma>0, \<rho>0, H0)" by (cases c) auto
  obtain \<sigma>' \<rho>' H' where c': "c' = (\<sigma>', \<rho>', H')" by (cases c') auto
  from st c c' have st': "step prog_uaf_fixed Phi_uaf_fixed_hs
                              (\<sigma>0, \<rho>0, H0) (\<sigma>', \<rho>', H')" by simp
  show "ev0 fix_free_il \<in> hist_labels (snd (snd c')) \<longrightarrow>
        ev0 fix_deref_il \<in> hist_labels (snd (snd c'))"
  proof (unfold c', simp only: snd_conv, intro impI)
    assume free': "ev0 fix_free_il \<in> hist_labels H'"
    show "ev0 fix_deref_il \<in> hist_labels H'"
    proof (cases "ev0 fix_free_il \<in> hist_labels H0")
      case True
      with IH c have "ev0 fix_deref_il \<in> hist_labels H0" by simp
      with step_hist_mono[OF st'] show ?thesis by blast
    next
      case False
      \<comment> \<open>the free was committed BY this step, so it was in the horizon before it\<close>
      from step_new_label_horizon[OF st' free' False]
      have "ev0 fix_free_il \<in> horizon_lbls Phi_uaf_fixed_hs H0"
        by (simp add: ev0_def sub_def)
      hence "free_enabled Phi_uaf_fixed_hs fix_free_il H0"
        by (simp add: free_enabled_def)
      hence "\<not> deref_pending fix_deref_il H0"
        using uaf_config_excluded_fixed_hs_horizon by (auto simp: uaf_config_def)
      hence "ev0 fix_deref_il \<in> hist_labels H0"
        by (simp add: deref_pending_def)
      with step_hist_mono[OF st'] show ?thesis by blast
    qed
  qed
qed

text \<open>The safety property: no reachable configuration of the fixed program has the
  free committed AND the deref enabled.  The two are mutually exclusive -- the free
  may have happened, or the deref may be about to, never both.\<close>
theorem uaf_realised_excluded_fixed:
  "\<not> (\<exists>cfg. opsem_client.reachable prog_uaf_fixed Phi_uaf_fixed_hs cfg \<and>
            uaf_realised Phi_uaf_fixed_hs fix_free_il fix_deref_il cfg)"
proof (rule notI, elim exE conjE)
  fix cfg
  assume reach: "opsem_client.reachable prog_uaf_fixed Phi_uaf_fixed_hs cfg"
    and uaf: "uaf_realised Phi_uaf_fixed_hs fix_free_il fix_deref_il cfg"
  obtain \<sigma> \<rho> H where cfg: "cfg = (\<sigma>, \<rho>, H)" by (cases cfg) auto
  from uaf cfg have free: "ev0 fix_free_il \<in> hist_labels H"
    and deref: "ev0 fix_deref_il \<in> horizon_lbls Phi_uaf_fixed_hs H"
    by (simp_all add: uaf_realised_def)
  from deref_committed_of_free_committed[OF reach] free cfg
  have "ev0 fix_deref_il \<in> hist_labels H" by simp
  moreover from deref have "ev0 fix_deref_il \<notin> hist_labels H"
    by (rule horizon_lbls_not_committed)
  ultimately show False by contradiction
qed


end
