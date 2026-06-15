(*  Title:      clients/RCU/RCU_Client.thy
    Author:     RCU-C11-OpSem project (Episodic stack, client: RCU -- W10 refactor)

    The RCU client in the SPINE style (data-as-program over the REAL Core types),
    the W10 refactor of the retired per-PC `case` development (RCU_prog.thy /
    RCU_state.thy and the 114-future enumeration -- all RETIRED in W4).

    What this refactor LANDS (the W10 goals that are in scope for the loop-free
    OpSem step relation):

      * S7 is DROPPED.  The legacy `pc` enum hard-coded `finished | I1..I14 |
        R1..R5 | S1..S7`; the spine has NO pc enum -- the program is DATA, a
        labelled `command` list -- so S7 (and every other per-PC label) simply does
        not exist as a constructor.  Control flow is the rolled `IfElse` / `While`
        of Core.command.

      * An abstract `command` datatype with operands + memory orders, and ONE
        generic effect rule per command: this is exactly `Core.command` +
        `OpSem.cmd_effect` + the single `step.Step` rule.  There is no per-PC
        `case`; every straight-line instruction fires through the same rule.  We
        re-export the generic effect of each command shape RCU uses, against the
        concrete RCU program, as the `rcu_effect_*` lemmas below.

      * `prog_RCU` is the RCU program expressed as DATA -- a labelled list of
        `command` instances over the REAL Core types (operand-generic: the object
        pointer, the rcu flags and the registers are ordinary `var` / `reg`
        operands, NOT baked-in `C` / `var_s` / `var_n` constructors as in the old
        RCU_atomics / RCU_prog).  Mirrors `clients/UAF_Bug/UAF_Bug.thy`.

    Structural source of truth: the mordor-rendered digests
    `RCU_prog_digest.thy` (rcu3) and `RCU_inc_loop_digest.thy` (rcuincloop) -- the
    surviving generated artefacts.  Those carry PROVISIONAL placeholder types and
    string labels; here everything is in the REAL Core / OpSem types,
    session-qualified, with `iloc` labels.

    HONESTY / SCOPE.  The full RCU program contains LOOPS (the inc() retry loop and
    the sync() poll loops -- `While` / `Do` in the digests).  The OpSem step
    relation imported here is the NON-LOOP fragment (milestone 3a): `cmd_effect`
    returns `None` for `While`, and there is no `lb`-reset / episodicity rule (that
    is milestone 3b / W8b, RCU-only, still open).  So:

      * `prog_RCU` faithfully includes the rolled `While` body, but the loop CANNOT
        be stepped by this OpSem -- only the straight-line init preamble and the
        straight-line body commands are steppable here.
      * NO end-to-end RCU safety theorem (no-use-after-free) is claimed in this
        file.  That needs the loop rule (W8b) and the RCU `Phi`; both are out of
        scope for this loop-free layer.  What is established here is the data model,
        its structural well-formedness, the generic per-command effect, and a
        concrete steppable reachability chain over the loop-free preamble -- the
        scaffolding the eventual safety proof will sit on.
*)

theory RCU_Client
  imports "OpSem.OpSem"
begin

section \<open>Owners, labels, variables, registers\<close>

text \<open>One reclaiming worker thread @{term "Thr 0"} (the RCU reader/updater running
  inc()), plus the init preamble @{term Init} (mordor @{text g}).  A single worker
  is enough to exhibit the inc() critical-section shape over the real types; the
  digests carry three symmetric workers (t0/t1/t2), added by replicating the body
  with a different @{typ owner}.\<close>

definition il :: "owner \<Rightarrow> nat \<Rightarrow> iloc" where
  "il own s = \<lparr> ilo_owner = own, ilo_seq = s, ilo_loops = [] \<rparr>"

text \<open>An instruction-label INSIDE loop @{term lp} (the rolled @{term While} body):
  same owner / seq, but recording the enclosing loop.\<close>
definition il_in :: "owner \<Rightarrow> nat \<Rightarrow> loopid \<Rightarrow> iloc" where
  "il_in own s lp = \<lparr> ilo_owner = own, ilo_seq = s, ilo_loops = [lp] \<rparr>"

abbreviation "g_il s   \<equiv> il Init s"
abbreviation "t0_il s  \<equiv> il (Thr 0) s"

text \<open>The leading event-label @{text "l#0"} of an instruction-label.\<close>
definition ev0 :: "iloc \<Rightarrow> elabel" where
  "ev0 l = sub l 0"

text \<open>The program variables and registers (Core: @{typ var} = @{typ reg} =
  @{typ string}).  Operand-generic: these are ordinary names, NOT baked-in
  constructors.\<close>
abbreviation "vC    \<equiv> ''rC''"      \<comment> \<open>the reclaimable shared object pointer\<close>
abbreviation "vrcu  \<equiv> ''rrcu''"    \<comment> \<open>the rcu handshake flag array base\<close>
abbreviation "rs    \<equiv> ''rs''"      \<comment> \<open>snapshot register (the Faa result)\<close>
abbreviation "rv    \<equiv> ''rv''"      \<comment> \<open>the value read through the snapshot\<close>
abbreviation "rn    \<equiv> ''rn''"      \<comment> \<open>the freshly allocated replacement node\<close>
abbreviation "rsucc \<equiv> ''rsucc''"   \<comment> \<open>the CAS success register (loop guard)\<close>

text \<open>The single retry loop of inc() (mordor @{text loop_id} 1).\<close>
definition rcu_loop :: loopid where "rcu_loop = 1"


section \<open>The RCU program @{text prog_RCU} (Core-typed labelled commands)\<close>

text \<open>The inc() critical section, retyped from the @{text rcuincloop} / @{text rcu3}
  digests into Core's @{typ command} / @{typ instr}, for one worker @{term "Thr 0"}.
  The body of the retry loop sits inside the rolled @{term While} (loop
  @{term rcu_loop}); the CAS-success register @{term rsucc} is the loop guard.

  Note the absence of any per-PC encoding: every line is a generic @{typ command}
  with ordinary operands.\<close>

definition prog_RCU :: program where
  "prog_RCU =
   [ \<comment> \<open>init preamble (mordor g.*): allocate + publish the rcu flag and the object\<close>
     g_il 1 is Malloc   vrcu (EInt 1),
     g_il 2 is WritePtr Rlx (EReg vrcu) (EInt 0),
     g_il 3 is Malloc   vC   (EInt 1),
     g_il 4 is WritePtr Rlx (EReg vC) (EInt 0),

     \<comment> \<open>worker Thr 0, inc(): enter the rcu read-side section, then the retry loop\<close>
     t0_il 1 is Malloc   rn (EInt 1),
     t0_il 2 is WritePtr Rlx (EReg vrcu) (EInt 1),      \<comment> \<open>rcu_enter (raise flag)\<close>
     t0_il 3 is While rcu_loop (EEq (EReg rsucc) (EInt 0))
        [ \<comment> \<open>rolled retry-loop body\<close>
          il_in (Thr 0) 4 rcu_loop is Faa     Acq Rel rs (EReg vC) (EInt 0),
          il_in (Thr 0) 5 rcu_loop is ReadPtr Rlx rv (EReg rs),
          il_in (Thr 0) 6 rcu_loop is WritePtr Rlx (EReg rn) (EAdd (EReg rv) (EInt 1)),
          il_in (Thr 0) 7 rcu_loop is Cas     Acq Rel rsucc (EReg vC) (EReg rs) (EReg rn)
        ],
     t0_il 8 is WritePtr Rlx (EReg vrcu) (EInt 0),       \<comment> \<open>rcu_exit (lower flag)\<close>

     \<comment> \<open>reclaim(): if the grace period elapsed, free the retired object\<close>
     t0_il 9 is IfElse (EEq (EReg rsucc) (EInt 1))
        [ t0_il 10 is Free rs ]
        []
   ]"

text \<open>The labels the RCU safety argument turns on (mirroring the UAF client's
  free / deref / exit triple): the reclaim free, the read-side deref (the @{term Faa}
  snapshot read), and the rcu-exit write.\<close>
definition rcu_free_il  :: iloc where "rcu_free_il  = t0_il 10"            \<comment> \<open>@{text "free rs"}\<close>
definition rcu_deref_il :: iloc where "rcu_deref_il = il_in (Thr 0) 4 rcu_loop"  \<comment> \<open>@{text "Faa C"} (deref)\<close>
definition rcu_exit_il  :: iloc where "rcu_exit_il  = t0_il 8"             \<comment> \<open>@{text "W rcu"} (exit)\<close>


section \<open>Structural well-formedness of @{term prog_RCU}\<close>

text \<open>Distinct instruction-labels have distinct @{text "#0"} event-labels (so the
  label algebra below never confuses two instructions).\<close>
lemma il_inj: "il o1 s1 = il o2 s2 \<longleftrightarrow> o1 = o2 \<and> s1 = s2"
  by (auto simp: il_def)

lemma ev0_eq_iff: "ev0 (il o1 s1) = ev0 (il o2 s2) \<longleftrightarrow> o1 = o2 \<and> s1 = s2"
  by (auto simp: ev0_def sub_def il_def)

text \<open>The init preamble and the worker top-level are present in the program text
  (the membership facts the @{text step.Step} rule consumes).\<close>
lemma prog_RCU_init_mem:
  "(g_il 1 is Malloc   vrcu (EInt 1)) \<in> set prog_RCU"
  "(g_il 2 is WritePtr Rlx (EReg vrcu) (EInt 0)) \<in> set prog_RCU"
  "(g_il 3 is Malloc   vC (EInt 1)) \<in> set prog_RCU"
  "(g_il 4 is WritePtr Rlx (EReg vC) (EInt 0)) \<in> set prog_RCU"
  "(t0_il 1 is Malloc rn (EInt 1)) \<in> set prog_RCU"
  "(t0_il 2 is WritePtr Rlx (EReg vrcu) (EInt 1)) \<in> set prog_RCU"
  "(t0_il 8 is WritePtr Rlx (EReg vrcu) (EInt 0)) \<in> set prog_RCU"
  by (simp_all add: prog_RCU_def)

text \<open>The retry loop is a genuine @{term While} keyed by @{term rcu_loop}; its body
  is the four-instruction read-modify-write sequence.  (Lookup through @{term prog}
  -- the rolled per-owner command map.)\<close>
lemma prog_RCU_loop:
  "prog prog_RCU (Thr 0) (t0_il 3)
     = Some (While rcu_loop (EEq (EReg rsucc) (EInt 0))
              [ il_in (Thr 0) 4 rcu_loop is Faa     Acq Rel rs (EReg vC) (EInt 0),
                il_in (Thr 0) 5 rcu_loop is ReadPtr Rlx rv (EReg rs),
                il_in (Thr 0) 6 rcu_loop is WritePtr Rlx (EReg rn) (EAdd (EReg rv) (EInt 1)),
                il_in (Thr 0) 7 rcu_loop is Cas     Acq Rel rsucc (EReg vC) (EReg rs) (EReg rn) ])"
  by (simp add: prog_def prog_RCU_def il_def il_in_def is_entry_def)

text \<open>The reclaim is a genuine @{term IfElse} whose THEN body is the single
  @{term Free}.\<close>
lemma prog_RCU_reclaim:
  "prog prog_RCU (Thr 0) (t0_il 9)
     = Some (IfElse (EEq (EReg rsucc) (EInt 1)) [ t0_il 10 is Free rs ] [])"
  by (simp add: prog_def prog_RCU_def il_def il_in_def is_entry_def)


section \<open>The generic per-command effect (one rule, no per-PC case)\<close>

text \<open>Each straight-line command shape that RCU uses fires through the SAME
  @{term cmd_effect} bridge -- there is no per-PC dispatch.  We record the effect of
  each shape against @{term prog_RCU}'s actual instructions; these feed directly
  into @{text step.Step}.\<close>

lemma rcu_effect_malloc:
  "cmd_effect casok (g_il 1) (Malloc vrcu (EInt 1)) \<rho>
     = Some ([AllocA (fresh \<rho>) (EInt 1)],
             [(sub (g_il 1) 0, AllocA (fresh \<rho>) (EInt 1))],
             set_reg (snd (next_sym \<rho>)) vrcu (fresh \<rho>))"
  by (simp add: next_sym_def Let_def)

lemma rcu_effect_writeptr:
  "cmd_effect casok (g_il 2) (WritePtr Rlx (EReg vrcu) (EInt 0)) \<rho>
     = Some ([Write Rlx (rg \<rho> vrcu) (EInt 0)],
             [(sub (g_il 2) 0, Write Rlx (rg \<rho> vrcu) (EInt 0))], \<rho>)"
  by (simp add: Let_def)

lemma rcu_effect_readptr:
  "cmd_effect casok (il_in (Thr 0) 5 rcu_loop) (ReadPtr Rlx rv (EReg rs)) \<rho>
     = Some ([Read Rlx (rg \<rho> rs) (fresh \<rho>)],
             [(sub (il_in (Thr 0) 5 rcu_loop) 0, Read Rlx (rg \<rho> rs) (fresh \<rho>))],
             set_reg (snd (next_sym \<rho>)) rv (fresh \<rho>))"
  by (simp add: next_sym_def Let_def)

lemma rcu_effect_free:
  "cmd_effect casok (t0_il 10) (Free rs) \<rho>
     = Some ([DeallocA (rg \<rho> rs)],
             [(sub (t0_il 10) 0, DeallocA (rg \<rho> rs))], \<rho>)"
  by (simp add: Let_def)

text \<open>The deref is an RMW (@{term Faa}) -- ONE command emitting TWO sub-events
  (@{text "#0"} the read, @{text "#1"} the write); the same generic bridge handles
  it, returning a non-empty effect (no per-PC special case).\<close>
lemma rcu_effect_faa_some:
  "\<exists>abar las \<rho>'. cmd_effect casok (il_in (Thr 0) 4 rcu_loop)
                   (Faa Acq Rel rs (EReg vC) (EInt 0)) \<rho> = Some (abar, las, \<rho>')"
  by (simp add: next_sym_def Let_def)

text \<open>The two structural commands carry NO straight-line effect (they are stepped by
  the branch rule / the -- out-of-scope -- loop rule, never the @{term Step} rule):
  this is what makes the loop genuinely a loop.\<close>
lemma rcu_effect_while_none:
  "cmd_effect casok (t0_il 3)
     (While rcu_loop (EEq (EReg rsucc) (EInt 0)) body) \<rho> = None"
  by simp

lemma rcu_effect_ifelse_none:
  "cmd_effect casok (t0_il 9) (IfElse b t f) \<rho> = None"
  by simp


section \<open>A steppable reachability chain over the loop-free init preamble\<close>

text \<open>The full RCU @{term Phi} (the mordor future set, with the retry/poll loops) is
  out of scope for this loop-free layer.  To exhibit that @{term prog_RCU} as DATA
  plugs into the OpSem step relation we use a single small future containing the two
  preamble events with one program-order edge @{text "g.1#0 -> g.2#0"} -- exactly
  the @{term horizon_lbls} pattern the UAF client uses.  This is a structural smoke test
  of the data-as-program wiring, NOT a safety claim.\<close>

abbreviation edge :: "iloc \<Rightarrow> iloc \<Rightarrow> (elabel \<times> elabel)" where
  "edge a b \<equiv> (ev0 a, ev0 b)"

text \<open>The one-future preamble @{term Phi}: a single program-order edge from the rcu
  alloc to its publishing write.\<close>
definition Phi_RCU_pre_exec :: future where
  "Phi_RCU_pre_exec = { edge (g_il 1) (g_il 2) }"

definition Phi_RCU_pre :: Phi where
  "Phi_RCU_pre = { Phi_RCU_pre_exec }"

text \<open>A single clean introduction rule for horizon membership via ONE witnessing
  future (the UAF idiom).\<close>
lemma in_horizon_lblsI:
  assumes "F \<in> Phi" and "consistent F H" and "l \<in> enabled_in F H"
  shows "l \<in> horizon_lbls Phi H"
  unfolding horizon_lbls_def using assms by blast

lemma pre_exec_in_Phi: "Phi_RCU_pre_exec \<in> Phi_RCU_pre"
  by (simp add: Phi_RCU_pre_def)

text \<open>Committing a single-action event extends the history's label set by exactly
  that label (the bookkeeping the chain tracks).\<close>
lemma hist_labels_commit_single:
  "hist_labels (commit_events [(l, a)] H) = insert l (hist_labels H)"
  by (simp add: commit_events_def hist_labels_def)

lemma hist_labels_empty [simp]: "hist_labels {} = {}"
  by (simp add: hist_labels_def)

lemma horizon_label_eq_ev0: "horizon_label l = ev0 l"
  by (simp add: horizon_label_def ev0_def)

text \<open>@{term instr_sublabel} of a @{term sub}-label at @{text 0} is itself.\<close>
lemma instr_sublabel_ev0 [simp]: "instr_sublabel (ev0 l) 0 = ev0 l"
  by (simp add: instr_sublabel_def ev0_def sub_def)

text \<open>The future is consistent with the empty history and with the post-g.1 history,
  and each preamble label is enabled at its history (g.1 has no predecessor; g.2's
  sole predecessor g.1 is committed first).\<close>

lemma pre_consistent_empty:
  "hist_labels H = {} \<Longrightarrow> consistent Phi_RCU_pre_exec H"
  unfolding consistent_def by (simp add: Phi_RCU_pre_exec_def)

lemma pre_consistent_g1:
  "hist_labels H = { ev0 (g_il 1) } \<Longrightarrow> consistent Phi_RCU_pre_exec H"
  unfolding consistent_def
  by (auto simp: Phi_RCU_pre_exec_def future_labels_def ev0_eq_iff)

lemma g1_enabled:
  "hist_labels H = {} \<Longrightarrow> ev0 (g_il 1) \<in> enabled_in Phi_RCU_pre_exec H"
  unfolding enabled_in_def
  by (auto simp: Phi_RCU_pre_exec_def future_labels_def ev0_eq_iff)

lemma g2_enabled:
  "hist_labels H = { ev0 (g_il 1) } \<Longrightarrow> ev0 (g_il 2) \<in> enabled_in Phi_RCU_pre_exec H"
  unfolding enabled_in_def
  by (auto simp: Phi_RCU_pre_exec_def future_labels_def ev0_eq_iff)

lemma g1_in_horizon: "hist_labels H = {} \<Longrightarrow> ev0 (g_il 1) \<in> horizon_lbls Phi_RCU_pre H"
  by (rule in_horizon_lblsI[OF pre_exec_in_Phi pre_consistent_empty g1_enabled])
lemma g2_in_horizon:
  "hist_labels H = { ev0 (g_il 1) } \<Longrightarrow> ev0 (g_il 2) \<in> horizon_lbls Phi_RCU_pre H"
  by (rule in_horizon_lblsI[OF pre_exec_in_Phi pre_consistent_g1 g2_enabled])

text \<open>Two preamble steps are enough to show the wiring: allocate the rcu flag
  (@{text "g.1"}) then publish it (@{text "g.2"}).  Each is a generic @{text
  step.Step}; the resulting config is @{term opsem_client.reachable}.\<close>

lemma reachable_RCU_preamble:
  "\<exists>\<sigma> \<rho> H. opsem_client.reachable prog_RCU Phi_RCU_pre (\<sigma>, \<rho>, H) \<and>
            hist_labels H = { ev0 (g_il 1), ev0 (g_il 2) }"
proof -
  define R where "R \<equiv> opsem_client.reachable prog_RCU Phi_RCU_pre"
  have r0: "R init_config"
    unfolding R_def by (rule opsem_client.reachable_init)
  \<comment> \<open>step 0: commit g.1 (Malloc rrcu)\<close>
  obtain \<sigma>1 \<rho>1 H1 where
    s1: "step prog_RCU Phi_RCU_pre init_config (\<sigma>1, \<rho>1, H1)"
    and h1: "hist_labels H1 = { ev0 (g_il 1) }"
  proof -
    let ?c = "Malloc vrcu (EInt 1)"
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 1) ?c init_renv = Some (abar, las, \<rho>')"
      and abar: "abar = [AllocA (fresh init_renv) (EInt 1)]"
      and las: "las = [(sub (g_il 1) 0, AllocA (fresh init_renv) (EInt 1))]"
      by (auto simp: next_sym_def Let_def split: prod.splits)
    have inh: "in_horizon (horizon_label (g_il 1)) abar Phi_RCU_pre {}"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using g1_in_horizon[of "{}"] by (simp add: hist_labels_def)
    have mem: "(g_il 1 is ?c) \<in> set prog_RCU" by (rule prog_RCU_init_mem)
    let ?st = "(apply_actions las init_mstate, \<rho>', commit_events las {})"
    have stp: "step prog_RCU Phi_RCU_pre init_config ?st"
      unfolding init_config_def
      by (rule step.Step[OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las {}) = { ev0 (g_il 1) }"
      by (simp add: las hist_labels_commit_single ev0_def)
    with stp show thesis using that by blast
  qed
  have r1: "R (\<sigma>1, \<rho>1, H1)"
    unfolding R_def using r0[unfolded R_def] s1 by (rule opsem_client.reachable_step)
  \<comment> \<open>step 1: commit g.2 (WritePtr *rrcu := 0)\<close>
  obtain \<sigma>2 \<rho>2 H2 where
    s2: "step prog_RCU Phi_RCU_pre (\<sigma>1, \<rho>1, H1) (\<sigma>2, \<rho>2, H2)"
    and h2: "hist_labels H2 = { ev0 (g_il 1), ev0 (g_il 2) }"
  proof -
    let ?c = "WritePtr Rlx (EReg vrcu) (EInt 0)"
    define act where "act = Write Rlx (rg \<rho>1 vrcu) (EInt 0)"
    obtain abar las \<rho>' where
      ce: "cmd_effect False (g_il 2) ?c \<rho>1 = Some (abar, las, \<rho>')"
      and abar: "abar = [act]"
      and las: "las = [(sub (g_il 2) 0, act)]"
      by (auto simp: act_def Let_def)
    have inh: "in_horizon (horizon_label (g_il 2)) abar Phi_RCU_pre H1"
      unfolding in_horizon_def horizon_label_eq_ev0 abar
      using g2_in_horizon[OF h1] by simp
    have mem: "(g_il 2 is ?c) \<in> set prog_RCU" by (rule prog_RCU_init_mem)
    let ?st = "(apply_actions las \<sigma>1, \<rho>', commit_events las H1)"
    have stp: "step prog_RCU Phi_RCU_pre (\<sigma>1, \<rho>1, H1) ?st"
      by (rule step.Step[OF mem _ _ ce inh refl refl]) auto
    have "hist_labels (commit_events las H1) = { ev0 (g_il 1), ev0 (g_il 2) }"
      by (auto simp: las hist_labels_commit_single h1 ev0_def)
    with stp show thesis using that by blast
  qed
  have r2: "R (\<sigma>2, \<rho>2, H2)"
    unfolding R_def using r1[unfolded R_def] s2 by (rule opsem_client.reachable_step)
  show ?thesis using r2[unfolded R_def] h2 by blast
qed

end
