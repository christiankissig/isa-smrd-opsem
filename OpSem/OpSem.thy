(*  Title:      OpSem/OpSem.thy
    Author:     Christian Kissig

    OpSem (REWORK_PLAN Phase 3a + 3b / workstreams W8a and W8b): the Episodic
    operational semantics.  This file provides

      1. the command/effect bridge -- a generic per-command effect that, for a
         command instance `(l is c)`, emits its labelled action sequence (reusing
         Core's `command` and MemSem's `apply_actions` / `faa_actions` /
         `cas_actions`; an RMW = one command, several sub-actions);
      2. the operational configuration `(sigma, rho, H)` -- `sigma` the MemSem
         `mstate`, `rho` the register/local environment, `H` the EventStruct
         `history` (an `event set`);
      3. the inductive `step prog Phi` relation with the straight-line / RMW step,
         the then/else branch rules, AND the W8b loop rules (`Loop` / `LoopExit`).
         A labelled command is taken only if its instruction-label is enabled,
         `(l : abar) \<in>* horizon Phi H`, applying the action effects to `sigma`,
         updating `rho`, and extending `H` with the committed event(s);
      4. a client locale `fixes prog Phi` and a `reachable` predicate (the
         reflexive-transitive closure of `step` from an initial config).

    W8b (milestone 3b) -- the `While` / lb-reset loop rules ADDED here:

      * `Loop`     -- the guard `b` of `(l is While lp b body)` holds along the
        path predicate and `l`'s guard label is in the horizon: commit the guard
        event `Branch (subst_expr rho b)` at `sub l 0`, exactly as `Then` commits
        an `IfElse` guard.  The body of the loop is NESTED (not in `set prg`) and
        is NOT stepped here; its events become enabled THROUGH the horizon at the
        representative iteration window (see the restriction note below).
      * `LoopExit` -- symmetric: the guard fails, commit `Branch (ENot ...)` and
        leave the loop.

    RESTRICTION vs full paper faithfulness (documented, not overclaimed).  The
    paper's lb-reset RELABELS the loop body per iteration (`el_iters` advances by
    one per back-edge) instead of UNROLLING into unboundedly many iterations.  The
    project's validated episodicity finding (mordor on `rcu-inc-loop.lit`,
    EventStruct `episodic` / `episodic_future`) is that an episodic Phi collapses
    every loop to a SINGLE representative iteration window: the `el_iters`
    component is degenerate, so the representative window suffices and unrolling is
    unnecessary.  Accordingly these rules commit the guard at the representative
    window `sub l 0` (matching `Then`/`Else`, whose committed labels also carry the
    degenerate `el_iters = []`) and do NOT unroll.  What is NOT yet modelled here:
    an explicit per-back-edge `el_iters` increment and the per-loop
    `sigma|^t_{\<ell>}` state restriction; under episodicity those are degenerate, so
    omitting them is sound (it admits no extra behaviours -- the guard commit is
    observation-only, `apply_action _ (Branch _)` leaves the alloc/memory state of
    sigma fixed and only narrows `phi`).  The episodicity meta-properties that
    JUSTIFY the single-window collapse live in EventStruct (`episodic_future`,
    `loop_free_episodic`).

    Depends on MemSem (sigma + action effects) and EventStruct (Phi + horizon),
    both session-qualified.
*)

theory OpSem
  imports "MemSem.MemSem" "EventStruct.EventStruct"
begin

section \<open>The register / local environment rho\<close>

text \<open>@{text rho} is the per-thread local state the operational layer threads
  alongside @{text sigma} and @{text H}.  A register names a SYMBOL (a value-symbol
  loaded by a read, or a symbolic location bound by @{term ReadRef} / @{term
  Malloc}); a program variable names a global symbolic location; @{term fresh} is a
  monotone counter handing out fresh symbols for loads and allocations.  Keeping
  registers and variables at the @{typ sym} granularity matches MemSem, whose
  actions are over symbols (@{typ sym}) and whose @{term evalE} is symbol-based.\<close>

record renv =
  rg    :: "reg \<Rightarrow> sym"       \<comment> \<open>register to its current value/location symbol\<close>
  vmap  :: "var \<Rightarrow> sym"      \<comment> \<open>global variable to its symbolic location\<close>
  fresh :: sym               \<comment> \<open>next fresh symbol (allocation / load counter)\<close>

definition init_renv :: renv where
  "init_renv = \<lparr> rg = (\<lambda>_. 0), vmap = (\<lambda>_. 0), fresh = 0 \<rparr>"

text \<open>Resolve a command-level expression to an ACTION-level expression by
  substituting each register @{term r} by its current symbol @{term "rg \<rho> r"} (a
  @{term ESym}).  After substitution the expression is register-free, so MemSem's
  @{term evalE} treats it faithfully.  (A bare @{term EDeref} is left to MemSem,
  which evaluates it degenerately; the operational layer resolves the pointer target
  through @{term resolve_loc} below where a location is needed.)\<close>

fun subst_expr :: "renv \<Rightarrow> expr \<Rightarrow> expr" where
  "subst_expr \<rho> (EInt n)    = EInt n"
| "subst_expr \<rho> (EReg r)    = ESym (rg \<rho> r)"
| "subst_expr \<rho> (ESym s)    = ESym s"
| "subst_expr \<rho> (EDeref e)  = EDeref (subst_expr \<rho> e)"
| "subst_expr \<rho> (EAdd a b)  = EAdd (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (ESub a b)  = ESub (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (EMul a b)  = EMul (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (EDiv a b)  = EDiv (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (EEq a b)   = EEq (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (ELeq a b)  = ELeq (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (ENot a)    = ENot (subst_expr \<rho> a)"
| "subst_expr \<rho> (EAnd a b)  = EAnd (subst_expr \<rho> a) (subst_expr \<rho> b)"
| "subst_expr \<rho> (EOr a b)   = EOr (subst_expr \<rho> a) (subst_expr \<rho> b)"

text \<open>Resolve a command-level expression to the SYMBOL it names as a location: a
  bare register / symbol is its own location symbol; everything else is currently
  approximated by the fresh-symbol-free default (the UAF client only ever
  dereferences a register).  This is the @{text "&x"} / pointer-target resolution
  the read/write-PTR and free commands use.\<close>

fun resolve_loc :: "renv \<Rightarrow> expr \<Rightarrow> sym" where
  "resolve_loc \<rho> (EReg r)   = rg \<rho> r"
| "resolve_loc \<rho> (ESym s)   = s"
| "resolve_loc \<rho> (EDeref e) = resolve_loc \<rho> e"
| "resolve_loc \<rho> _          = 0"

text \<open>Bind a register to a symbol.\<close>
definition set_reg :: "renv \<Rightarrow> reg \<Rightarrow> sym \<Rightarrow> renv" where
  "set_reg \<rho> r s = \<rho>\<lparr> rg := (rg \<rho>)(r := s) \<rparr>"

text \<open>Hand out the current fresh symbol and bump the counter.\<close>
definition next_sym :: "renv \<Rightarrow> sym \<times> renv" where
  "next_sym \<rho> = (fresh \<rho>, \<rho>\<lparr> fresh := Suc (fresh \<rho>) \<rparr>)"


section \<open>The command/effect bridge\<close>

text \<open>The labelled action sequence an instruction @{term "(l is c)"} emits, the
  resulting register environment, and (for a branch) the chosen continuation marker.

  The result of @{term cmd_effect} is @{text "(abar, las, rho')"} where
  @{term abar} is the bare action list (the @{text "(l : abar)"} the horizon
  membership consumes), @{term las} the SAME actions paired with their per-sub-event
  labels @{text "l#0, l#1, \<dots>"} (what @{term apply_actions} / @{term H} consume),
  and @{term "rho'"} the updated local environment.  An RMW is ONE command emitting
  several sub-actions (Core: @{term Faa} two, @{term Cas} three).

  @{term IfElse} / @{term While} are handled by the branch / (excluded) loop rules,
  not here: at the bridge they emit no straight-line effect.  A @{term Cas} needs the
  success bit (decided at step time against @{term sigma}); the bridge takes it as a
  parameter and the step rule supplies it.\<close>

definition sub :: "iloc \<Rightarrow> nat \<Rightarrow> elabel" where
  "sub l k = \<lparr> el_iloc = l, el_iters = [], el_k = k \<rparr>"

text \<open>The straight-line (non-branch, non-loop) effect of a command.  Returns
  @{term None} for the structural commands @{term IfElse} / @{term While} (handled by
  the branch / loop rules).  The Boolean @{term casok} is the CAS success bit
  (ignored by every other command).\<close>

fun cmd_effect ::
    "bool \<Rightarrow> iloc \<Rightarrow> command \<Rightarrow> renv
       \<Rightarrow> (action list \<times> (elabel \<times> action) list \<times> renv) option" where
  "cmd_effect casok l (Assign r e) \<rho> =
     \<comment> \<open>no event; bind @{term r} to the resolved location symbol of @{term e}\<close>
     Some ([], [], set_reg \<rho> r (resolve_loc \<rho> e))"
| "cmd_effect casok l (ReadRef r x) \<rho> =
     \<comment> \<open>take-address, no event; bind register to the variable's symbolic location\<close>
     Some ([], [], set_reg \<rho> r (vmap \<rho> x))"
| "cmd_effect casok l (ReadVar ord r x) \<rho> =
     (let (a, \<rho>') = next_sym \<rho>;
          act = Read ord (vmap \<rho> x) a
      in Some ([act], [(sub l 0, act)], set_reg \<rho>' r a))"
| "cmd_effect casok l (ReadPtr ord r e) \<rho> =
     (let (a, \<rho>') = next_sym \<rho>;
          act = Read ord (resolve_loc \<rho> e) a
      in Some ([act], [(sub l 0, act)], set_reg \<rho>' r a))"
| "cmd_effect casok l (WriteVar ord x e) \<rho> =
     (let act = Write ord (vmap \<rho> x) (subst_expr \<rho> e)
      in Some ([act], [(sub l 0, act)], \<rho>))"
| "cmd_effect casok l (WritePtr ord pe e) \<rho> =
     (let act = Write ord (resolve_loc \<rho> pe) (subst_expr \<rho> e)
      in Some ([act], [(sub l 0, act)], \<rho>))"
| "cmd_effect casok l (CFence ord) \<rho> =
     (let act = Fence ord in Some ([act], [(sub l 0, act)], \<rho>))"
| "cmd_effect casok l (Faa o\<^sub>r o\<^sub>w r e\<^sub>x e) \<rho> =
     (let (a, \<rho>') = next_sym \<rho>;
          x   = resolve_loc \<rho> e\<^sub>x;
          las = faa_actions (sub l 0) (sub l 1) o\<^sub>r o\<^sub>w x a (subst_expr \<rho> e)
      in Some (map snd las, las, set_reg \<rho>' r a))"
| "cmd_effect casok l (Cas o\<^sub>r o\<^sub>w r e\<^sub>x e\<^sub>s e\<^sub>n) \<rho> =
     (let (a, \<rho>') = next_sym \<rho>;
          x   = resolve_loc \<rho> e\<^sub>x;
          las = cas_actions casok (sub l 0) (sub l 1) (sub l 2) o\<^sub>r o\<^sub>w
                            x a (subst_expr \<rho> e\<^sub>s) (subst_expr \<rho> e\<^sub>n)
      in Some (map snd las, las, set_reg \<rho>' r a))"
| "cmd_effect casok l (Malloc r e) \<rho> =
     (let (x, \<rho>') = next_sym \<rho>;
          act = AllocA x (subst_expr \<rho> e)
      in Some ([act], [(sub l 0, act)], set_reg \<rho>' r x))"
| "cmd_effect casok l (Free r) \<rho> =
     (let act = DeallocA (rg \<rho> r)
      in Some ([act], [(sub l 0, act)], \<rho>))"
| "cmd_effect casok l (IfElse b t f) \<rho> = None"
| "cmd_effect casok l (While lp b body) \<rho> = None"

text \<open>Project the bare action list (the @{text abar} the horizon consumes).\<close>
definition cmd_abar ::
    "bool \<Rightarrow> iloc \<Rightarrow> command \<Rightarrow> renv \<Rightarrow> action list option" where
  "cmd_abar casok l c \<rho> = map_option fst (cmd_effect casok l c \<rho>)"


section \<open>Thread-indexed register state\<close>

text \<open>The register environment above (@{typ renv}) is ONE thread's local state.  The
  operational configuration carries a register environment PER thread -- a map from
  the owner @{typ owner} (@{term Init} preamble or a @{term "Thr t"}) to that
  thread's @{typ renv}.  The executing thread of an instruction at label @{term l}
  is its owner @{term "ilo_owner l"}; a step reads and updates ONLY that thread's
  slice.  This is the mechanised counterpart of the paper's thread-parameterised
  branching auxiliaries @{text "ifCond\<^sub>t"}, @{text "enterThen\<^sub>t"},
  @{text "enterElse\<^sub>t"}: the guard is resolved against the executing thread
  @{term t}'s registers, i.e.\ against @{term "\<rho> (ilo_owner l)"}.\<close>

type_synonym renvs = "owner \<Rightarrow> renv"

definition init_renvs :: renvs where
  "init_renvs = (\<lambda>_. init_renv)"


section \<open>Operational configuration\<close>

text \<open>A configuration is the triple @{text "(sigma, rho, H)"}: the MemSem state,
  the thread-indexed register environment @{typ renvs}, and the EventStruct history
  (an @{typ "event set"}).\<close>

type_synonym config = "mstate \<times> renvs \<times> history"

definition init_config :: config where
  "init_config = (init_mstate, init_renvs, {})"

text \<open>Commit a list of labelled sub-actions to a history (the events become part of
  @{term H}).\<close>
definition commit_events :: "(elabel \<times> action) list \<Rightarrow> history \<Rightarrow> history" where
  "commit_events las H = H \<union> set las"


section \<open>The step relation (NON-LOOP rules only)\<close>

text \<open>@{term horizon_label}: the event-label whose enabledness the horizon gate
  checks for an instruction at @{term l} -- its leading sub-event @{text "l#0"}.\<close>
definition horizon_label :: "iloc \<Rightarrow> elabel" where
  "horizon_label l = sub l 0"

text \<open>The inductive future-stepping relation @{text "prog, Phi \<turnstile> (sigma,rho,H) \<rightarrow>
  (sigma',rho',H')"}.  Five rules:

  \<^item> @{text Step} -- a straight-line (non-branch, non-loop) command whose label is
    enabled in @{text "horizon Phi H"} fires: resolve its effect against the executing
    thread's registers @{text "rho (ilo_owner l)"}, apply the action sub-sequence to
    @{text sigma}, update that thread's register slice, and extend @{text H} with the
    committed events.  RMWs ride this rule (their effect is several sub-actions).
  \<^item> @{text Then} -- an @{term IfElse} whose guard the path predicate admits commits
    the guard as a @{term Branch} event and proceeds into the THEN body's first
    instruction's effect.
  \<^item> @{text Else} -- symmetric, committing the negated guard and proceeding into the
    ELSE body.
  \<^item> @{text Loop} -- (W8b) a @{term While} whose guard the path predicate admits:
    commit the guard as a @{term Branch} event at @{text "l#0"}, exactly as
    @{text Then}.  The body is NESTED (not in @{term "set prg"}) and is NOT stepped
    here; under episodicity it is enabled through the horizon at the representative
    single-iteration window (the lb-reset collapses iterations rather than
    unrolling -- see the header comment).
  \<^item> @{text LoopExit} -- (W8b) symmetric: the guard fails, commit the negated guard
    @{text "Branch (ENot \<dots>)"} and leave the loop.

  The guard event for a branch / loop carries the label @{text "l#0"} of the
  @{term IfElse} / @{term While} instruction; the horizon gate uses that
  instruction's own label.  We thread @{term prg} only to fetch the program text; the
  executing thread is recovered from each label as @{term "ilo_owner l"}, and the
  register environment @{term \<rho>} is indexed by it.\<close>

inductive
  step :: "program \<Rightarrow> Phi \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  for prg :: program and Phi :: Phi
where
  Step:
    \<comment> \<open>straight-line / RMW command @{term c} at label @{term l} (not @{term IfElse} /
        @{term While}); enabled and effectful.  The executing thread is
        @{term "ilo_owner l"}; only its register slice @{term "\<rho> (ilo_owner l)"} is
        read and updated.\<close>
    "\<lbrakk> (l is c) \<in> set prg;
       \<forall>b tb fb. c \<noteq> IfElse b tb fb;  \<forall>lp b body. c \<noteq> While lp b body;
       cmd_effect casok l c (\<rho> (ilo_owner l)) = Some (abar, las, \<rho>t');
       in_horizon (horizon_label l) abar Phi H;
       \<sigma>' = apply_actions las \<sigma>;
       H' = commit_events las H \<rbrakk>
     \<Longrightarrow> step prg Phi (\<sigma>, \<rho>, H) (\<sigma>', \<rho>(ilo_owner l := \<rho>t'), H')"
| Then:
    \<comment> \<open>@{term IfElse} guard taken (THEN branch): commit the guard, resolved against the
        executing thread's registers @{term "\<rho> (ilo_owner l)"} (the paper's
        @{text "ifCond\<^sub>t"}).  Registers are unchanged by a branch.\<close>
    "\<lbrakk> (l is IfElse b tb fb) \<in> set prg;
       gact = Branch (subst_expr (\<rho> (ilo_owner l)) b);
       in_horizon (horizon_label l) [gact] Phi H;
       holds (SOME e. e \<in> phi \<sigma>) (subst_expr (\<rho> (ilo_owner l)) b);
       \<sigma>' = apply_action (sub l 0) gact \<sigma>;
       H' = commit_events [(sub l 0, gact)] H \<rbrakk>
     \<Longrightarrow> step prg Phi (\<sigma>, \<rho>, H) (\<sigma>', \<rho>, H')"
| Else:
    \<comment> \<open>@{term IfElse} guard not taken (ELSE branch): commit the negated guard,
        resolved against @{term "\<rho> (ilo_owner l)"}.\<close>
    "\<lbrakk> (l is IfElse b tb fb) \<in> set prg;
       gact = Branch (ENot (subst_expr (\<rho> (ilo_owner l)) b));
       in_horizon (horizon_label l) [gact] Phi H;
       \<not> holds (SOME e. e \<in> phi \<sigma>) (subst_expr (\<rho> (ilo_owner l)) b);
       \<sigma>' = apply_action (sub l 0) gact \<sigma>;
       H' = commit_events [(sub l 0, gact)] H \<rbrakk>
     \<Longrightarrow> step prg Phi (\<sigma>, \<rho>, H) (\<sigma>', \<rho>, H')"
| Loop:
    \<comment> \<open>(W8b) @{term While} guard holds (enter / iterate): commit the loop guard,
        resolved against @{term "\<rho> (ilo_owner l)"}, at the representative window
        @{text "l#0"}.  The nested body is enabled through the horizon, not stepped here.\<close>
    "\<lbrakk> (l is While lp b body) \<in> set prg;
       gact = Branch (subst_expr (\<rho> (ilo_owner l)) b);
       in_horizon (horizon_label l) [gact] Phi H;
       holds (SOME e. e \<in> phi \<sigma>) (subst_expr (\<rho> (ilo_owner l)) b);
       \<sigma>' = apply_action (sub l 0) gact \<sigma>;
       H' = commit_events [(sub l 0, gact)] H \<rbrakk>
     \<Longrightarrow> step prg Phi (\<sigma>, \<rho>, H) (\<sigma>', \<rho>, H')"
| LoopExit:
    \<comment> \<open>(W8b) @{term While} guard fails (exit): commit the negated guard and leave.\<close>
    "\<lbrakk> (l is While lp b body) \<in> set prg;
       gact = Branch (ENot (subst_expr (\<rho> (ilo_owner l)) b));
       in_horizon (horizon_label l) [gact] Phi H;
       \<not> holds (SOME e. e \<in> phi \<sigma>) (subst_expr (\<rho> (ilo_owner l)) b);
       \<sigma>' = apply_action (sub l 0) gact \<sigma>;
       H' = commit_events [(sub l 0, gact)] H \<rbrakk>
     \<Longrightarrow> step prg Phi (\<sigma>, \<rho>, H) (\<sigma>', \<rho>, H')"

text \<open>Sanity: the rules are @{text Step}, @{text Then}, @{text Else}, and the W8b
  loop rules @{text Loop} / @{text LoopExit} (the @{text lb}-reset, single-window).\<close>


section \<open>Reflexive-transitive closure and the client locale\<close>

text \<open>The multi-step relation: zero or more @{term step}s.\<close>
abbreviation steps :: "program \<Rightarrow> Phi \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
  "steps prg Phi \<equiv> (step prg Phi)\<^sup>*\<^sup>*"

lemma steps_refl: "steps prg Phi cfg cfg"
  by simp

lemma steps_step:
  "steps prg Phi cfg cfg' \<Longrightarrow> step prg Phi cfg' cfg'' \<Longrightarrow> steps prg Phi cfg cfg''"
  by (rule rtranclp.rtrancl_into_rtrancl)

text \<open>A configuration is REACHABLE from @{term cfg0} when it is in the
  reflexive-transitive closure of @{term step}.\<close>
definition reachable_from :: "program \<Rightarrow> Phi \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
  "reachable_from prg Phi cfg0 cfg \<longleftrightarrow> steps prg Phi cfg0 cfg"


subsection \<open>Client locale\<close>

text \<open>A client (UAF, RCU, \<dots>) instantiates the program text @{term prg} and its
  future set @{term Phi}; everything operational is then derived.  @{term reachable}
  is reachability from the canonical @{term init_config}.

  Locale inputs: OWN -- @{term prg}, @{term Phi} (fixed DATA, not relations;
  no assumption is placed on either here -- well-formedness, if wanted, is a
  client-side proof obligation, not a locale axiom). INHERITED -- none: this
  locale has no parent; it lives in this session alone and does NOT extend
  the sibling @{text OwickiGries} entry's @{text transition_system} (nor
  @{text Ownership}'s @{text ownership_system}), so a client wanting the
  Owicki-Gries / ownership machinery over @{term step} would have to bridge
  the two itself (the deferred "Phase 6" interpretation, see
  @{text "docs/W1_owicki_gries_design.md"} \<section>6) -- an
  @{text interpretation} or @{text sublocale} linking this locale's @{term
  step} to @{text transition_system}'s @{text astep} is not done anywhere in
  this codebase yet.\<close>

locale opsem_client =
  fixes prg :: program
    and Phi  :: Phi
begin

definition cstep :: "config \<Rightarrow> config \<Rightarrow> bool" where
  "cstep \<equiv> step prg Phi"

definition reachable :: "config \<Rightarrow> bool" where
  "reachable cfg \<longleftrightarrow> reachable_from prg Phi init_config cfg"

lemma reachable_init: "reachable init_config"
  by (simp add: reachable_def reachable_from_def)

lemma reachable_step:
  "reachable cfg \<Longrightarrow> step prg Phi cfg cfg' \<Longrightarrow> reachable cfg'"
  by (auto simp: reachable_def reachable_from_def
           intro: rtranclp.rtrancl_into_rtrancl)

text \<open>Reachability as an induction principle: a predicate holding at the initial
  config and preserved by every @{term step} holds at every reachable config -- the
  shape every client safety proof (UAF, RCU) uses.\<close>
lemma reachable_induct [consumes 1, case_names init step]:
  assumes "reachable cfg"
    and "P init_config"
    and "\<And>c c'. reachable c \<Longrightarrow> P c \<Longrightarrow> step prg Phi c c' \<Longrightarrow> P c'"
  shows "P cfg"
proof -
  have "reachable_from prg Phi init_config cfg" using assms(1) by (simp add: reachable_def)
  then have "steps prg Phi init_config cfg" by (simp add: reachable_from_def)
  then show ?thesis
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by (rule assms(2))
  next
    case (step y z)
    have "reachable y"
      by (simp add: reachable_def reachable_from_def step.hyps(1))
    from assms(3)[OF this step.IH step.hyps(2)] show ?case .
  qed
qed

end

end
