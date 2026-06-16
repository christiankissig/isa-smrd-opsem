(*  Title:      EventStruct/EventStruct.thy
    Author:     RCU-C11-OpSem project (Episodic stack, layer 3: EventStruct)

    The SMRD event-structure semantics: events, preserved program order `ppo`,
    semantic dependency `DP`, executions, the future set `Phi` (a set of edge-sets
    over event-labels, one edge-set per execution -- matching the generated
    `Phi_P` / mordor `futures` array), histories, posterior futures, the
    horizon `horizonPhi_H` (the actions a history `H` enables next), the
    instruction-granularity membership `(l : abar) :elem: horizonPhi_H`, and an
    episodicity predicate.

    This layer DEFINES how Phi is CONSUMED: the operational layer (OpSem) consults
    Phi only through `horizonPhi_H`.  mordor is the computational ORACLE that
    PRODUCES a concrete Phi per program; nothing here computes Phi.

    Frozen interface per docs/SPIKE_B_label_digest_design.md sec 6:
      - EventStruct is parameterised over Core's `elabel`/`action`;
      - Phi is `(elabel * elabel) set set` (edge-sets per execution);
      - horizonPhi_H / `:elem:` use `pc` / `iterf` / `okey` from Core.

    Depends only on Core.Core.  No state effects (that is MemSem), no step relation
    (that is OpSem).  AFP-capable; abstract over the action alphabet via Core.
*)

theory EventStruct
  imports "Core.Core"
begin

section \<open>Events and event sets\<close>

text \<open>An EVENT is a labelled action @{text "l : a"} -- the paper's
  configuration element.  The label @{typ elabel} carries the program point,
  loop nesting and iteration vector; the @{typ action} is the memory effect.\<close>

type_synonym event = "elabel \<times> action"

definition ev_label :: "event \<Rightarrow> elabel" where
  "ev_label e = fst e"

definition ev_action :: "event \<Rightarrow> action" where
  "ev_action e = snd e"

lemma ev_label_simp [simp]: "ev_label (l, a) = l"
  by (simp add: ev_label_def)

lemma ev_action_simp [simp]: "ev_action (l, a) = a"
  by (simp add: ev_action_def)

text \<open>The owner / thread that emits an event (lifted from the label's @{typ iloc}).\<close>
definition ev_owner :: "event \<Rightarrow> owner" where
  "ev_owner e = ilo_owner (el_iloc (ev_label e))"

text \<open>The event labels of a set of events.\<close>
definition labels_of :: "event set \<Rightarrow> elabel set" where
  "labels_of E = ev_label ` E"


section \<open>Preserved program order and semantic dependency\<close>

text \<open>The two edge sources Phi is built from (mordor emits @{text "ppo \<union> DP"}
  edges; this layer takes them as the abstract relations they range over).

  @{text ppo} -- PRESERVED PROGRAM ORDER -- is the program-faithful order of
  Core (@{term elabel_lt}), parameterised by the static loop-header table
  @{text hdr}: an outer loop's iteration dominates an inner loop's position, which
  is exactly what the @{text lb} rule needs.  We expose it both as a label
  relation and lifted to events.\<close>

definition ppo_lbl :: "(loopid \<Rightarrow> nat) \<Rightarrow> (elabel \<times> elabel) set" where
  "ppo_lbl hdr = {(a, b). elabel_lt hdr a b}"

definition ppo :: "(loopid \<Rightarrow> nat) \<Rightarrow> (event \<times> event) set" where
  "ppo hdr = {(e1, e2). (ev_label e1, ev_label e2) \<in> ppo_lbl hdr}"

text \<open>@{text DP} -- SEMANTIC DEPENDENCE (data / address / control + the
  read-from contribution).  It is genuinely program- AND execution-specific (it
  depends on which write each read takes, i.e. on @{text RF}), so it cannot be
  derived from labels alone; mordor computes it per execution.  Here it is an
  abstract parameter: a relation over event-labels supplied alongside Phi.  We
  keep it as a type so downstream layers can instantiate it.\<close>

type_synonym dep_rel = "(elabel \<times> elabel) set"

text \<open>The combined per-execution dependency edge relation @{text "ppo \<union> DP"}
  over labels -- the thing one element of Phi enumerates.\<close>
definition ppo_DP :: "(loopid \<Rightarrow> nat) \<Rightarrow> dep_rel \<Rightarrow> (elabel \<times> elabel) set" where
  "ppo_DP hdr DP = ppo_lbl hdr \<union> DP"


section \<open>Executions\<close>

text \<open>An EXECUTION bundles the events that occur with the per-execution
  semantic-dependence relation @{text DP} (read-from is folded into @{text DP} at
  the EventStruct level; the concrete @{text RF} lives in MemSem's @{text sigma}).
  This is the per-execution object mordor produces one of for each entry of its
  @{text futures} array.\<close>

record execution =
  exec_events :: "event set"
  exec_DP     :: dep_rel

text \<open>The @{text "ppo \<union> DP"} edge-set of an execution (its future, before we
  forget the actions and keep only the label edges).\<close>
definition exec_edges :: "(loopid \<Rightarrow> nat) \<Rightarrow> execution \<Rightarrow> (elabel \<times> elabel) set" where
  "exec_edges hdr X =
     {(a, b) \<in> ppo_DP hdr (exec_DP X).
        a \<in> labels_of (exec_events X) \<and> b \<in> labels_of (exec_events X)}"

text \<open>Well-formedness: edges of @{text DP} stay within the execution's labels,
  and @{text ppo} is irreflexive on them (no event before itself).\<close>
definition wf_execution :: "(loopid \<Rightarrow> nat) \<Rightarrow> execution \<Rightarrow> bool" where
  "wf_execution hdr X \<longleftrightarrow>
     (\<forall>(a, b) \<in> exec_DP X.
        a \<in> labels_of (exec_events X) \<and> b \<in> labels_of (exec_events X)) \<and>
     (\<forall>l \<in> labels_of (exec_events X). \<not> elabel_lt hdr l l)"


section \<open>The future set Phi\<close>

text \<open>A FUTURE is one execution's dependency edge-set: a set of
  @{text "(elabel \<times> elabel)"} edges over event-labels.  The generated constant
  @{text Phi_P} (mordor's @{text futures} array, rendered by
  @{text generate_phi.py}) has exactly this shape -- one edge-set per execution.\<close>

type_synonym future = "(elabel \<times> elabel) set"

text \<open>@{text Phi} is the FUTURE SET: a set of futures (edge-sets), one per
  execution.  This is the frozen interface type (Spike B sec 6):
  @{text "Phi :: (elabel \<times> elabel) set set"}.  mordor PRODUCES it; this layer
  only CONSUMES it (via @{term horizonPhi} below).\<close>

type_synonym Phi = "future set"

text \<open>Render the future set of a set of executions (how a generated
  @{text Phi_P} relates to a family of executions).\<close>
definition phi_of :: "(loopid \<Rightarrow> nat) \<Rightarrow> execution set \<Rightarrow> Phi" where
  "phi_of hdr Xs = (\<lambda>X. exec_edges hdr X) ` Xs"

text \<open>The labels that occur as an endpoint anywhere in a future.\<close>
definition future_labels :: "future \<Rightarrow> elabel set" where
  "future_labels F = fst ` F \<union> snd ` F"


section \<open>Histories\<close>

text \<open>A HISTORY @{text H} records the events committed so far: a set of
  @{text "l : a"} pairs (same shape as MemSem / OpSem's @{text H}).  It is exactly
  @{typ "event set"}; we name it for readability and give the projections the
  rules use.\<close>

type_synonym history = "event set"

text \<open>The labels already committed in @{text H}.\<close>
definition hist_labels :: "history \<Rightarrow> elabel set" where
  "hist_labels H = ev_label ` H"

text \<open>@{text "iter(H)(\<ell>)"} -- the @{text lb} guard's per-loop iteration maximum
  over a history.  Re-exported from Core (@{term iter_H}) at the @{typ history}
  type for convenience.\<close>
definition hist_iter :: "history \<Rightarrow> loopid \<Rightarrow> iter" where
  "hist_iter H lp = iter_H H lp"

lemma hist_iter_unfold: "hist_iter H lp = iter_H H lp"
  by (simp add: hist_iter_def)


section \<open>The horizon: how Phi is consumed\<close>

text \<open>This is the central deliverable: @{text horizonPhi_H} = the actions a
  history @{text H} enables NEXT.  The operational layer consults @{text Phi}
  ONLY through this function.

  Semantics (paper @{text "horizonPhi_H"}): a label @{text l} is enabled in a
  future @{text F} given @{text H} iff @{text l} is not already committed in
  @{text H} and ALL of its @{text "(ppo \<union> DP)"} predecessors in @{text F} are
  already committed in @{text H} -- i.e. every edge @{text "(p, l) \<in> F"} has its
  source @{text p} in @{text "labels(H)"}.  These are the @{text F}-minimal,
  not-yet-done labels just past the @{text H} frontier.

  We expose three granularities:
    1. @{term enabled_in} -- the enabled LABELS in ONE future @{text F};
    2. @{term horizon_lbls} -- the enabled labels across Phi (union over futures,
       restricted to futures CONSISTENT with @{text H}, see @{term consistent});
    3. @{term horizonPhi} -- the enabled labels paired with the action a digest
       supplies (the @{text "(l : abar)"} the step rule consumes), exposed via the
       membership @{term in_horizon} below.\<close>

definition enabled_in :: "future \<Rightarrow> history \<Rightarrow> elabel set" where
  "enabled_in F H =
     {l \<in> future_labels F.
        l \<notin> hist_labels H \<and> (\<forall>p. (p, l) \<in> F \<longrightarrow> p \<in> hist_labels H)}"

text \<open>A future @{text F} is CONSISTENT with a history @{text H} when every label
  already committed in @{text H} that appears in @{text F} has all its @{text F}
  predecessors committed too -- i.e. @{text H}'s committed-and-in-@{text F} labels
  form an @{text F}-downward-closed frontier.  Only consistent futures contribute
  to the horizon (mordor's @{text futures} are the maximal executions; @{text H}
  selects the live ones).\<close>

definition consistent :: "future \<Rightarrow> history \<Rightarrow> bool" where
  "consistent F H \<longleftrightarrow>
     (\<forall>l \<in> hist_labels H \<inter> future_labels F.
        \<forall>p. (p, l) \<in> F \<longrightarrow> p \<in> hist_labels H)"

text \<open>The horizon LABELS across the whole future set: the labels enabled by some
  future of @{text Phi} that is consistent with @{text H}.\<close>

definition horizon_lbls :: "Phi \<Rightarrow> history \<Rightarrow> elabel set" where
  "horizon_lbls Phi H = (\<Union>F \<in> {F \<in> Phi. consistent F H}. enabled_in F H)"

text \<open>@{text horizonPhi_H}: the horizon as @{text "(label, action)"} EVENTS.
  An action is associated with a horizon label by an instruction's emitted
  action sequence; abstractly here a candidate event @{text "(l, a)"} is in the
  horizon iff its label is a horizon label.  (OpSem refines this by checking the
  action against the digest's emitted @{term n_events} sequence; at the
  EventStruct level the alphabet is abstract, so the label gate is the interface.)\<close>

definition horizonPhi :: "Phi \<Rightarrow> history \<Rightarrow> event set" where
  "horizonPhi Phi H = {e. ev_label e \<in> horizon_lbls Phi H}"

text \<open>The paper's instruction-granularity membership @{text "(l : abar) :elem:
  horizonPhi_H"} (Spike B / W1 sec 7: freeze @{text "'act"} at instruction, not
  event, granularity).  An instruction is enabled when its label is a horizon
  label and its emitted action sequence @{text abar} has the right arity; the
  per-action labels are @{text "l#0 .. l#(n-1)"} sharing the @{text iloc} /
  @{term el_iters}, differing only in @{term el_k}.  We model @{text abar} as the
  action list the instruction emits and check the leading sub-event @{text "#0"}
  is enabled.\<close>

definition instr_sublabel :: "elabel \<Rightarrow> nat \<Rightarrow> elabel" where
  "instr_sublabel l k = l\<lparr> el_k := k \<rparr>"

definition in_horizon :: "elabel \<Rightarrow> action list \<Rightarrow> Phi \<Rightarrow> history \<Rightarrow> bool"
  ("((_ : _)/ \<in>* horizon _ _)" [55, 55, 55, 55] 54) where
  "in_horizon l abar Phi H \<longleftrightarrow>
     abar \<noteq> [] \<and> instr_sublabel l 0 \<in> horizon_lbls Phi H"


section \<open>Posterior futures\<close>

text \<open>The POSTERIOR future of @{text Phi} after committing a label @{text l}
  (the future set restricted to the executions that still agree with the extended
  history).  Stepping @{text l} narrows @{text Phi} to those futures in which
  @{text l} actually occurs; horizons computed against the posterior set drive the
  next step.  This is the @{text Phi}-side of one operational step.\<close>

definition post_label :: "Phi \<Rightarrow> elabel \<Rightarrow> Phi" where
  "post_label Phi l = {F \<in> Phi. l \<in> future_labels F}"

text \<open>The posterior future set after committing a whole event @{text "(l, a)"} to
  the history @{text H} (history grows, @{text Phi} narrows).\<close>

definition posterior :: "Phi \<Rightarrow> history \<Rightarrow> event \<Rightarrow> Phi \<times> history" where
  "posterior Phi H e = (post_label Phi (ev_label e), insert e H)"

lemma posterior_history: "snd (posterior Phi H e) = insert e H"
  by (simp add: posterior_def)

lemma posterior_phi: "fst (posterior Phi H e) = post_label Phi (ev_label e)"
  by (simp add: posterior_def)

text \<open>Posterior is monotone in narrowing: the posterior set is a subset.\<close>
lemma post_label_subset: "post_label Phi l \<subseteq> Phi"
  by (auto simp: post_label_def)


section \<open>Episodicity\<close>

text \<open>EPISODICITY: a program is episodic when every future collapses to a SINGLE
  posterior iteration per loop -- the property the @{text lb} reset relies on
  (REWORK_PLAN sec ``Caveat for the iter-vector design'': episodic clients UAF and
  RCU collapse to a single posterior iteration, so the @{term el_iters} component
  is effectively degenerate, always @{text 1}, in their Phi).

  We give the predicate at the future-set level: @{text Phi} is episodic for the
  loop set used by a program when, in every future, each loop carries at most ONE
  iteration value among the labels of that future.  Formally: for every future
  @{text F} and loop @{text lp}, the set of iterations @{term iterf} assigns to
  @{text lp} across @{text F}'s labels has at most one element.\<close>

definition future_loop_iters :: "future \<Rightarrow> loopid \<Rightarrow> iter set" where
  "future_loop_iters F lp =
     {i. \<exists>l \<in> future_labels F. iterf l lp = Some i}"

text \<open>An episodic future assigns AT MOST ONE iteration value to each loop across
  its labels.  We state this as @{term finite} together with @{text "card \<le> 1"}:
  the finiteness conjunct is essential, because @{term card} collapses every
  INFINITE set to @{text 0}, so a bare @{text "card \<dots> \<le> 1"} would be silently
  satisfied by a future that mentions infinitely many iterations of a loop -- the
  exact opposite of ``single posterior iteration''.  With finiteness in hand the
  predicate genuinely means ``at most one iteration per loop'', which is what the
  @{text lb}-reset / single-iteration-window argument below relies on.  (For the
  episodic clients UAF and RCU each future is a finite edge set, so the finiteness
  conjunct is discharged for free.)\<close>
definition episodic_future :: "future \<Rightarrow> bool" where
  "episodic_future F \<longleftrightarrow>
     (\<forall>lp. finite (future_loop_iters F lp) \<and> card (future_loop_iters F lp) \<le> 1)"

definition episodic :: "Phi \<Rightarrow> bool" where
  "episodic Phi \<longleftrightarrow> (\<forall>F \<in> Phi. episodic_future F)"

text \<open>A loop-free future is trivially episodic (no label assigns any iteration to
  any loop, so each per-loop iteration set is empty).\<close>
lemma loop_free_episodic:
  assumes "\<forall>l \<in> future_labels F. ilo_loops (el_iloc l) = []"
  shows "episodic_future F"
proof -
  have "\<And>lp. future_loop_iters F lp = {}"
  proof -
    fix lp
    have "\<And>i. i \<notin> future_loop_iters F lp"
    proof -
      fix i
      show "i \<notin> future_loop_iters F lp"
      proof
        assume "i \<in> future_loop_iters F lp"
        then obtain l where "l \<in> future_labels F" and "iterf l lp = Some i"
          by (auto simp: future_loop_iters_def)
        with assms have "ilo_loops (el_iloc l) = []" by blast
        hence "iterf l lp = None"
          by (simp add: iterf_def)
        with \<open>iterf l lp = Some i\<close> show False by simp
      qed
    qed
    thus "future_loop_iters F lp = {}" by blast
  qed
  \<comment> \<open>Every per-loop iteration set is empty, hence finite with cardinality @{text 0}.\<close>
  thus ?thesis by (simp add: episodic_future_def)
qed

text \<open>Hence a loop-free future set (every label outside all loops, as for the UAF
  client) is episodic.\<close>
lemma loop_free_episodic_Phi:
  assumes "\<forall>F \<in> Phi. \<forall>l \<in> future_labels F. ilo_loops (el_iloc l) = []"
  shows "episodic Phi"
  using assms loop_free_episodic by (auto simp: episodic_def)

text \<open>The deep episodicity meta-properties tying @{term episodic} to the
  @{text lb}-reset (that an episodic Phi makes the @{text lb} rule fire at most
  once per loop boundary, and that the horizon over the posterior set stays
  within a single iteration window) are OpSem obligations -- they need the
  @{text lb} reset rule and the @{text hdr}-keyed @{term elabel_lt} faithfulness,
  which is @{text Phi_RCU}-gated (Core's deferred linorder, Spike B residual 2).
  We state the single-iteration-window consequence as a TODO obligation for the
  OpSem layer to discharge once those exist.\<close>

lemma episodic_single_iteration_window:
  \<comment> \<open>Under episodicity, two distinct iterations of the same loop never coexist as
      endpoints of any single future's edges; the @{text lb} reset is what keeps
      the horizon single-windowed.\<close>
  assumes "episodic Phi" and "F \<in> Phi"
  assumes "l1 \<in> future_labels F" and "l2 \<in> future_labels F"
  assumes "iterf l1 lp = Some i1" and "iterf l2 lp = Some i2"
  shows "i1 = i2"
proof -
  from \<open>episodic Phi\<close> \<open>F \<in> Phi\<close> have "episodic_future F"
    by (simp add: episodic_def)
  hence fin: "finite (future_loop_iters F lp)"
    and crd: "card (future_loop_iters F lp) \<le> 1"
    by (simp_all add: episodic_future_def)
  \<comment> \<open>Both iterations are members of the per-loop iteration set of @{text F}.\<close>
  from \<open>l1 \<in> future_labels F\<close> \<open>iterf l1 lp = Some i1\<close>
  have m1: "i1 \<in> future_loop_iters F lp"
    by (auto simp: future_loop_iters_def)
  from \<open>l2 \<in> future_labels F\<close> \<open>iterf l2 lp = Some i2\<close>
  have m2: "i2 \<in> future_loop_iters F lp"
    by (auto simp: future_loop_iters_def)
  \<comment> \<open>A finite set of cardinality at most one has all members equal.\<close>
  from fin crd m1 m2 show "i1 = i2"
    using card_le_Suc0_iff_eq[of "future_loop_iters F lp"] by simp
qed

end
