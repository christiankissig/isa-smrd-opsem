(*  Title:      MemSem/MemSem.thy
    Author:     Christian Kissig

    The thin SMRD memory semantics: the paper's program state
    sigma = (viswrite, memory, phi, RF) and the per-action effect sigma ~>_t sigma'.

    Per docs/SPIKE_C_smrd_memsem.md: MemSem carries NO coherence machinery -- no
    timestamps, modification order, per-thread views, visible-writes-by-timestamp,
    release/acquire view-merge, or `covered`.  ALL ordering (incl. release/acquire
    synchronisation) is delegated to Phi (ppo u DP) in the EventStruct/OpSem
    layers.  Memory orders survive ON actions (inputs to Phi) but have no
    view-merge effect here.  This makes the memory layer memory-model agnostic:
    SMRD-vs-RC11 is a property of Phi alone (Spike C, Q5).

    Depends only on Core.  Allocation discipline is folded in as `memory` +
    phi-disjointness.

    Representation choices (documented deviations, both pragmatic & noted):
    - phi is modelled SHALLOWLY as the set of admissible symbolic valuations
      (env set): TRUE = UNIV, conjunction = intersection, satisfiable = nonempty,
      x ==_phi y iff all admissible valuations agree.  This is the "constraint
      accumulator" of Spike C without committing to a syntactic formula datatype.
    - The per-loop restriction sigma|^t_{\\ell} for the `lb` reset (Spike C, Q2's
      iteration-indexed phi) is DEFERRED: it is an OpSem concern that must be
      designed together with the `lb` rule and the (Phi_RCU-gated) iteration order,
      mirroring Core's deferred linorder.  MemSem here gives the action effects and
      their local invariants.
*)

theory MemSem
  imports "Core.Core"
begin

section \<open>Symbolic valuations and expression evaluation\<close>

text \<open>A valuation assigns a concrete value to each symbol (read value-symbol or
  symbolic location).  Expression evaluation is over symbols and literals; at the
  action level expressions are register-free and deref-free (OpSem substitutes
  registers and resolves derefs before emitting actions), so @{term EReg}/@{term
  EDeref} take a degenerate value here.\<close>

type_synonym env = "sym \<Rightarrow> valu"

fun evalE :: "env \<Rightarrow> expr \<Rightarrow> valu" where
  "evalE e (EInt n)   = n"
| "evalE e (ESym s)   = e s"
| "evalE e (EReg _)   = 0"
| "evalE e (EDeref _) = 0"
| "evalE e (EAdd a b) = evalE e a + evalE e b"
| "evalE e (ESub a b) = evalE e a - evalE e b"
| "evalE e (EMul a b) = evalE e a * evalE e b"
| "evalE e (EDiv a b) = evalE e a div evalE e b"
| "evalE e (EEq a b)  = (if evalE e a = evalE e b then 1 else 0)"
| "evalE e (ELeq a b) = (if evalE e a \<le> evalE e b then 1 else 0)"
| "evalE e (ENot a)   = (if evalE e a = 0 then 1 else 0)"
| "evalE e (EAnd a b) = (if evalE e a \<noteq> 0 \<and> evalE e b \<noteq> 0 then 1 else 0)"
| "evalE e (EOr a b)  = (if evalE e a \<noteq> 0 \<or> evalE e b \<noteq> 0 then 1 else 0)"

definition holds :: "env \<Rightarrow> bexp \<Rightarrow> bool" where
  "holds e b \<longleftrightarrow> evalE e b \<noteq> 0"


section \<open>Writes and the program state\<close>

text \<open>A visible write records the writing event-label, its location, the value
  written, and its memory order (the order is an input to Phi, not used here).\<close>
record write_rec =
  w_label :: elabel
  w_loc   :: sym
  w_val   :: expr
  w_order :: mem_order

text \<open>The paper's program state.  @{term viswrite}: last visible write per
  symbolic location.  @{term memory}: allocated symbols.  @{term phi}: the path
  predicate as its set of admissible valuations.  @{term rf}: read-from edges
  (reader event-label to writer event-label).\<close>
record mstate =
  viswrite :: "sym \<rightharpoonup> write_rec"
  memory   :: "sym set"
  phi      :: "env set"
  rf       :: "(elabel \<times> elabel) set"

definition init_mstate :: mstate where
  "init_mstate = \<lparr> viswrite = Map.empty, memory = {}, phi = UNIV, rf = {} \<rparr>"

text \<open>Symbolic-location equivalence modulo @{term phi}: @{term x} and @{term y}
  denote the same address in every admissible valuation.\<close>
definition sym_eq :: "mstate \<Rightarrow> sym \<Rightarrow> sym \<Rightarrow> bool" where
  "sym_eq \<sigma> x y \<longleftrightarrow> (\<forall>e \<in> phi \<sigma>. e x = e y)"

text \<open>@{term sym_eq} is reflexive, symmetric, and transitive on every state, so
  @{text "viswrite(x)"} resolution modulo @{term phi} is well-behaved.\<close>
lemma sym_eq_refl: "sym_eq \<sigma> x x"
  by (simp add: sym_eq_def)

lemma sym_eq_sym: "sym_eq \<sigma> x y \<Longrightarrow> sym_eq \<sigma> y x"
  by (auto simp: sym_eq_def)

lemma sym_eq_trans: "sym_eq \<sigma> x y \<Longrightarrow> sym_eq \<sigma> y z \<Longrightarrow> sym_eq \<sigma> x z"
  by (auto simp: sym_eq_def)

text \<open>@{text "viswrite(x)"} resolved MODULO @{term phi} (Spike C, Q2's
  ``@{text "x \<equiv>\<^sub>\<phi> x'"}'' -- @{term viswrite} is keyed by syntactic symbol, so a
  read of @{term x} must consult the write at any @{term phi}-equal location).  We
  take the write at @{term x} itself when present, otherwise any write whose key is
  @{term phi}-equal to @{term x}.  When @{term phi}-equality is syntactic identity
  on the relevant keys (the common case) this collapses to the raw map lookup.\<close>
definition viswrite_at :: "mstate \<Rightarrow> sym \<Rightarrow> write_rec option" where
  "viswrite_at \<sigma> x =
     (case viswrite \<sigma> x of
        Some w \<Rightarrow> Some w
      | None   \<Rightarrow>
          (case (SOME y. y \<in> dom (viswrite \<sigma>) \<and> sym_eq \<sigma> x y) of _ \<Rightarrow>
             (if \<exists>y \<in> dom (viswrite \<sigma>). sym_eq \<sigma> x y
              then viswrite \<sigma> (SOME y. y \<in> dom (viswrite \<sigma>) \<and> sym_eq \<sigma> x y)
              else None)))"

text \<open>@{term viswrite_at} only ever yields a record actually stored in @{term
  viswrite}; hence it preserves the @{term wf_mstate} location invariant.\<close>
lemma viswrite_at_ran:
  "viswrite_at \<sigma> x = Some w \<Longrightarrow> \<exists>y. viswrite \<sigma> y = Some w"
  unfolding viswrite_at_def
  by (auto split: option.splits if_splits)

definition satisfiable :: "mstate \<Rightarrow> bool" where
  "satisfiable \<sigma> \<longleftrightarrow> phi \<sigma> \<noteq> {}"


section \<open>Per-action effects  sigma ~>_t sigma'\<close>

text \<open>Conjoin a constraint into the path predicate (intersection of admissible
  valuations).\<close>
definition conj_phi :: "(env \<Rightarrow> bool) \<Rightarrow> mstate \<Rightarrow> env set" where
  "conj_phi P \<sigma> = phi \<sigma> \<inter> {e. P e}"

text \<open>The thin effect of one labelled action (no coherence/views):
  \<^item> a read extends @{term rf} with the visible write and conjoins the rf
    value-equality @{text "alpha = val(viswrite x)"} into @{term phi};
  \<^item> a write updates the last visible write at its location;
  \<^item> an alloc adds a fresh symbol, conjoining its disjointness from the
    already-allocated symbols into @{term phi};
  \<^item> a dealloc removes the symbol;
  \<^item> a branch conjoins its guard;
  \<^item> a fence is a no-op.
  The memory order on read/write/fence has NO effect here (Spike C, Q4): its
  synchronisation is a ppo fact in Phi, and a failing CAS's acquire-only-ness shows
  up only as the ABSENCE of a release write, hence a missing ppo edge.\<close>
fun apply_action :: "elabel \<Rightarrow> action \<Rightarrow> mstate \<Rightarrow> mstate" where
  "apply_action l (Read ord x a) \<sigma> =
     (case viswrite_at \<sigma> x of
        None   \<Rightarrow> \<sigma>
      | Some w \<Rightarrow> \<sigma>\<lparr> rf  := rf \<sigma> \<union> {(l, w_label w)},
                      phi := conj_phi (\<lambda>e. e a = evalE e (w_val w)) \<sigma> \<rparr>)"
| "apply_action l (Write ord x ev) \<sigma> =
     \<sigma>\<lparr> viswrite := (viswrite \<sigma>)(x \<mapsto> \<lparr> w_label = l, w_loc = x, w_val = ev, w_order = ord \<rparr>) \<rparr>"
| "apply_action l (Branch b) \<sigma> =
     \<sigma>\<lparr> phi := conj_phi (\<lambda>e. evalE e b \<noteq> 0) \<sigma> \<rparr>"
| "apply_action l (Fence ord) \<sigma> = \<sigma>"
| "apply_action l (AllocA x v) \<sigma> =
     \<sigma>\<lparr> memory := insert x (memory \<sigma>),
        phi := conj_phi (\<lambda>e. \<forall>y \<in> memory \<sigma>. e x \<noteq> e y) \<sigma> \<rparr>"
| "apply_action l (DeallocA x) \<sigma> = \<sigma>\<lparr> memory := memory \<sigma> - {x} \<rparr>"

text \<open>Sequencing: apply a list of labelled sub-actions left-to-right.  This is the
  vehicle for RMWs (below) and for stepping a whole instruction's events.\<close>
definition apply_actions :: "(elabel \<times> action) list \<Rightarrow> mstate \<Rightarrow> mstate" where
  "apply_actions las \<sigma> = foldl (\<lambda>s (l, a). apply_action l a s) \<sigma> las"

lemma apply_actions_Nil [simp]: "apply_actions [] \<sigma> = \<sigma>"
  by (simp add: apply_actions_def)

lemma apply_actions_Cons [simp]:
  "apply_actions ((l, a) # las) \<sigma> = apply_actions las (apply_action l a \<sigma>)"
  by (simp add: apply_actions_def)


section \<open>Read-modify-writes as action sequences (Spike C, Q4)\<close>

text \<open>SMRD models an RMW as its constituent sub-actions, each carrying its OWN
  memory order; MemSem just applies the thin per-action effects in order.  There is
  no monolithic surrey @{text Update}/@{text is_releasing} -- the acquire/release
  asymmetry has NO @{term mstate} effect (Spike C, Q4); it surfaces only as the
  PRESENCE or ABSENCE of the release @{term Write} sub-action, which @{term Phi}
  reads off to (not) emit a ppo edge.

  @{term faa_actions}: fetch-and-add @{text "FAA(x, e)"} = @{text "R\<^bsub>o\<^sub>r\<^esub> x \<alpha>; W\<^bsub>o\<^sub>w\<^esub> x (\<alpha>+e)"}.
  The read symbol @{term a} (the loaded value) and the two sub-event labels are
  supplied by OpSem (Core: a @{term Faa} command spans @{text 2} event-labels).\<close>
definition faa_actions ::
    "elabel \<Rightarrow> elabel \<Rightarrow> mem_order \<Rightarrow> mem_order \<Rightarrow> sym \<Rightarrow> sym \<Rightarrow> expr
       \<Rightarrow> (elabel \<times> action) list" where
  "faa_actions l\<^sub>r l\<^sub>w o\<^sub>r o\<^sub>w x a e =
     [ (l\<^sub>r, Read o\<^sub>r x a), (l\<^sub>w, Write o\<^sub>w x (EAdd (ESym a) e)) ]"

text \<open>@{term cas_actions}: a compare-and-swap @{text "CAS(x, e\<^sub>s, n)"} is
  @{text "R\<^bsub>o\<^sub>r\<^esub> x \<alpha>; Branch(\<alpha> = e\<^sub>s); [W\<^bsub>o\<^sub>w\<^esub> x n]"}.  The boolean @{term succeeds} selects the
  paper's two rules (Spike C, Q4 / Core: a @{term Cas} spans @{text 3} event-labels,
  the @{term Write} absent on failure):
  \<^item> SUCCESS emits @{text "R; Branch(\<alpha> = e\<^sub>s); W\<^bsub>o\<^sub>w\<^esub> x n"} -- a (possibly releasing) write.
  \<^item> FAILURE emits only @{text "R; Branch(\<alpha> \<noteq> e\<^sub>s)"} -- NO write, hence NO release:
    an acquire-only RMW (ISO C11 7.17.7.4).  The acquire-ness is just @{term o\<^sub>r} on
    the read, with no @{term mstate} effect.\<close>
definition cas_actions ::
    "bool \<Rightarrow> elabel \<Rightarrow> elabel \<Rightarrow> elabel \<Rightarrow> mem_order \<Rightarrow> mem_order
       \<Rightarrow> sym \<Rightarrow> sym \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> (elabel \<times> action) list" where
  "cas_actions succeeds l\<^sub>r l\<^sub>b l\<^sub>w o\<^sub>r o\<^sub>w x a e\<^sub>s n =
     (if succeeds
      then [ (l\<^sub>r, Read o\<^sub>r x a),
             (l\<^sub>b, Branch (EEq (ESym a) e\<^sub>s)),
             (l\<^sub>w, Write o\<^sub>w x n) ]
      else [ (l\<^sub>r, Read o\<^sub>r x a),
             (l\<^sub>b, Branch (ENot (EEq (ESym a) e\<^sub>s))) ])"

text \<open>A failing CAS emits no @{term Write}: structurally, no sub-action updates
  @{term viswrite} (the Q4 acquire-only fact at the @{term mstate} level).\<close>
definition is_write_act :: "action \<Rightarrow> bool" where
  "is_write_act act \<longleftrightarrow> (\<exists>ord y v. act = Write ord y v)"

lemma cas_fail_no_write:
  "\<not> succeeds \<Longrightarrow>
     \<forall>(l, act) \<in> set (cas_actions succeeds l\<^sub>r l\<^sub>b l\<^sub>w o\<^sub>r o\<^sub>w x a e\<^sub>s n).
        \<not> is_write_act act"
  by (auto simp: cas_actions_def is_write_act_def)


section \<open>Well-formedness and local soundness (Spike C, Q5-local)\<close>

text \<open>The MemSem invariant: every visible-write record sits at its own location.\<close>
definition wf_mstate :: "mstate \<Rightarrow> bool" where
  "wf_mstate \<sigma> \<longleftrightarrow> (\<forall>x w. viswrite \<sigma> x = Some w \<longrightarrow> w_loc w = x)"

lemma wf_init: "wf_mstate init_mstate"
  by (simp add: wf_mstate_def init_mstate_def)

lemma wf_apply_action: "wf_mstate \<sigma> \<Longrightarrow> wf_mstate (apply_action l a \<sigma>)"
  by (cases a) (auto simp: wf_mstate_def conj_phi_def split: option.splits)

text \<open>The path predicate only ever TIGHTENS: an action adds constraints, it never
  admits new valuations.  (Hence impossible paths stay pruned -- Spike C, Q5.)\<close>
lemma phi_mono: "phi (apply_action l a \<sigma>) \<subseteq> phi \<sigma>"
  by (cases a) (auto simp: conj_phi_def split: option.splits)

lemma satisfiable_init: "satisfiable init_mstate"
  by (simp add: satisfiable_def init_mstate_def)

text \<open>Reads only grow @{term rf}; a read-from edge is never retracted.\<close>
lemma rf_mono: "rf \<sigma> \<subseteq> rf (apply_action l a \<sigma>)"
  by (cases a) (auto split: option.splits)


subsection \<open>Lifted to action sequences (RMWs, whole-instruction stepping)\<close>

lemma wf_apply_actions: "wf_mstate \<sigma> \<Longrightarrow> wf_mstate (apply_actions las \<sigma>)"
proof (induction las arbitrary: \<sigma>)
  case (Cons la las)
  obtain l a where "la = (l, a)" by (cases la)
  with Cons show ?case by (simp add: wf_apply_action)
qed simp

lemma phi_mono_actions: "phi (apply_actions las \<sigma>) \<subseteq> phi \<sigma>"
proof (induction las arbitrary: \<sigma>)
  case (Cons la las)
  obtain l a where "la = (l, a)" by (cases la)
  with Cons show ?case using phi_mono by force
qed simp

lemma rf_mono_actions: "rf \<sigma> \<subseteq> rf (apply_actions las \<sigma>)"
proof (induction las arbitrary: \<sigma>)
  case (Cons la las)
  obtain l a where "la = (l, a)" by (cases la)
  with Cons show ?case using rf_mono by force
qed simp

text \<open>The two RMW sequences therefore preserve well-formedness (Spike C, Q5-local).\<close>
lemma wf_faa_actions:
  "wf_mstate \<sigma> \<Longrightarrow> wf_mstate (apply_actions (faa_actions l\<^sub>r l\<^sub>w o\<^sub>r o\<^sub>w x a e) \<sigma>)"
  by (simp add: wf_apply_actions)

lemma wf_cas_actions:
  "wf_mstate \<sigma> \<Longrightarrow>
     wf_mstate (apply_actions (cas_actions s l\<^sub>r l\<^sub>b l\<^sub>w o\<^sub>r o\<^sub>w x a e\<^sub>s n) \<sigma>)"
  by (simp add: wf_apply_actions)

end
