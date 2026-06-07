(*  Title:      OwickiGries/OwickiGries.thy
    Author:     RCU-C11-OpSem project (Track A, first AFP target)

    A generic Owicki-Gries / rely-guarantee program logic over an ABSTRACT
    transition system.  Depends only on HOL (imports Main); it is decoupled
    from the Episodic OpSem and the rest of the project, so that it (together
    with the sibling Ownership entry) can be submitted to the AFP on its own.

    See docs/W1_owicki_gries_design.md and REWORK_PLAN.md (Decision 7, Phase 5,
    Risk 6).

    WIP: all proofs are `sorry`'d.  The point of this file is to fix the locale
    interface, the definitions, and the theorem STATEMENTS.
*)

theory OwickiGries
  imports Main
begin

section ‹Shallow assertions›

text ‹An assertion is the set of states satisfying it.  This keeps the logic
  HOL-only and lets assertions mention any component of the (abstract) state.›

type_synonym 's assn = "'s set"


section ‹The command language (parameterised over abstract atomic actions)›

text ‹Basic statements are abstract atomic actions of type @{typ 'act}; guards
  are state predicates @{typ "'s set"}.›

datatype ('act, 's) com =
    Atom 'act
  | Skip
  | Seq   "('act,'s) com" "('act,'s) com"
  | Cond  "'s set" "('act,'s) com" "('act,'s) com"
  | While "'s set" "('act,'s) com"


section ‹The abstract transition-system locale›

text ‹The single fixed parameter is the atomic-step relation.  It is an
  arbitrary binary relation: NOT assumed total, deterministic, or always
  enabled.  This is what lets a (non-deterministic, horizon-guarded,
  history-dependent) Episodic OpSem step interpret it later (Risk 6).›

locale transition_system =
  fixes astep :: "'act ⇒ 's ⇒ 's ⇒ bool"
begin

subsection ‹Sequential small-step semantics›

inductive seq_step ::
  "('act,'s) com × 's ⇒ ('act,'s) com × 's ⇒ bool"
where
  Atom:   "astep a s s' ⟹ seq_step (Atom a, s) (Skip, s')"
| Seq1:   "seq_step (c1, s) (c1', s') ⟹ seq_step (Seq c1 c2, s) (Seq c1' c2, s')"
| Seq2:   "seq_step (Seq Skip c2, s) (c2, s)"
| CondT:  "s ∈ b ⟹ seq_step (Cond b c1 c2, s) (c1, s)"
| CondF:  "s ∉ b ⟹ seq_step (Cond b c1 c2, s) (c2, s)"
| WhileT: "s ∈ b ⟹ seq_step (While b c, s) (Seq c (While b c), s)"
| WhileF: "s ∉ b ⟹ seq_step (While b c, s) (Skip, s)"

subsection ‹Parallel (interleaving) small-step semantics›

text ‹A parallel program is a list of sequential commands (one per thread); a
  configuration is the residual thread pool plus the shared state.›

inductive par_step ::
  "(('act,'s) com list × 's) ⇒ (('act,'s) com list × 's) ⇒ bool"
where
  Par: "⟦ i < length cs; seq_step (cs ! i, s) (c', s') ⟧
          ⟹ par_step (cs, s) (cs[i := c'], s')"

abbreviation par_steps ::
  "(('act,'s) com list × 's) ⇒ (('act,'s) com list × 's) ⇒ bool"
  where "par_steps ≡ par_step⇧*⇧*"

text ‹A thread is terminated when its residual command is @{const Skip}; the
  whole program has terminated at @{term "replicate n Skip"}.›

end  \<comment> ‹@{locale transition_system}›


section ‹Annotated commands (Owicki-Gries proof outlines)›

text ‹A proof outline annotates each node with the assertion holding before it.›

datatype ('act, 's) ann =
    ABasic "'s set" 'act
  | ASkip  "'s set"
  | AComp  "('act,'s) ann" "('act,'s) ann"
  | ACond  "'s set" "'s set" "('act,'s) ann" "('act,'s) ann"
  | AWhile "'s set" "'s set" "('act,'s) ann"

text ‹@{term pre}: the head assertion of an outline node.›
primrec pre :: "('act,'s) ann ⇒ 's set" where
  "pre (ABasic P a)       = P"
| "pre (ASkip P)          = P"
| "pre (AComp c1 c2)      = pre c1"
| "pre (ACond P b c1 c2)  = P"
| "pre (AWhile P b c)     = P"

text ‹@{term strip}: the underlying command (assertions erased).›
primrec strip :: "('act,'s) ann ⇒ ('act,'s) com" where
  "strip (ABasic P a)      = Atom a"
| "strip (ASkip P)         = Skip"
| "strip (AComp c1 c2)     = Seq (strip c1) (strip c2)"
| "strip (ACond P b c1 c2) = Cond b (strip c1) (strip c2)"
| "strip (AWhile P b c)    = While b (strip c)"

text ‹@{term assertions}: every assertion occurring in an outline.›
primrec assertions :: "('act,'s) ann ⇒ 's set set" where
  "assertions (ABasic P a)      = {P}"
| "assertions (ASkip P)         = {P}"
| "assertions (AComp c1 c2)     = assertions c1 ∪ assertions c2"
| "assertions (ACond P b c1 c2) = insert P (assertions c1 ∪ assertions c2)"
| "assertions (AWhile P b c)    = insert P (assertions c)"

text ‹@{term atomics}: the @{text "(local-precondition, action)"} pair of every
  basic statement.›
primrec atomics :: "('act,'s) ann ⇒ ('s set × 'act) set" where
  "atomics (ABasic P a)      = {(P, a)}"
| "atomics (ASkip P)         = {}"
| "atomics (AComp c1 c2)     = atomics c1 ∪ atomics c2"
| "atomics (ACond P b c1 c2) = atomics c1 ∪ atomics c2"
| "atomics (AWhile P b c)    = atomics c"


section ‹The proof system (in the locale context)›

context transition_system
begin

subsection ‹Local correctness (sequential Hoare, partial)›

text ‹The basic rule is in partial-correctness shape: it is vacuous when the
  abstract step is blocked (no successor), so guarded/non-deterministic atomic
  actions are fine.›

inductive loc_correct :: "('act,'s) ann ⇒ 's set ⇒ bool" where
  Basic: "(⋀s s'. s ∈ P ⟹ astep a s s' ⟹ s' ∈ Q)
            ⟹ loc_correct (ABasic P a) Q"
| Skip:  "P ⊆ Q ⟹ loc_correct (ASkip P) Q"
| Comp:  "⟦ loc_correct c1 (pre c2); loc_correct c2 Q ⟧
            ⟹ loc_correct (AComp c1 c2) Q"
| Cond:  "⟦ P ∩ b ⊆ pre c1; P ∩ (- b) ⊆ pre c2;
            loc_correct c1 Q; loc_correct c2 Q ⟧
            ⟹ loc_correct (ACond P b c1 c2) Q"
| While: "⟦ P ∩ b ⊆ pre c; P ∩ (- b) ⊆ Q; loc_correct c P ⟧
            ⟹ loc_correct (AWhile P b c) Q"

subsection ‹Interference freedom›

text ‹An assertion @{term r} of one thread is stable under a foreign atomic
  action @{term "(P,a)"}.›

definition if_pair :: "'s set ⇒ ('s set × 'act) ⇒ bool" where
  "if_pair r pa ⟷ (∀s s'. s ∈ r ∩ fst pa ⟶ astep (snd pa) s s' ⟶ s' ∈ r)"

text ‹Each thread's assertions (incl. its postcondition) survive every other
  thread's atomic actions.›

definition interference_free ::
  "(('act,'s) ann × 's set) list ⇒ bool" where
  "interference_free Ts ⟷
     (∀i < length Ts. ∀j < length Ts. i ≠ j ⟶
        (∀r ∈ insert (snd (Ts!j)) (assertions (fst (Ts!j))).
           ∀pa ∈ atomics (fst (Ts!i)). if_pair r pa))"

subsection ‹The Owicki-Gries judgement for a thread vector›

definition og_parallel :: "(('act,'s) ann × 's set) list ⇒ bool" where
  "og_parallel Ts ⟷
     (∀i < length Ts. loc_correct (fst (Ts!i)) (snd (Ts!i)))
     ∧ interference_free Ts"

definition og_pre :: "(('act,'s) ann × 's set) list ⇒ 's set" where
  "og_pre Ts = (⋂i ∈ {..< length Ts}. pre (fst (Ts!i)))"

definition og_post :: "(('act,'s) ann × 's set) list ⇒ 's set" where
  "og_post Ts = (⋂i ∈ {..< length Ts}. snd (Ts!i))"


section ‹Annotated interleaving semantics (for the safety invariant)›

text ‹The same interleaving as @{const par_step}, but over annotated outlines,
  so a reachable configuration still carries each thread's current @{const pre}.›

inductive ann_step ::
  "('act,'s) ann × 's ⇒ ('act,'s) ann × 's ⇒ bool"
where
  ABasic:  "astep a s s' ⟹ ann_step (ABasic P a, s) (ASkip UNIV, s')"
| AComp1:  "ann_step (c1, s) (c1', s') ⟹ ann_step (AComp c1 c2, s) (AComp c1' c2, s')"
| AComp2:  "ann_step (AComp (ASkip P) c2, s) (c2, s)"
| ACondT:  "s ∈ b ⟹ ann_step (ACond P b c1 c2, s) (c1, s)"
| ACondF:  "s ∉ b ⟹ ann_step (ACond P b c1 c2, s) (c2, s)"
| AWhileT: "s ∈ b ⟹ ann_step (AWhile P b c, s) (AComp c (AWhile P b c), s)"
| AWhileF: "s ∉ b ⟹ ann_step (AWhile P b c, s) (ASkip UNIV, s)"

inductive ann_par_step ::
  "(('act,'s) ann list × 's) ⇒ (('act,'s) ann list × 's) ⇒ bool"
where
  AnnPar: "⟦ i < length acs; ann_step (acs ! i, s) (c', s') ⟧
             ⟹ ann_par_step (acs, s) (acs[i := c'], s')"

abbreviation ann_par_steps ::
  "(('act,'s) ann list × 's) ⇒ (('act,'s) ann list × 's) ⇒ bool"
  where "ann_par_steps ≡ ann_par_step⇧*⇧*"


section ‹Soundness›

subsection ‹Safety: the assertion network is an inductive invariant›

text ‹The reusable result Ownership/UAF consumes: from a state in the
  precondition, every reachable configuration satisfies every thread's current
  precondition.  This is the formal counterpart of "the logic gets stuck before
  witnessing the UAF".›

theorem og_safety:
  assumes "og_parallel Ts"
      and "s ∈ og_pre Ts"
      and "ann_par_steps (map fst Ts, s) (acs, s')"
  shows "∀i < length acs. s' ∈ pre (acs ! i)"
  sorry  \<comment> ‹WIP — induction on @{thm[source] rtranclp.induct}; local correctness
            re-establishes thread @{text i}, interference freedom preserves the
            others.  See docs/W1 §4.3.›

subsection ‹Partial correctness (corollary)›

theorem og_sound:
  assumes "og_parallel Ts"
  shows "∀s ∈ og_pre Ts. ∀s'.
           par_steps (map (strip ∘ fst) Ts, s) (replicate (length Ts) Skip, s')
             ⟶ s' ∈ og_post Ts"
  sorry  \<comment> ‹WIP — corollary of @{thm og_safety}.›

end  \<comment> ‹@{locale transition_system}›

end
