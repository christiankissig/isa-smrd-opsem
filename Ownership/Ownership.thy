(*  Title:      Ownership/Ownership.thy
    Author:     RCU-C11-OpSem project (Track A, first AFP target)

    Ownership as a concrete IMPLEMENTATION of the generic Owicki-Gries
    framework (OwickiGries.thy).  An ownership predicate over an abstract
    transition system, a transfer discipline, the exclusivity invariant, the
    "ownership discharges interference-freedom" lemma, and a use-after-free
    safety corollary reproducing the paper's reasoning
    (rcu-c11-paper/example-uaf-bug-opsem.tex).

    Its ONLY dependency is the sibling OwickiGries entry (no Core/MemSem/
    EventStruct/OpSem/c11_opsem/SEFM).  Together they form the first AFP
    submission.  See docs/W1_owicki_gries_design.md, REWORK_PLAN.md (Decision 7,
    Phase 5, Risk 6).

    WIP: all proofs are `sorry`'d.  This file fixes the locale interface and the
    theorem STATEMENTS.
*)

theory Ownership
  imports OwickiGries
begin

section ‹The ownership-system locale›

text ‹Atomic actions are tagged with the acting process @{typ 'p}; resources
  have type @{typ 'r}.  The state @{typ 's} carries an ownership map
  @{term owns}.  Each (untagged) action declares an ownership footprint via
  @{term acquires} / @{term releases}.

  The transfer discipline (the three assumptions below) encodes the paper:
  threads instantly assume ownership of freshly allocated resources, gain
  ownership after reading the shared structure, and relinquish it at the
  rcu-exit / @{text free}.›

locale ownership_system =
  transition_system astep
    for astep :: "('p × 'act) ⇒ 's ⇒ 's ⇒ bool" +
  fixes owns     :: "'s ⇒ 'p ⇒ 'r set"
    and acquires :: "'act ⇒ 'r set"
    and releases :: "'act ⇒ 'r set"
  assumes
      \<comment> ‹Locality: an action by @{text p} changes only @{text p}'s ownership.›
      locality:    "⟦ astep (p, a) s s'; q ≠ p ⟧ ⟹ owns s' q = owns s q"
  and \<comment> ‹Footprint: @{text p}'s ownership evolves exactly by its footprint.›
      footprint:   "astep (p, a) s s' ⟹ owns s' p = (owns s p ∪ acquires a) - releases a"
  and \<comment> ‹Fresh acquisition: cannot acquire a resource currently owned by
        anyone (abstracts freezing/distinctness and the deref/free sequencing).›
      fresh_acq:   "⟦ astep (p, a) s s'; r ∈ acquires a ⟧ ⟹ r ∉ owns s q"
begin

section ‹The ownership predicate (the paper's @{text "t ∈ own(s)"})›

definition Owns :: "'p ⇒ 'r ⇒ 's set" where
  "Owns p r = {s. r ∈ owns s p}"

definition NotOwns :: "'p ⇒ 'r ⇒ 's set" where
  "NotOwns p r = {s. r ∉ owns s p}"

lemma NotOwns_compl: "NotOwns p r = - Owns p r"
  by (auto simp: Owns_def NotOwns_def)


section ‹Exclusivity invariant›

definition exclusive :: "'s ⇒ bool" where
  "exclusive s ⟷ (∀p q r. r ∈ owns s p ⟶ r ∈ owns s q ⟶ p = q)"

lemma exclusive_step:
  assumes "exclusive s" and "astep (p, a) s s'"
  shows   "exclusive s'"
  sorry  \<comment> ‹WIP — by @{thm locality} @{thm footprint} @{thm fresh_acq}.›

lemma exclusive_reach:
  assumes "exclusive s"
      and "(λs s'. ∃p a. astep (p, a) s s')⇧*⇧* s s'"
  shows   "exclusive s'"
  sorry  \<comment> ‹WIP — induction using @{thm exclusive_step}.›


section ‹Ownership discharges interference freedom›

text ‹The crux: a foreign action (@{text "q ≠ p"}) leaves @{text "owns s p"}
  untouched, so ownership assertions tagged to another thread are automatically
  stable — no @{term astep}-specific reasoning needed.›

lemma foreign_preserves_Owns:
  assumes "q ≠ p" and "astep (q, a) s s'" and "s ∈ Owns p r"
  shows   "s' ∈ Owns p r"
  sorry  \<comment> ‹WIP — by @{thm locality}.›

lemma foreign_preserves_NotOwns:
  assumes "q ≠ p" and "astep (q, a) s s'" and "s ∈ NotOwns p r"
  shows   "s' ∈ NotOwns p r"
  sorry  \<comment> ‹WIP — by @{thm locality}.›

text ‹An assertion is @{emph ‹owned by›} @{text p} if it is stable under every
  action of every other process.  @{const Owns} and @{const NotOwns} of @{text
  p} qualify (above).›

definition own_stable :: "'p ⇒ 's set ⇒ bool" where
  "own_stable p r ⟷
     (∀q a s s'. q ≠ p ⟶ astep (q, a) s s' ⟶ s ∈ r ⟶ s' ∈ r)"

lemma Owns_own_stable:    "own_stable p (Owns p r)"
  sorry  \<comment> ‹WIP — by @{thm own_stable_def} and @{thm foreign_preserves_Owns}.›

lemma NotOwns_own_stable: "own_stable p (NotOwns p r)"
  sorry  \<comment> ‹WIP — by @{thm own_stable_def} and @{thm foreign_preserves_NotOwns}.›

text ‹If every assertion of thread @{text j}'s outline is owned by @{text j},
  then the Owicki-Gries interference-freedom obligation holds by construction.
  This is the reusable "ownership disjointness ⟹ non-interference".›

definition owned_outline ::
  "'p ⇒ ('p × 'act, 's) ann ⇒ bool" where
  "owned_outline j c Q ⟷ (∀r ∈ insert Q (assertions c). own_stable j r)"

lemma ownership_interference_free:
  assumes "⋀j. j < length Ts ⟹ owned_outline j (fst (Ts!j)) (snd (Ts!j))"
  shows   "interference_free Ts"
  sorry  \<comment> ‹WIP — unfold @{thm interference_free_def} @{thm if_pair_def}; each
            foreign atomic action is some @{term "astep (q,a)"} with @{text
            "q ≠ j"}, and @{thm own_stable_def} closes it.›


section ‹Use-after-free safety (the paper's corollary)›

text ‹The paper's Hoare rules instantiate as follows (informally; the concrete
  RCU program is supplied by the client in Phase 6):

  \<^item> rcu-exit  @{text "{} t2: rcu[t2]:=⇧rel 0 {t2 ∉ own(s)}"} :
                @{text "s ∈ releases a"}, post @{term "NotOwns t2 s"};
  \<^item> free      @{text "{t1 ∈ own(s)} t1: free(s) {t1 ∉ own(s)}"} :
                @{text "s ∈ releases a"}, with precondition @{term "NotOwns t2 s"}
                for the safe-to-free side condition;
  \<^item> deref     @{text "{t2 ∈ own(s)} t2: v:=*s {}"} :
                precondition @{term "Owns t2 s"}.

  The UAF would co-enable @{text "free(s)"} (so @{term "NotOwns t2 s"}) with a
  still-pending @{text "deref(s)"} (so @{term "Owns t2 s"}); by @{thm og_safety}
  both threads' current preconditions hold at every reachable configuration, so
  the racy configuration is contradictory — the logic is stuck before
  witnessing the UAF.›

theorem uaf_safe:
  fixes Ts :: "(('p × 'act, 's) ann × 's set) list"
  assumes og:    "og_parallel Ts"
      and start: "s0 ∈ og_pre Ts"
      and run:   "ann_par_steps (map fst Ts, s0) (acs, s')"
      and i1:    "i1 < length acs" and i2: "i2 < length acs" and "i1 ≠ i2"
      \<comment> ‹thread @{text i1} is about to @{text "free(s)"}; thread @{text i2} is
         about to @{text "deref(s)"}, hence still owns @{text s}:›
      and free_pre:  "pre (acs ! i1) ⊆ NotOwns t2 s"
      and deref_pre: "pre (acs ! i2) ⊆ Owns t2 s"
  shows "False"
  sorry  \<comment> ‹WIP — from @{thm og_safety}: @{term "s' ∈ pre (acs!i1)"} and
            @{term "s' ∈ pre (acs!i2)"}, so @{term "s' ∈ NotOwns t2 s ∩ Owns t2 s"},
            contradiction by @{thm NotOwns_compl}.  The premise @{text og} would
            itself be obtained from @{thm ownership_interference_free}.›

end  \<comment> ‹@{locale ownership_system}›

end
