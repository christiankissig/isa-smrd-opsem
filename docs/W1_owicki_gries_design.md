# W1 — Generic Owicki-Gries + Ownership (Track A, first AFP target)

**Status:** ✅ **complete (2026-06-09)** — all proofs discharged; `OwickiGries` and
`Ownership` build with **zero `sorry` and without `quick_and_dirty`** (the AFP gate).
Verification session `Track_A` (`TrackA/ROOT`) builds both together in ~3s; standalone
per-entry ROOTs (`OwickiGries/ROOT`, `Ownership/ROOT`) retained for the two-entry AFP split.

Three skeleton corrections were required during the proof phase (each a real soundness/type
fix, not a workaround):
1. **`OwickiGries` post-erasure.** `ann_step` erased postconditions to `ASkip UNIV` (in the
   `ABasic`/`AWhileF` rules), making the safety invariant non-inductive. Fixed by carrying the
   post: `ABasic "'s set" 'act "'s set"` steps to `ASkip post`, and `AWhileF` to `ASkip (P ∩ -b)`
   with that exit assertion recorded in `assertions` (so interference-freedom covers it).
2. **`owned_outline` type.** Declared `'p ⇒ ann ⇒ bool` but used with a postcondition argument;
   corrected to `'p ⇒ ann ⇒ 's set ⇒ bool`.
3. **OG-index ↔ ownership-process bridge.** `ownership_interference_free` conflated the OG thread
   index (`nat`) with the process tag (`'p`). It now takes an explicit injective index→process
   map `proc :: nat ⇒ 'p` plus the well-tagging discipline (thread `i`'s atoms carry `proc i`);
   the RCU client supplies `proc`.

Original design follows.
**Scope:** REWORK_PLAN.md §1 (the independent OG+Ownership vertical), §3 (AFP
requirements + decoupling), Decision 7, Phase 5, Risk 6.

This document specifies a **generic Owicki-Gries / rely-guarantee program logic** over an
**abstract transition system**, with **Ownership** as a concrete instantiation, packaged so it
can be the project's **first AFP submission** — *independent of the Episodic `OpSem`* and of
everything else in this repository. It depends only on HOL.

The two skeleton theories are:

- `OwickiGries/OwickiGries.thy` — `imports Main`. The abstract transition-system locale, the
  command language, interleaving semantics, OG proof outlines, interference freedom, and the
  soundness/safety theorem *statements*.
- `Ownership/Ownership.thy` — `imports OwickiGries`. The ownership predicate, transfer
  discipline, exclusivity invariant, the "ownership discharges interference-freedom" lemma,
  and the use-after-free safety corollary.

> **Dependency note.** "Independent / HOL-only" means *no Track-B / project dependency*
> (`Core`/`MemSem`/`EventStruct`/`OpSem`/`c11_opsem`/SEFM). `Ownership` imports its sibling
> `OwickiGries` — they form one tightly-coupled AFP entry (Decision 7: "`Ownership` as an
> implementation of `OwickiGries`"). `OwickiGries` itself imports only `Main`.

---

## 1. Design goals and the two-horned constraint (Risk 6)

The interface must be simultaneously:

- **(a) weak enough to be sound generically** — soundness is proved once against the
  framework's *own* standard interleaving semantics, with no assumption tying it to weak
  memory or to the Episodic stack; and
- **(b) rich enough that the Episodic `OpSem` `step` relation interprets it cleanly** later
  (Phase 6, RCU client), so the RCU no-UAF proof reuses this entry by *interpretation*, not by
  reopening it.

The single decision that satisfies both is: **the atomic step is an arbitrary binary relation
over a fully abstract state type** —

```
astep :: 'act ⇒ 's ⇒ 's ⇒ bool
```

with **no** assumption of totality, determinism, or enabledness. This matters because the
Episodic `OpSem` step is

- **non-deterministic** (a read may read from several writes),
- **partial / guarded** (an action fires only when it lies in `horizonΦ_H`), and
- **history-dependent** (enabledness depends on `H`).

All three are accommodated by letting `'s` be the *whole* configuration `(σ, ρ, H)` and letting
`astep` be a guarded relation that may simply have no successor when an action is not enabled.
Crucially the framework must **never** assume `astep` is a function or is always enabled — the
skeleton's local-correctness and soundness statements are therefore *partial-correctness*
shaped (`∀ s'. astep a s s' ⟶ …`), which is vacuously fine for blocked actions. This is the
concrete content of the Risk-6 freeze.

---

## 2. The abstract transition-system locale and interleaving semantics

### 2.1 Locale

```isabelle
locale transition_system =
  fixes astep :: "'act ⇒ 's ⇒ 's ⇒ bool"
```

`'act` is an abstract atomic-action type; `'s` an abstract state. Everything below lives in
this locale's context, so all semantics are relative to `astep`.

### 2.2 Command language (parameterised by `'act`, `'s`)

A small structured language; **basic statements are abstract atomic actions**, guards are state
predicates (`'s set`, the shallow-assertion convention):

```isabelle
datatype ('act,'s) com =
    Atom 'act
  | Skip
  | Seq  "('act,'s) com" "('act,'s) com"
  | Cond "'s set" "('act,'s) com" "('act,'s) com"
  | While "'s set" "('act,'s) com"
```

### 2.3 Sequential and parallel small-step semantics

`seq_step :: ('act,'s) com × 's ⇒ ('act,'s) com × 's ⇒ bool` reduces one thread; the only rule
that consults the locale parameter is `Atom`:

```
astep a s s' ⟹ seq_step (Atom a, s) (Skip, s')
```

(plus the standard `Seq`/`Cond`/`While` congruence/branch rules; a thread is *terminated* when
its command is `Skip`).

`par_step :: (('act,'s) com list × 's) ⇒ … ⇒ bool` is the standard interleaving: pick a thread
index `i`, reduce it, write the residual back:

```
i < length cs ⟹ seq_step (cs!i, s) (c', s') ⟹ par_step (cs, s) (cs[i:=c'], s')
```

`par_steps = par_step⇧*⇧*`. This is the *standard interleaving semantics* the AFP entry proves
soundness against (§3 requirement).

---

## 3. OG assertion language, proof outlines, interference freedom

Assertions are **shallow**: `'s assn = 's set` (an assertion is the set of states satisfying
it). This keeps the logic HOL-only and lets assertions refer to *any* component of `'s` —
including the history `H` once `OpSem` is plugged in (needed for the rcu-exit/horizon
reasoning).

### 3.1 Annotated commands (proof outlines)

An OG proof is a **proof outline**: a command annotated with the assertion holding *before*
each node.

```isabelle
datatype ('act,'s) ann =
    ABasic "'s set" 'act                                  -- {P} a
  | ASkip  "'s set"                                        -- {P} skip
  | AComp  "('act,'s) ann" "('act,'s) ann"                -- c1 ; c2
  | ACond  "'s set" "'s set" "('act,'s) ann" "('act,'s) ann"  -- {P} if b then c1 else c2
  | AWhile "'s set" "'s set" "('act,'s) ann"              -- {P=inv} while b do c
```

Helper functions (all `primrec`):

- `pre c` — the head assertion of an outline node.
- `strip c` — the underlying `com` (erases assertions).
- `assertions c` — the set of *all* assertions occurring in `c`.
- `atomics c` — the set of `(local-precondition, action)` pairs of every `ABasic` in `c`.

### 3.2 Local correctness (sequential Hoare, partial)

`loc_correct :: ('act,'s) ann ⇒ 's set ⇒ bool` — `loc_correct c Q` says outline `c` is a valid
sequential proof with postcondition `Q`. The atomic rule is the partial-correctness shape that
tolerates blocked/non-deterministic `astep`:

```
(⋀s s'. s ∈ P ⟹ astep a s s' ⟹ s' ∈ Q) ⟹ loc_correct (ABasic P a) Q
```

with the standard `Skip` (`P ⊆ Q`), `Comp`, `Cond`, and `While` (invariant) rules.

### 3.3 Interference freedom

The defining OG side condition. An atomic action `(P,a)` of one thread must not falsify any
assertion `r` of another thread:

```isabelle
definition if_pair :: "'s set ⇒ ('s set × 'act) ⇒ bool" where
  "if_pair r (P,a) ⟷ (∀s s'. s ∈ r ∩ P ⟶ astep a s s' ⟶ s' ∈ r)"
```

For a vector of thread outlines with their postconditions `Ts :: (('act,'s) ann × 's set)
list`:

```isabelle
definition interference_free Ts ⟷
  (∀i<length Ts. ∀j<length Ts. i ≠ j ⟶
     (∀r ∈ assertions (fst (Ts!j)) ∪ {snd (Ts!j)}.
        ∀pa ∈ atomics (fst (Ts!i)). if_pair r pa))"
```

### 3.4 The OG proof judgement

```isabelle
definition og_parallel Ts ⟷
  (∀i<length Ts. loc_correct (fst (Ts!i)) (snd (Ts!i))) ∧ interference_free Ts
```

with `og_pre Ts = (⋂i<length Ts. pre (fst (Ts!i)))` and
`og_post Ts = (⋂i<length Ts. snd (Ts!i))`.

---

## 4. Soundness and the reusable safety invariant

Two theorems. The **safety invariant** is the one Ownership/UAF actually consumes; partial
correctness is the headline corollary.

To state the invariant we step the *annotated* outlines (`ann_step`, `ann_par_step`,
`ann_par_steps = ann_par_step⇧*⇧*`) — identical to §2.3 but over `ann`, so a reachable
configuration still carries each thread's *current* outline node and hence its `pre`.

### 4.1 Safety (assertion network is an inductive invariant)

```isabelle
theorem og_safety:
  assumes "og_parallel Ts"
      and "s ∈ og_pre Ts"
      and "ann_par_steps (map fst Ts, s) (acs, s')"
  shows "∀i < length acs. s' ∈ pre (acs ! i)"
```

In words: from a state in the precondition, **every reachable configuration has every thread's
current precondition satisfied**. This is exactly "the logic never reaches a state where a
node's assertion is false" — the formal counterpart of the paper's *"the logic gets stuck
before witnessing the UAF."*

### 4.2 Partial correctness (corollary)

```isabelle
theorem og_sound:
  assumes "og_parallel Ts"
  shows "∀s ∈ og_pre Ts. ∀s'.
           par_steps (map (strip ∘ fst) Ts, s) (replicate (length Ts) Skip, s')
             ⟶ s' ∈ og_post Ts"
```

### 4.3 Proof sketch (for when proofs are discharged)

- `og_safety` by induction on `ann_par_steps`. Base: `s ∈ og_pre Ts ⟹` each `pre` holds.
  Step: a reduction in thread `i` (i) re-establishes thread `i`'s next `pre` by
  `loc_correct` (local correctness), and (ii) preserves thread `j≠i`'s `pre` by
  `interference_free` (every reachable node-assertion of `j` is in `assertions (fst (Ts!j))`,
  and the firing action of `i` is in `atomics (fst (Ts!i))`). A small lemma "every reachable
  `ann` node's `pre` is in the original `assertions` set, and stepping a `loc_correct` outline
  keeps it `loc_correct`" closes the bookkeeping.
- `og_sound` from `og_safety` plus the fact that a fully-terminated config's per-thread `pre`
  for `ASkip` nodes is the postcondition.

These mirror the AFP `Hoare-Parallel` (Prensa Nieto) development; the only novelty is the
*abstract, relational, possibly-blocking* `astep`, which is why every obligation is in
partial-correctness `∀s'. astep … ⟶ …` form.

---

## 5. Ownership as an instantiation

`Ownership.thy` (`imports OwickiGries`) is the showcase implementation: ownership discipline
*discharges interference freedom generically*, and yields UAF safety.

### 5.1 Ownership state and predicate

Actions are tagged with the acting process; resources have a type `'r`:

```isabelle
locale ownership_system =
  transition_system astep
    for astep :: "('p × 'act) ⇒ 's ⇒ 's ⇒ bool" +
  fixes owns      :: "'s ⇒ 'p ⇒ 'r set"     -- resources owned by a process in a state
    and acquires :: "'act ⇒ 'r set"          -- footprint: resources the action takes
    and releases :: "'act ⇒ 'r set"          -- footprint: resources the action relinquishes
  assumes ...transfer discipline...
```

The paper's `t ∈ own(s)` is `s_state ∈ Owns t s`:

```isabelle
definition Owns    p r = {s. r ∈ owns s p}
definition NotOwns p r = {s. r ∉ owns s p}
```

### 5.2 Transfer discipline (locale assumptions)

The discipline encodes the paper's rules ("threads instantly assume ownership of newly
allocated `n`; read-ownership after reading `C`; relinquish at rcu-exit / `free`"):

1. **Locality** — an action by `p` changes only `p`'s ownership:
   `astep (p,a) s s' ⟹ q ≠ p ⟹ owns s' q = owns s q`.
2. **Footprint** — `astep (p,a) s s' ⟹ owns s' p = (owns s p ∪ acquires a) − releases a`.
3. **Fresh acquisition** — you cannot acquire a resource currently owned by anyone:
   `astep (p,a) s s' ⟹ r ∈ acquires a ⟹ r ∉ owns s q` (for all `q`).

(Assumption 3 abstracts "allocated memory is distinct by freezing" and the rule that a thread
takes ownership only after others relinquish — the paper's deref/free sequencing.)

### 5.3 Exclusivity invariant

```isabelle
definition exclusive s ⟷ (∀p q r. r ∈ owns s p ⟶ r ∈ owns s q ⟶ p = q)

lemma exclusive_step:  "exclusive s ⟹ astep (p,a) s s' ⟹ exclusive s'"
lemma exclusive_reach: "exclusive s ⟹ (astep-reachable s s') ⟹ exclusive s'"
```

### 5.4 Ownership discharges interference freedom (the reusable lemma)

Because a foreign action (`q ≠ p`) leaves `owns _ p` untouched (Locality), ownership
assertions *tagged to another thread* are automatically stable — no `astep`-specific reasoning
needed:

```isabelle
lemma foreign_preserves_Owns:
  "q ≠ p ⟹ astep (q,a) s s' ⟹ s ∈ Owns p r ⟹ s' ∈ Owns p r"
lemma foreign_preserves_NotOwns:
  "q ≠ p ⟹ astep (q,a) s s' ⟹ s ∈ NotOwns p r ⟹ s' ∈ NotOwns p r"
```

Lifted to the OG obligation: if every assertion of thread `j`'s outline is an ownership
assertion tagged to `j` (a conjunction of `Owns j _ / NotOwns j _`), then `interference_free`
holds *by construction*:

```isabelle
lemma ownership_interference_free:
  assumes "⋀j. j<length Ts ⟹ ownership_assertions_of j (fst (Ts!j))"
  shows   "interference_free Ts"
```

This is the AFP entry's selling point: **ownership disjointness ⟹ OG non-interference**,
proved once.

### 5.5 The paper's Hoare rules as instances

The rules from `example-uaf-bug-opsem.tex` become `loc_correct`/`if_pair` facts under the
discipline:

| paper rule | as a skeleton fact |
|---|---|
| `own:free`  `{∀t≠t1. t∉own(s)} t1:free(s) {}` | `loc_correct (ABasic (⋂t≠t1. NotOwns t s) (t1, Free s)) UNIV` |
| `own:deref` `{t2∈own(s)} t2:v:=*s {}`          | precondition `Owns t2 s` required by `loc_correct` |
| `rcu-exit`  `{} t2:rcu[t2]:=⁰ {t2∉own(s)}`     | `releases (RcuExit t2) = {s}`, post `NotOwns t2 s` |
| `free`      `{t1∈own(s)} t1:free(s) {t1∉own(s)}` | `releases (Free s) = {s}` |
| fadd post   `{} t2:s:=fadd(&C,0) {t2∈own(s)}`   | `acquires (Fadd …) = {s}`, post `Owns t2 s` |

### 5.6 UAF-safety corollary

Set up the fixed program's two relevant outlines: `t1` reaching `free(s)` with precondition
`NotOwns t2 s`, and `t2` reaching `deref(s)` with precondition `Owns t2 s`. By `og_safety`,
every reachable configuration satisfies both threads' current preconditions; a configuration
co-enabling `free(s)` (so `NotOwns t2 s`) and a *still-pending* `deref(s)` (so `Owns t2 s`) is
contradictory:

```isabelle
theorem uaf_safe:
  assumes "og_parallel Ts"                       -- the RCU outline is OG-provable (via §5.4)
      and "pre (free-node  of t1) ⊆ NotOwns t2 s"
      and "pre (deref-node of t2) ⊆ Owns t2 s"
      and "ann_par_steps (map fst Ts, s0) (acs, s')"
      and "s0 ∈ og_pre Ts"
      and "t1-at-free acs ∧ t2-at-deref acs"     -- the racy configuration
  shows  False
```

i.e. the buggy co-enabling is **unreachable**; the logic is stuck before witnessing the UAF,
matching the paper's lightning-rule contradiction `t2∈own(s)` vs `t2∉own(s)`.

---

## 6. How the Episodic `OpSem` plugs in later (Phase 6 — interface check)

This is the Risk-6 paper-exercise interpretation, recorded so the locale is frozen correctly
*before* AFP submission. It is **not** part of the AFP entry — it lives in `clients/RCU`.

Instantiate the locale:

| OG abstract | Episodic `OpSem` |
|---|---|
| `'s` | the configuration `(σ, ρ, H)` |
| `'act` | a labelled atomic action `(tid, action)` (or `(p, action)`) |
| `astep (t,a) (σ,ρ,H) (σ',ρ',H')` | `OpSem` single-action step: `a` emitted by `t`, **guarded by `a ∈ horizonΦ_H`**, with MemSem effect `σ ⤳_t σ'` and `H' = H ∪ {t:a}` |
| `owns (σ,ρ,H) t` | the RCU ownership map read off `(σ,H)` (allocated/read/released resources of `t`) |

Why the interface fits:

- `astep` being a **relation** absorbs non-determinism (multiple `viswrite` reads).
- `astep` being **partial** absorbs the horizon guard: actions not in `horizonΦ_H` simply have
  no `astep` successor — and partial-correctness obligations are vacuous there.
- `'s` carrying `H` lets both `astep`'s guard *and* assertions mention history — required for
  the rcu-exit reasoning (`(t2:rcu[t2]:=0) ∉ horizonΦ^fix_{H_0}`).

The one **proof obligation at the seam** (Phase 6, not now): the OG interleaving semantics over
the RCU thread outlines *agrees with* the `OpSem` `step` relation — i.e. each `OpSem` `step`
emits exactly one thread's one atomic action, so `par_step` and `step prog Φ` coincide on the
RCU program. This is the riskiest decoupling assumption (see §7).

---

## 7. Riskiest part of the decoupling

The abstract `astep` and the OG interleaving semantics are easy to keep HOL-only. The genuine
risk is the **granularity / scheduling match** at the future interpretation seam (§6):

> The OG framework *generates* interleaving from per-thread command structure and assumes each
> atomic step is **one thread's one action**. The Episodic `OpSem` `step prog Φ` instead bundles
> *scheduling + horizon enabling + action effect* into a single whole-program relation, and a
> multi-event instruction (CAS = R;Branch;W, FAA = R;W) emits an **action sequence**, not one
> action.

If a CAS must be a *single* OG atomic node (to make the ownership transfer atomic) but `OpSem`
exposes it as three horizon-steps, the `par_step ≈ step` agreement lemma in §6 needs a
coarser-grained `astep` (one OG `Atom` = the whole instruction's action sequence). The
mitigation is to **bake instruction-granularity atomicity into `'act`** now: let an abstract
`astep a s s'` denote the effect of a *whole instruction's* action sequence (matching the
paper's `(l:ā) ∈ horizonΦ_H`, one label `l`, action sequence `ā`). Then `'act` = an instruction
label, `astep` = "run this instruction's emitted actions, if all enabled." This keeps the OG
entry oblivious to sub-events while letting `OpSem` discharge the seam lemma at instruction
granularity. **Freeze `'act` at instruction (not event) granularity** — that is the single
decision that de-risks the eventual interpretation without touching the submitted AFP entry.

Everything else (assertions as `'s set`, relational/partial `astep`, the standard interleaving
semantics, OG soundness) is squarely HOL-only and submittable on its own.
