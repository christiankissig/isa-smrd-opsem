# Spike C — Memory Semantics (MemSem) re-evaluation for SMRD

**Scope.** Decide whether the current RC11/surrey memory model
is the right basis for an SMRD-faithful `MemSem`, and define what `MemSem` should be.
Answers Q1–Q5 + the fate of `PSem`/`OpSem_definite`.

**Inputs read.** `c11_opsem/OpSem.thy` (surrey model), `MemSem/PSem.thy`,
`MemSem/OpSem_definite.thy`; paper `cas-semantics-and-bug.tex`, `opsem.tex`,
`app-opsem.tex` (§Configurations, action rules), `app-defs.tex`, and the
`rules/actions:{read,write}`, `rules/commands:cas-failure`, `diagrams/cas-semantics`
fragments.

---

## TL;DR — Decision

**Build a new, thin `MemSem` = the paper's program state**
`σ = (viswrite, memory, φ, RF)` with SMRD action effects, and **do NOT** carry over
surrey's RC11 coherence machinery (timestamps / modification-order / monotone
per-thread `thrView` / `visible_writes`-by-timestamp / `modView` release-acquire
view-merge / `covered`). **All ordering — including release/acquire synchronisation —
is delegated to Φ (ppo ∪ DP) in the `EventStruct`/`OpSem` layers, not to MemSem.**

This is a *replacement*, not a relaxation, of surrey. The reusable surface from
surrey is small (the action vocabulary and the *shape* of an action transition
`σ ⤳ₜ σ'`); the substantive content (anything timestamp/mo/view-based) conflicts
with SMRD and is dropped. `PSem` **folds in** as the `memory`/alloc effects;
`OpSem_definite` is **retired**.

**Important correction to the earlier "likely outcome".** The rework plan tentatively proposed
"reusing surrey's release/acquire **and** visible-write machinery where compatible".
This evaluation finds those are exactly the coherence/ordering machinery that must be
dropped: in the paper, acquire/release semantics and visible-write *ordering* are
realised as ppo/DP edges in Φ (e.g. a *release* RCU-exit `ppo`-orders the deref read
before it; an *acquire* failing-CAS does not), so they belong to `EventStruct`, not
`MemSem`. MemSem keeps only a *coherence-free* "last visible write per symbolic
location" map. Memory-order annotations survive **on actions** (as inputs to Φ
construction), but have **no view-merge effect** in MemSem.

---

## Q1 — Does surrey's timestamp-mo + visible_writes thread-view exclude the SMRD-admitted UAF reorder?  **Yes — surrey is RC11-too-strong.**

Surrey (`OpSem.thy`) is an operational presentation of the RA + coherence (SC-per-location)
fragment of C11. Three mechanisms together hard-wire RC11 coherence:

1. **Total per-location modification order via timestamps.** `mods :: (L×TS) ⇒ write_record`
   with `TS = rat`; `mo w w' ≡ var w = var w' ∧ tst w < tst w'` (`OpSem.thy:504`).
   Every write to a location is totally ordered.
2. **Monotone per-thread, per-location view.** `thrView :: T ⇒ L ⇒ (L×TS)` and
   `visible_writes σ t x = {w ∈ writes_on σ x. tst(thrView σ t x) ≤ tst w}`
   (`OpSem.thy:92`). A thread may only read writes at or after its current view
   timestamp, and a read **advances** that view: `read_trans` sets
   `thrView σ t (var w) := w` (`OpSem.thy:135`). This is exactly CoRR/CoWR
   coherence-per-location: once a thread observes a write it can never read an older one.
3. **Operational interleaving executes each thread in program order**, so each thread's
   accesses are emitted po-respecting and pinned by the monotone view above.

Consequently surrey **cannot** produce the SMRD-admitted execution. The UAF requires the
deref read `v := *s` to take effect *below* the failing CAS / RCU-exit in the same thread
(load→store reorder; `cas-semantics-and-bug.tex`, Fig. uaf-bug-oota-cycle-smrd). Surrey
has no representation of "this earlier-in-po read happened after a later-in-po write of
the same thread": the read advances `thrView` at its po-position and the model keeps a
po-ordered, coherent per-thread view. SMRD relaxes precisely the coherence axiom (it
forbids thin-air cycles only in `ppo ∪ DP ∪ rf`, not in `po ∪ rf`), which is what admits
the reorder. Surrey forbids it. **Verdict: surrey enforces RC11 coherence structurally
and must be replaced, not patched.**

(There is no localized "relaxation knob": coherence in surrey is the *meaning* of
`thrView`/`tst`/`mo`, not a side axiom. Relaxing it would dismantle the model.)

## Q2 — Is the paper's thin σ = (viswrite, memory, φ, RF) the right MemSem?  **Yes.**

From `app-opsem.tex` (Def. Program States) the program state has exactly four parts and
**no timestamps, no mo, no per-thread coherent views**:

| component | type / role | action effect |
|---|---|---|
| `viswrite` | `Expr_A × Expr_B ⇀ Writes` — last visible write per symbolic location `x` modulo `φ` | write: `viswrite := viswrite(x ↦ a)` (`actions:write`) |
| `memory` | `Set(Symbols)` — allocated symbolic locations | alloc: add symbol + conjoin disjointness into `φ`; dealloc: remove |
| `φ` | path predicate: branch decisions ∧ alloc-disjointness ∧ rf value-equalities (`φ_RF`) | read: `φ := φ ∧ (α = val(viswrite(x)))`; branch: conjoin condition |
| `RF` | `(Labels×Reads×Threads) × Writes` read-from relation | read: `RF := RF ∪ {(a, viswrite(x))}` (`actions:read`) |

Ordering is **absent by design** — the paper states the opsem "does not impose RC11
coherence/mo; ordering is delegated to Φ", and the future-stepping rules
(`step:non-lb_non-branch`, `step:lb`, `step:branch`) only ever advance along
`horizonΦ_H` (next ppo/DP-enabled actions). So coherence/ordering correctness is an
`EventStruct`/`OpSem` property, and MemSem is just a symbolic store + constraint
accumulator. This σ is the right MemSem; surrey's coherence apparatus is unnecessary in
the opsem and actively wrong for SMRD (Q1).

Two practical notes from `app-opsem.tex` that MemSem's types must accommodate:
`viswrite`/`φ`/`RF` carry **loop-iteration indices** (so the `lb` rule can reset
this-thread, this-loop terms `|^t_{∖ℓ}`); and `viswrite(x)` is resolved **modulo `φ`**
(`x ≡_φ x'`), i.e. symbolic-location equivalence, not syntactic equality.

## Q3 — Reuse boundary: what of surrey survives vs conflicts?

**Reusable (concept/shape, mostly re-derived in `Core`/`MemSem` — not imported):**
- The **action vocabulary** `Read/Write/Update`, generalised: replace the boolean
  `is_releasing`/RA flag with a proper memory-order `o ∈ {rlx, acq, rel}` (paper
  `app-defs.tex` grammar). Lives in `Core`.
- The **transition shape** `σ ⤳ₜ σ'` as a function of an action — keep the pattern,
  replace the body with the thin effects in the Q2 table.
- The **allocation discipline** (see PSem below): `alloc_addrs`/`isfree_addr`/
  `Unique_allocs`/disjointness ↦ MemSem's `memory` + `φ` disjointness.
- The **well-formedness habit** (a `wfs`-style invariant): re-cast as "`viswrite` total
  where defined, `RF` maps each read to a write of `φ`-equal value, `memory` closed",
  not surrey's view/mo well-formedness.

**Conflicts (drop entirely):**
- `TS = rat`, `mods` as `(L×TS)`-indexed total order, `mo`, `lastWr`, `valid_fresh_ts`.
- `thrView`, `modView`, monotone per-location views, `visible_writes` *by timestamp*.
- The **release/acquire view-merge** machinery: `syncing`, `ts_oride`, the `modView`
  override in `read_trans`/`update_trans` (`OpSem.thy:126–146,248–282`). In surrey this
  *implements* RA synchronisation by merging views; in the paper RA synchronisation is a
  ppo fact in Φ. → belongs to `EventStruct`, not MemSem.
- `covered` and mo-based CAS coverage (`OpSem.thy:285–299`).
- The surrey **observation/value-order predicate suite** built on the above —
  `d_obs`/`c_obs`/`p_obs`/`enc`/`p_vorder`/`d_vorder`/`amo`/`no_val`/`last_val`
  (`OpSem.thy:471–552`). These are defined over `lastWr`/`mo`/`tst` and are
  coherence-specific; the Owicki-Gries/ownership assertion language is rebuilt over
  `σ.φ`/`σ.RF`/`memory` instead. (The *names* may reappear; the *definitions* do not port.)

**Net:** of `OpSem.thy`'s ~600 lines, the surviving content is essentially the
action datatype and the "transition driven by an action" idea. The bulk is coherence
machinery that conflicts with SMRD.

## Q4 — Failing CAS = acquire-only.

Paper (`cas-semantics-and-bug.tex` + `rules/commands:cas-{success,failure}`):
CAS is a sequence **R_{o_r}; Branch; (W_{o_w} only on success)**. Success emits
`a_r = Reads_{o_r} x α`, `a_b = Branches(α = ⟦e_s⟧)`, `a_w = Writes_{o_w} x n`
(guard `α ≡_{σ.φ} ⟦e_s⟧`). **Failure emits only `a_r; a_b`** with `r ↦ ⊥` and
`α ≢_{σ.φ} ⟦e_s⟧` — **no write, hence no release** (ISO C11 7.17.7.4). The acquire/release
asymmetry is what permits the load→store reorder below a *failing* CAS that enables the UAF.

Neither current encoding matches:
- Surrey collapses CAS into one monolithic `Update` with `is_releasing` handling on the
  RMW; failure degrades to `read_trans … False` — i.e. surrey's failing CAS is a *relaxed*
  read (`b = False` ⇒ no `syncing`), not an acquire read, and there is no separate Branch
  event. (`OpSem.thy:285–299`.)
- `OpSem_definite`'s `FAAZ` is an RCU-specific fetch-and-add-zero RMW on top of surrey.

**MemSem/OpSem change:** model RMWs as their action sequence (FAA ↦ R;W, CAS ↦
R;Branch;W / R;Branch), each sub-action carrying its own memory order. MemSem just applies
the thin per-action effects (read extends `RF`+`φ`; write funupds `viswrite`); the Branch
conjoins its condition into `φ`. The **acquire-only-ness has no MemSem view effect** — it
manifests only as the *absence* of a release write in the failure case, which in Φ means
no ppo edge orders subsequent same-thread instructions before the CAS. So Q4 is realised
by (a) MemSem splitting RMWs into ordered sub-actions with per-action memory orders, and
(b) `EventStruct` deriving ppo from those orders. The single surrey `Update` with
`is_releasing` is dropped.

## Q5 — Soundness obligation vs the SMRD event structure.

Paper soundness/completeness (`opsem.tex` §Correspondence): every opsem derivation
`prog, Φ ⊢ (σ,ρ,H) → …` corresponds to an SMRD event-structure execution following the
same actions, and conversely (completeness) every complete execution of an episodic-loop
program has a corresponding derivation. Split the obligation by layer:

- **MemSem-local (provable, near-term):** action effects preserve the σ-invariants —
  `viswrite` stays well-defined per symbolic location; every `RF` edge links a read to a
  write whose value equals the read symbol under `φ` (`φ ⊇ φ_RF`); `memory` disjointness is
  reflected in `φ`; satisfiability of `φ` is preserved/monotone (impossible paths pruned).
  These are the only MemSem-level proof duties.
- **EventStruct/OpSem-level (the SMRD agreement, stretch goal):** the thin-air condition —
  acyclicity of `ppo ∪ DP ∪ rf` — is **not** a MemSem property (MemSem imposes no order).
  It holds because `horizonΦ_H` only enables ppo/DP-respecting next actions and `rf` is
  drawn from `σ.viswrite`; thus an exhaustive derivation builds a maximal `ppo∪DP∪rf`-acyclic
  history = an SMRD execution. State as the paper's `opsem-sound`/`opsem-complete`; carry it
  as an `OpSem` stretch goal, with MemSem only discharging the rf/value-consistency lemma it
  depends on.

**Consequence:** because all ordering lives in Φ, MemSem can be proved sound *independently*
of the SMRD-vs-RC11 distinction — the distinction is entirely in how Φ is computed
(mordor, `ppo∪DP` vs `po`). This is the key reason the thin σ is the right MemSem: it makes
the memory layer **memory-model-agnostic**, with SMRD-vs-RC11 a property of Φ alone.

## Fate of PSem / OpSem_definite.

- **`PSem.thy` — FOLD into MemSem.** It is provenance/allocation: `posem` with
  `alloc_addrs`, `isfree_addr`, `Unique_allocs`, `constant_alloc_ass`,
  `allocate_object`/`kill`. This *is* the paper's `σ.memory ⊆ Symbols` + alloc-disjointness
  (folded into `φ`). Re-express as MemSem's `memory` component and the alloc/dealloc action
  effects (`actions:allocate`/`actions:deallocate`). Do not keep as a separate SEFM import;
  drop its surrey coupling. Keep the *ideas* (uniqueness, free-address test), not the file.
- **`OpSem_definite.thy` — RETIRE.** It is built entirely on surrey
  (`surrey_state`, `covered`, `modView`, timestamps): `FAAZ`, `These_writes_releasing`,
  `c_obs_last`, and surrey-coherence observation lemmas. All of it is RC11/coherence-specific
  and conflicts with Q1–Q3. `FAAZ` becomes the generic `faa` command (R;W with mem-orders)
  in `OpSem`; the `c_obs`/`d_obs` reasoning is replaced by the φ/RF-based ownership assertion
  language. Nothing ports verbatim. (It also currently contains `sorry`s, so it is not an AFP
  asset.) Move out of `MemSem/`; do not import.

---

## Concrete: Build vs Reuse vs Drop

**BUILD (new in `Core` + `MemSem`):**
- `Core`: memory-order type `{rlx, acq, rel}`; locations/symbols; values; symbolic
  expressions `Expr_A`/`Expr_B`; action datatype `Read_o / Write_o / Branch / Alloc /
  Dealloc / Fence` over symbolic locations (the level Φ/H build on).
- `MemSem`: program-state record `σ = ⟨viswrite, memory, φ, RF⟩` (with iteration indices on
  `viswrite`/`φ`/`RF` per `app-opsem.tex`); `viswrite(x)` resolution modulo `φ`
  (`x ≡_φ x'`); per-action effect `σ ⤳ₜ σ'` for read/write/alloc/dealloc/branch/fence
  exactly per the paper rules; initial σ (`viswrite`,`memory` empty, `φ = ⊤`); MemSem
  well-formedness invariant + its preservation lemmas (Q5-local).
- RMW sub-action sequencing for FAA (R;W) and CAS (R;Branch;W / R;Branch, acquire-only
  failure) — Q4.

**REUSE (concept/shape only; re-derive, do not import surrey/SEFM):**
- Action-datatype skeleton and the "transition driven by an action" pattern from surrey.
- PSem's allocation discipline (unique allocs, free-address test, disjointness) → MemSem
  `memory` + `φ`.

**DROP (RC11 coherence — conflicts with SMRD):**
- Surrey: `TS`/`mods`/`mo`/`lastWr`/`valid_fresh_ts`; `thrView`/`modView`/`visible_writes`
  (timestamp views); `syncing`/`ts_oride` RA view-merge; `covered` + mo-based CAS;
  the `d_obs`/`c_obs`/`p_obs`/`enc`/`p_vorder`/`d_vorder`/`amo`/`no_val`/`last_val` suite.
- `OpSem_definite.thy` wholesale (retire). `PSem.thy` as a standalone import (fold).
- The `c11_opsem` surrey submodule as a dependency of MemSem.

**RECONSIDER vs the plan's wording:** "reuse surrey's release/acquire and visible-write
machinery" → these are coherence/ordering and move to `EventStruct` (Φ), not MemSem.
Memory orders stay on actions; their *synchronisation effect* is a ppo fact, not a σ update.
