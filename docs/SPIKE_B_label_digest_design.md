# Spike B — Core label/digest interface freeze

**Status:** proposed freeze, 2026-06-07. Unblocks `Core`, `EventStruct`, `OpSem`
(abstract command/action granularity, the interchange format, interface freezes).
Resolves the open questions **Q1, Q2, Q4, Q5** on command/action granularity and pins **Q2** of
`docs/MORDOR_ISA_FORMAT.md`. Inputs: paper `app-opsem.tex` / `app-defs.tex` +
`rules/{actions,commands,step}:*`, and the implemented `isa` outputs
(`workspace/spikes/uaf-bridge/{uaf,uaf_fixed,cas_aba}_isa.json`).

This document fixes the concrete Isabelle types for the program **labels**, the
**action**/**command**/**expr** vocabulary, and the digested `LABEL is INSTRUCTION`
program. It is the `Core` layer's public API; `EventStruct` (Φ over event-labels) and
`OpSem` (commands → actions, `step prog Φ`) are written against it.

---

## 0. The two-line summary of the decisions

1. **Two label granularities, formally linked.** The *digest* is keyed by a **static
   instruction-label** `iloc` (≈ MoRDor `t<tid>.<seq>` + its `loops` array). Φ and
   histories are over **event-labels** `elabel = iloc + iteration-vector + sub-event
   index `k``. The paper's formal label `l` (with per-event `pc`, `loopfun`, `iter`) **is**
   the `elabel`; an instruction with `n` events (CAS=3, FAA=2) is **one digest entry** whose
   `command` emits the `elabel` sequence `#0..#(n-1)` (resolves **Q2**).
2. **`pc(l)` is derived, never a hand-coded enum.** `pc(l) = (ilo_seq, k)` — the syntactic
   per-thread instruction position plus the RMW sub-event index. `I1…S7` survive only as
   *abbreviations over keys*, not a datatype (retires the `RCU_state.PC` enum).
3. **Rolled digest, unrolled Φ, bridged by the iteration-vector.** The digest carries
   `If`/`While` structure (rolled). `elabel.el_iters` carries the dynamic `iter(l)(ℓ)` that
   MoRDor's `@loop:iter` suffix supplies; the `lb` rule's `iter(H) < iter(l)` test reads it
   directly (resolves **Q4**).
4. **Lexicographic linorder via an explicit order key** `okey :: elabel ⇒ (nat × nat) list`
   ordered by `lexordp` — outer-loop `(header, iter)` dominates inner, terminated by
   `(seq, k)` (resolves **Q5**).
5. **Hand-author the digest, machine-check it against `isa`; always generate Φ** (resolves
   **Q1**).

---

## 1. Labels (`Core`)

### 1.1 The paper object

`app-opsem.tex` §Configurations: an event is a pair `l : a` of *control label* `l` and
*action* `a`. Each label is associated with a line in code / instruction, a program counter
`pc(l)`, loop indices `ℓ ∈ loopfun(l)`, and per loop index an iteration `iter(l)(ℓ)`.
`app-defs.tex` (l.193–195, 416–417): `loopfun : Labels → ℕ`, `iter : Labels → Pfn(ℕ,ℕ)`,
and `pc : Events → ℕ` — crucially "**program counters differ from lines of code in
particular for composite operations such as RMW operations**". So `pc` is a *per-event*
notion: the three events of a CAS share a source line but carry distinct `pc`.

### 1.2 Decision — instruction-label vs event-label (Q2)

```isabelle
type_synonym tid    = nat
type_synonym loopid = nat
type_synonym iter   = nat

(* Who owns the instruction: the thread-less init/preamble (MoRDor "g.*") or a thread. *)
datatype owner = Init | Thr tid

(* STATIC instruction-label = the digest key. MoRDor "t<tid>.<seq>" + its "loops" array. *)
record iloc =
  ilo_owner :: owner
  ilo_seq   :: nat            (* 1-based syntactic position within the owner (MoRDor <seq>) *)
  ilo_loops :: "loopid list"  (* loopfun: enclosing loops, innermost LAST ([] outside loops) *)

(* DYNAMIC event-label = the paper's formal label l = (pc, loopfun, iter), the key of Φ/H.
   pc(l) = (ilo_seq, el_k); loopfun(l) = ilo_loops; iter(l) = el_iters (aligned to loops). *)
record elabel =
  el_iloc  :: iloc
  el_iters :: "iter list"     (* iter(l)(ℓ) for each ℓ in ilo_loops, same order; [] outside *)
  el_k     :: nat             (* sub-event index within the instruction (RMW: 0,1,2) *)
```

**Relationship (the freeze).** `event-label = (instruction-label, iteration-vector,
event-index)`. Equivalently the projection used by the rules:

```isabelle
definition pc      :: "elabel ⇒ nat × nat" where "pc l      = (ilo_seq (el_iloc l), el_k l)"
definition loopfun :: "elabel ⇒ loopid list" where "loopfun l = ilo_loops (el_iloc l)"
(* iter as a partial map loopid ⇀ iter, built by zipping loops with el_iters *)
definition iterf   :: "elabel ⇒ loopid ⇀ iter" where
  "iterf l = map_of (zip (ilo_loops (el_iloc l)) (el_iters l))"
```

Why `iters` lives on `elabel`, not `iloc`: the digest is **rolled** — the static instruction
is in loop `ℓ` (it carries `ilo_loops`) but has no iteration until run. MoRDor's Φ is
**unrolled** and supplies the iteration via the `@loop:iter` suffix; the renderer parses
`"t0.7@1:1#2"` into `⟨el_iloc = ⟨Thr 0, 7, [1]⟩, el_iters = [1], el_k = 2⟩`. This is exactly
the rolled/unrolled bridge of Q4 (§4).

### 1.3 Mapping the `isa` label strings

| isa string            | parse                                                            |
|-----------------------|------------------------------------------------------------------|
| `g.4`                 | `iloc ⟨Init, 4, []⟩`                                              |
| `t0.7`                | `iloc ⟨Thr 0, 7, [1]⟩` (its `loops` field gives `[1]`)           |
| `t1.1#0`              | `elabel ⟨⟨Thr 1, 1, []⟩, [], 0⟩`                                 |
| `t0.7@1:1#2`          | `elabel ⟨⟨Thr 0, 7, [1]⟩, [1], 2⟩` (loop 1, iter 1, sub-event 2)  |
| `t0.7@2:3@1:1#0` (nested, hypothetical) | `elabel ⟨⟨Thr 0, 7, [2,1]⟩, [3,1], 0⟩` — see §4 ordering note |

The static `loops` array in the instruction record is the source of truth for `ilo_loops`;
the renderer asserts each event-label's `@loop:iter` loops agree with it (a conformance
check, §5).

### 1.4 Lexicographic linorder (Q5)

The paper orders labels "lexicographically over all loop indices `ℓ`", extended to `l ≤ H`,
to detect loop-boundary crossings. We realise it by an explicit **order key** and the
standard list-lex order:

```isabelle
(* one (loop-header position, iteration) pair per enclosing loop, outer FIRST,
   terminated by the leaf (seq, k). header_seq ℓ = ilo_seq of ℓ's While instruction. *)
definition okey :: "(loopid ⇒ nat) ⇒ elabel ⇒ (nat × nat) list" where
  "okey hdr l =
     map (λ(ℓ,i). (hdr ℓ, i)) (zip (rev (ilo_loops (el_iloc l))) (rev (el_iters l)))
     @ [(ilo_seq (el_iloc l), el_k l)]"

(* owner ordered Init < Thr 0 < Thr 1 < … ; within an owner, lexordp on okey *)
instantiation elabel :: linorder ...   (* ≤ ≡ lexicographic on (owner, okey hdr) *)
```

Properties this gives (the program order the rules need):
- same loop, same iteration, positions `s_a < s_b` ⇒ leaf `(s_a,·) < (s_b,·)` ✓;
- same loop, iteration `i < i'` ⇒ outer pair `(hdr ℓ, i) < (hdr ℓ, i')` dominates ✓ (later
  iteration is strictly greater, the property `lb` relies on);
- outer-loop iteration dominates inner-loop position/iteration (nested loops) ✓;
- instruction outside a loop vs inside: discriminated by the leaf `seq` against the loop
  header's `seq` (program text order) ✓.

`iter(H) < iter(l)` (the `lb` guard) is then the per-loop projection:

```isabelle
definition iter_H :: "(elabel × action) set ⇒ loopid ⇒ iter" where
  "iter_H H ℓ = Max (insert 0 {i. ∃l a. (l,a) ∈ H ∧ iterf l ℓ = Some i})"
(* lb fires for ℓ = innermost loopfun(l) when  iter_H H ℓ < the_iter (iterf l ℓ) *)
```

`hdr` (loop-id → header `seq`) is a static table extracted once from the digest's `While`
instructions, so `okey` needs no global state. **RCU is the first real stress** of nested /
back-to-back loops here (§4).

---

## 2. Actions, commands, expressions (`Core`/`MemSem`/`OpSem`)

### 2.1 Memory orders, locations, values, expressions

```isabelle
datatype mem_order = Rlx | Acq | Rel | Acq_rel | Sc

type_synonym reg  = string         (* register name, MoRDor "reg" *)
type_synonym var  = string         (* global symbolic variable x (read-var / write-var) *)
type_synonym sym  = nat            (* symbolic value α / symbolic location returned by alloc *)
type_synonym valu = int            (* concrete integer literal *)

(* Expressions: app-defs E ::= E_A | E_B.  Kept as one datatype; a bexp is an expr.    *)
datatype expr =
    EInt  int                      (* {"int":n} *)
  | EReg  reg                      (* {"reg":"r"} *)
  | ESym  sym                      (* symbolic value α (read events introduce fresh symbols) *)
  | EDeref expr                    (* *e *)
  | EAdd  expr expr | ESub expr expr | EMul expr expr | EDiv expr expr
  | EEq   expr expr | ELeq expr expr
  | ENot  expr      | EAnd expr expr | EOr expr expr
type_synonym bexp = expr           (* E_B is a sub-language; condition slot is an expr *)
```

`loc` operands: a *direct* global variable (`x` in read-var/write-var) is an `expr` `EReg`/a
`var`; a *pointer* target (`*e`) is an arbitrary `expr`. We keep one `expr` slot and let the
command constructor say whether it is dereferenced (mirrors the appendix's `x` vs `*e`).

### 2.2 `action` (Core/MemSem — the level Φ and `σ ⤳ₜ σ'` are built on)

One constructor per `rules/actions:*` (read, write, fence/branch, allocate, deallocate):

```isabelle
datatype action =
    Read    mem_order sym sym      (* a = R_o  x α   : read symbol α at location x        *)
  | Write   mem_order sym expr     (* a = W_o  x e   : write e to location x               *)
  | Branch  bexp                   (* a = Branch (α = ⟦e_s⟧) — fence/branch leave σ fixed  *)
  | Fence   mem_order              (* a = Fence_o                                          *)
  | AllocA  sym expr               (* a = Alloc x v  : σ.memory ∪ {x}, φ ∧ ⋀ x ≠ α         *)
  | DeallocA sym                   (* a = Dealloc x  : σ.memory ∖ {x}                       *)
```

`type(a) ∈ {Fence, Branch}` (the `actions:fence/branch` rule's side condition) is the obvious
discriminator. Locations in actions are *symbolic* (`sym`) — they are the evaluated
`⟦e⟧_ρ`/`σ.φ`-resolved targets, not raw expressions; this matches `σ.viswrite : Sym ⇀ Write`.

### 2.3 `command` / instruction (OpSem — one ctor per `rules/commands:*`)

```isabelle
datatype command =
    Set      reg expr                              (* commands:set      i := e            *)
  | ReadVar  mem_order reg var                     (* commands:read-var i :=^o x          *)
  | ReadPtr  mem_order reg expr                    (* commands:read-ptr i :=^o *e         *)
  | ReadRef  reg var                               (* commands:read-ref i := &x  (no event)*)
  | WriteVar mem_order var expr                    (* commands:write-var x :=^o e          *)
  | WritePtr mem_order expr expr                   (* commands:write-ptr *e_l :=^o e_v     *)
  | Fence    mem_order                             (* commands:fence                       *)
  | Faa      mem_order mem_order reg expr expr     (* commands:faa  i := FAA^{o_r,o_w}(x,e)*)
  | Cas      mem_order mem_order reg expr expr expr(* commands:cas  i:=CAS^{o_r,o_w}(x,es,en)*)
  | Malloc   reg expr                              (* commands:alloc i := malloc(e)        *)
  | Free     reg                                   (* commands:free  free(i)               *)
  | If       bexp "instr list" "instr list"        (* control flow (then/else)             *)
  | While    loopid bexp "instr list"              (* rolled loop, carries its loop-id     *)
and instr = Instr (instr_loc: iloc) (instr_cmd: command)
```

Notes:
- **`command` is operand-generic** — no baked `C`/`var_s`. `prog` is data, not a per-PC
  `case` (retires `RCU_atomics.get_C_val`, `cas_step_rcu`, `RCU_prog.prog`).
- **One generic effect rule per constructor** emits the action sequence (`OpSem`, mirrors the
  appendix): `Faa → [Read o_r x α, Write o_w x n]`; `Cas`-success →
  `[Read o_r x α, Branch (α=⟦e_s⟧), Write o_w x n]` (guard `α ≡_{σ.φ} ⟦e_s⟧`); `Cas`-failure →
  `[Read o_r x α, Branch (α=⟦e_s⟧)]`, **acquire-only on `o_r`, no release** (paper §sec:cas,
  the asymmetry that admits the reorder — MemSem/OpSem job). Proved **once**,
  not per PC.
- `ReadRef` and `Set` emit **no** action (`events: []` in the isa output — cf. `cas_aba`
  `t0.1` Set), so they step `σ` unchanged and only update `ρ`.
- `If`/`While` carry nested `instr list` bodies — the **rolled** structure (MoRDor's nested
  `then`/`else`/`body`). `While` records its `loopid` (MoRDor `loop_id`), which feeds the
  static `hdr`/`ilo_loops` tables. (MoRDor emits `Do`/`While`; both map here, the renderer
  normalises to `While`.)

### 2.4 `command → events` arity (the `iloc`↔`elabel` link, §1.2)

```isabelle
fun n_events :: "command ⇒ nat" where
  "n_events (Set _ _) = 0"   | "n_events (ReadRef _ _) = 0"
| "n_events (Faa _ _ _ _ _) = 2"
| "n_events (Cas _ _ _ _ _ _) = 3"   (* the W (#2) is absent on a failing CAS, decided at step time *)
| "n_events _ = 1"
```

The digest entry for label `il` thus stands for event-labels `⟨il, iters, 0⟩ … ⟨il, iters,
n_events c − 1⟩`, with `iters` supplied by the run/Φ — exactly the paper's `(l : ā) ∈*
horizonΦ_H` (one label `l`, action list `ā`).

---

## 3. The `LABEL is INSTRUCTION` digest

### 3.1 Type and notation

```isabelle
type_synonym program = "instr list"        (* the whole digest; owner in each iloc separates
                                              Init (MoRDor "g.*") from each thread            *)

(* the rolled per-thread / init command map  prog(o) : iloc ⇀ command  (paper proḡ(t)) *)
definition prog :: "program ⇒ owner ⇒ iloc ⇀ command" where
  "prog P own = map_of (map (λi. (instr_loc i, instr_cmd i))
                            (filter (λi. ilo_owner (instr_loc i) = own) P))"

(* readable digest constructor:  LABEL is INSTRUCTION *)
definition is_entry :: "iloc ⇒ command ⇒ instr"  ("(_ is/ _)" [61,60] 60)
  where "l is c = Instr l c"
```

> **Keyword caveat.** `is` is used by Isar's `(is "?pat")` term-abbreviation at the
> *command* level, not in inner term syntax, so a mixfix delimiter `"(_ is _)"` is expected to
> parse — but **verify on first build**. Fallbacks if it shadows: notation `"(_ ≜ _)"`
> (`\<triangleq>`) or `"(_ ::: _)"`. Mnemonic labels (`I8`, `cas_res`) survive as
> abbreviations over keys, e.g. `abbreviation "i8 ≡ ⟨Thr 0, 8, [1]⟩"`.

### 3.2 Rendered uaf-bug digest (from `uaf_isa.json`)

```isabelle
(* helper keys (would be generated as abbreviations; Init seqs 1..4, threads 1..) *)
abbreviation "g1 ≡ ⟨Init, 1, []⟩"   abbreviation "g2 ≡ ⟨Init, 2, []⟩"
abbreviation "g3 ≡ ⟨Init, 3, []⟩"   abbreviation "g4 ≡ ⟨Init, 4, []⟩"
abbreviation "t0_1 ≡ ⟨Thr 0, 1, []⟩"  abbreviation "t0_2 ≡ ⟨Thr 0, 2, []⟩"
abbreviation "t0_3 ≡ ⟨Thr 0, 3, []⟩"
abbreviation "t1_1 ≡ ⟨Thr 1, 1, []⟩"  abbreviation "t1_2 ≡ ⟨Thr 1, 2, []⟩"

definition prog_uaf_bug :: program where
  "prog_uaf_bug = [
     g1   is Malloc   ''rC''  (EInt 1),
     g2   is WritePtr Rlx (EReg ''rC'')  (EInt 0),
     g3   is Malloc   ''rcu'' (EInt 1),
     g4   is WritePtr Rlx (EReg ''rcu'') (EInt 1),
     t0_1 is ReadPtr  Rlx ''rtemp'' (EReg ''rcu''),
     t0_2 is If (EEq (EReg ''rtemp'') (EInt 0))
                [ t0_3 is Free ''rC'' ]            (* then *)
                [],                                (* else *)
     t1_1 is ReadPtr  Rlx ''rv''  (EReg ''rC''),
     t1_2 is WritePtr Rlx (EReg ''rcu'') (EInt 0) ]"
```

**The fix** (`uaf_fixed_isa.json`) changes exactly one operand — `t1_2`'s order — and Φ gains
the discriminating edge `["t1.1#0","t1.2#0"]`:

```isabelle
   t1_2 is WritePtr Rel (EReg ''rcu'') (EInt 0)    (* rlx → rel; + acq enter; deref→exit edge appears *)
```

The digest is read literally: "`t1_1` **is** `ReadPtr Rlx rv rC`". Operands are arguments; the
label is just the key.

### 3.3 CAS as one entry, three sub-events (from `cas_aba_isa.json` `t0.7`)

```isabelle
abbreviation "t0_7 ≡ ⟨Thr 0, 7, [1]⟩"   (* inside While loop_id = 1 *)
   …
   t0_7 is Cas Acq Rel ''rsucc'' (EReg ''rC'') (EReg ''rs'') (EReg ''rn'')
```

One digest entry; `n_events (Cas …) = 3` ⇒ event-labels `t0.7@1:i#0` (R), `t0.7@1:i#1`
(Branch), `t0.7@1:i#2` (W), the last absent on failure. Φ edges reference these `elabel`s.

---

## 4. Rolled program ↔ unrolled Φ and the `lb` reset (Q4)

**The shape of the problem.** The digest is **rolled** (`While loopid bexp body`); MoRDor
computes Φ on a **step-counter-unrolled** event set, so Φ's event-labels carry the iteration
in `@loop:iter`. The `lb` rule (`rules/step:lb`) fires when stepping a label `l` whose
iteration exceeds everything in `H` for that loop (`iter(H) < iter(l)`), resets `σ`/`ρ`/`φ`/`H`
restricted to that loop (`·|^t_{∖loopfun(l)}`), and re-bases the label to the loop start
`l⁻ = (pc(l), 0)`.

**How the iteration carries (the design).**
- Φ stays indexed by **`elabel`** (iteration-vector included). The renderer parses each
  MoRDor `@loop:iter` suffix into `el_iters` (and asserts the loops agree with the static
  `ilo_loops`). So Φ membership `(l:ā) ∈* horizonΦ_H` compares fully-iterated event-labels —
  no rolling needed on Φ's side.
- The **digest** stays rolled; `OpSem`'s step, when it enters the body of `While ℓ`, manufactures
  the candidate `elabel` for each body instruction with the *current* iteration of `ℓ`
  (tracked as `iter_H H ℓ` + 1 at a boundary, else `iter_H H ℓ`). This is the only place the
  rolled digest and the unrolled `el_iters` meet.
- The `lb` guard is then `iter_H H ℓ < the (iterf l ℓ)` (§1.4); the reset
  `H ∖ {(l':_) | loopfun ℓ ⊆ loopfun(l')}` and the `σ`-restrictions are loop-id filters over
  `el_iters`/the `ilo_loops` of stored entries. `l⁻ = (pc(l), 0)` is
  `el_iters := (el_iters l)[ℓ ↦ 0]` — drop to iteration 0 at the same `pc`.

**What RCU stresses (flagged, not yet exercised — cas_aba is the closest precedent):**
1. **Back-to-back loops** in one thread (cas_aba `t1.3` then `t1.10`, distinct `loop_id`s 2,3) —
   the `hdr`/`ilo_loops` tables must keep loop-ids globally unique per program so `iter_H`
   doesn't bleed across loops. MoRDor already assigns fresh ids (1,2,3), good.
2. **Nested loops** (sync()/grace-period inside a retry) — `ilo_loops`/`el_iters` length > 1;
   `okey`'s outer-first ordering (§1.4) and the loop-restriction `loopfun ℓ ⊆ loopfun(l')` are
   only exercised by RCU. The nested example label form is the hypothetical `t0.7@2:3@1:1#0`
   in §1.3; **validate the suffix order convention (outer-first vs inner-first) against the
   first RCU `isa` output** — MORDOR_ISA §2 says "innermost last" for `loops`, so the `@`
   suffix order must be pinned the same way (renderer asserts it).
3. **`iter(H)` over a partially-reset history** — after an `lb` reset the surviving `H`
   entries are the pre-loop ones; `iter_H` must return 0 for a freshly-entered loop. The
   `Max (insert 0 …)` form handles the empty case.

This is a *design*, not a proof: the obligation `EventStruct`/`OpSem` must discharge is that
`iter_H`/`okey` make the `lb` rule fire exactly at MoRDor's unrolled iteration boundaries
(a regression `value`-check against the RCU `isa` Φ).

---

## 5. Q1 — generate vs hand-author the digest

**Recommendation: hand-author the `LABEL is INSTRUCTION` digest; machine-check it against the
`isa` output; always generate Φ.**

Rationale, now that `isa` exists:
- **Trusted base stays small & the digest stays auditable.** The digest is the *readable
  specification* of the client program. Hand-authoring keeps MoRDor's parser
  out of the trusted base for the program text, and keeps the Isabelle readable (a generated
  digest risks the "ugly, hard-to-audit Isabelle" of Q1).
- **`isa` removes the drift risk for free.** Because the schema now carries the full structured
  program (labels, commands, operands, loops), we can mechanically cross-check the hand digest
  against it — a conformance test that the hand digest's
  `{(iloc, command-shape, loops)}` set equals the rendered `isa` document. This is the best of
  both: auditable source **and** a machine guarantee it matches MoRDor's parse.
- **Φ is always generated** (`scripts/generate_phi.py`): it is large, unreadable,
  and not meant to be inspected; it carries a provenance header.

Concretely:
- `clients/*/prog_*.thy` hold the hand digests (§3) + mnemonic abbreviations.
- `scripts/generate_phi.py` renders `Φ_*` over `elabel` **and** emits a checkable structural
  dump (`(label, op, operands, loops, events)` per instruction) the digest theory asserts
  against via `value`/lemma — the conformance fixture is `uaf-bug{,-fixed}` (MORDOR_ISA §0).
- **Fallback** (large/auto programs, or if hand-authoring RCU proves error-prone): flip to
  renderer-generated digests using the *same* schema — the `isa` boundary already supports it
  (MORDOR_ISA §0 leaning), so this is a config switch, not a redesign.

---

## 6. What this freezes for downstream layers

- **`Core`** owns: `owner`, `iloc`, `elabel`, `mem_order`, `expr`/`bexp`, `action`,
  `command`/`instr`, `program`, the `_ is _` notation, and the label algebra
  (`pc`, `loopfun`, `iterf`, `okey`, `linorder elabel`, `iter_H`). No semantics.
- **`MemSem`** consumes `action` for `σ ⤳ₜ σ'` (read/write/alloc/dealloc/fence-branch);
  `sym` locations and `expr` values are the interface.
- **`EventStruct`** is parameterised over `elabel`/`action`; Φ is `(elabel × elabel) set set`
  (edge-sets per execution), `horizonΦ_H` and `(l:ā) ∈* horizonΦ_H` use `pc`/`iterf`/`okey`.
- **`OpSem`** consumes `command`/`prog`, emits `action` lists per §2.3, and the `step` rules
  use the `lb` machinery of §4.

---

## 7. Residual tensions / open items (carried forward)

1. **`is` mixfix keyword clash** (§3.1) — needs a one-line build check; `≜` fallback ready.
2. **`okey` faithfulness for nested loops** (§1.4/§4) — the proposed outer-first key is
   unproven against RCU; the first RCU `isa` Φ is the regression that confirms (or refutes) it,
   and pins the `@loop:iter` suffix order. *Highest-value next check.*
3. **`pc(l) = (seq, k)` vs a flat `nat`** — the paper's `pc : Events → ℕ` is a single nat; we
   use a pair `(seq,k)` for RMW sub-events. Order-isomorphic to a flattened nat, so faithful,
   but if a downstream proof wants the literal `ℕ` we can collapse via a pairing. Noted, not
   blocking.
4. **`var` vs `sym` for read-var/write-var locations** — direct globals are named `var`
   (string) while pointer targets evaluate to `sym`. Kept distinct in `command`; both resolve
   to `sym` in `action`. Confirm against the first RCU digest (RCU uses named globals `C`,
   `rcu[]`).
5. **Init ordering** — `Init` is ordered before all threads in the `elabel` linorder; adequate
   for the preamble, but if MoRDor ever interleaves init with threads this needs revisiting
   (not the case in any current `isa` output).
6. **MORDOR_ISA v0.2 "after-threads"/`Do`-vs-`While`** — the epilogue bucket and `Do`
   normalisation (§2.3) are renderer concerns; the `command` type already covers them.
