# MoRDor ↔ Isabelle interchange format (`isa` output) — SPECIFICATION

**Status:** v0.1 — **implemented in MoRDor and conformance-passing (2026-06-07).** MoRDor's
`isa` output mode (`src/isa_export.ml`) now emits this schema; verified against
`uaf-bug{,-fixed}.lit` (structure + bug/fix discriminating edge) and `cas_aba.lit` (RMW
sub-events + loop-iteration suffixes). This spec is a **deliverable of `isa-smrd-opsem`** and the
**contract** for that output. v0.2 refinements + RCU validation pending in **Spike B**.

## 0. Boundary decision *(leaning, confirm)*
MoRDor emits a **versioned structured JSON** per this schema; the repo's `scripts/generate_phi.py`
renders it to Isabelle (the `_ is _` digest + `Φ_P` constant + label defs). This keeps
Isabelle-specific notation in this repo and MoRDor Isabelle-agnostic/reusable. *(Alternative:
`isa` emits Isabelle source directly — rejected for the first cut.)*
Every document carries `format_version`; the conformance fixture is `programs/uaf-bug{,-fixed}.lit`.

## 1. Top-level schema
```json
{
  "format_version": "0.1",
  "program": "uaf-bug.lit",
  "orders": ["rlx","acq","rel","acq_rel","sc"],
  "init":    [ <instruction>, ... ],          // thread-less setup (allocations, init writes)
  "threads": [ { "tid": <int>, "body": [ <instruction>, ... ] }, ... ],
  "futures": [ { "execution": <int>, "edges": [ [<evlabel>,<evlabel>], ... ] }, ... ]
}
```
- `init` is straight-line setup executed before the threads (the `.lit` preamble).
- `body` is a thread's **rolled** program (control flow preserved; see §3).
- `futures[*].edges` are `(ppo∪DP)` edges over **event-labels** (§4); identity edges may be
  omitted (the renderer adds reflexive closure).

## 2. Label model *(closes Q2/Q4/Q5)*
- **instruction-label** = `"t<tid>.<seq>"` (e.g. `"t0.1"`), stable per source instruction.
  *(Open: use source `line:col` instead of `seq` — DECIDE in Spike B; renderer maps either to the
  Isabelle key.)*
- **event-label** = `"<instruction-label>#<k>"`, `k` = 0-based event index within the instruction.
  An RMW (CAS=3, FAA=2) shares one instruction-label; its sub-events are `#0,#1,#2`.
- **loops / iter** *(rolled program):* each instruction carries `"loops": [<loop-id>...]`
  (`loopfun`, innermost last; `[]` if outside loops). Event-labels inside loops gain an iteration
  suffix `"@<loop-id>:<iter>"` in `futures` (MoRDor's unrolled events), which the `lb`-rule
  collapses. UAF has no loops; **RCU is the first real test of this part.**
- Lexicographic order over `(t, seq/line:col, loops, iter, k)` realises the paper's
  `(pc,loopfun,iter)` comparison.

## 3. Instruction & command grammar
```json
{ "label": "t0.2", "loc": [6,2], "loops": [],
  "command": { "op": "...", ... },
  "events":  [ { "k": 0, "type": "R" }, ... ] }
```
`command.op` ∈ the appendix grammar (operands shown):
| op | operands | events |
|----|----------|--------|
| `Set`       | `dst`, `expr` | — |
| `ReadPtr`   | `order`, `dst`, `ptr` | `R` |
| `ReadVar`   | `order`, `dst`, `var` | `R` |
| `ReadRef`   | `dst`, `var` | — |
| `WritePtr`  | `order`, `ptr`, `val` | `W` |
| `WriteVar`  | `order`, `var`, `val` | `W` |
| `Faa`       | `order_r`, `order_w`, `dst`, `loc`, `addend` | `R;W` |
| `Cas`       | `order_r`, `order_w`, `dst`, `loc`, `expected`, `new` | `R;Branch;W` (succ) / `R;Branch` (fail) |
| `Alloc`     | `dst`, `size` | `Alloc` |
| `Free`      | `ptr` | `Dealloc` |
| `Fence`     | `order` | `Fence` |
| `If`        | `cond`, `then`:[instr…], `else`:[instr…] | `Branch` |
| `While`     | `cond`, `body`:[instr…], `loop_id` | `Branch` |

`expr` / `cond` / `val`: `{"int":n}` | `{"reg":"r"}` | `{"eq":[e,e]}` | `{"add":[e,e]}` | …
`ptr`/`loc`: a register holding an address (`{"reg":"rC"}` or bare `"rC"`).

## 4. Events / actions
Event `type` ∈ `R | W | Branch | Fence | Alloc | Dealloc` (MoRDor's `I`/`T` init/terminator are
implicit, not digest instructions). Each event inherits `order`/`loc`/value from its command.

## 5. Worked example — `uaf-bug.lit`  *(idealised target format)*
```json
{
  "format_version": "0.1",
  "program": "uaf-bug.lit",
  "orders": ["rlx","acq","rel","acq_rel","sc"],
  "init": [
    { "label": "g.1", "loc": [1,0], "loops": [], "events": [{"k":0,"type":"Alloc"}],
      "command": { "op": "Alloc", "dst": "rC", "size": {"int": 1} } },
    { "label": "g.2", "loc": [2,0], "loops": [], "events": [{"k":0,"type":"W"}],
      "command": { "op": "WritePtr", "order": "rlx", "ptr": "rC", "val": {"int": 0} } },
    { "label": "g.3", "loc": [3,0], "loops": [], "events": [{"k":0,"type":"Alloc"}],
      "command": { "op": "Alloc", "dst": "rcu", "size": {"int": 1} } },
    { "label": "g.4", "loc": [4,0], "loops": [], "events": [{"k":0,"type":"W"}],
      "command": { "op": "WritePtr", "order": "rlx", "ptr": "rcu", "val": {"int": 1} } }
  ],
  "threads": [
    { "tid": 0, "body": [
      { "label": "t0.1", "loc": [6,2], "loops": [], "events": [{"k":0,"type":"R"}],
        "command": { "op": "ReadPtr", "order": "rlx", "dst": "rtemp", "ptr": "rcu" } },
      { "label": "t0.2", "loc": [7,2], "loops": [], "events": [{"k":0,"type":"Branch"}],
        "command": { "op": "If", "cond": {"eq": [{"reg":"rtemp"}, {"int":0}]},
          "then": [
            { "label": "t0.3", "loc": [8,4], "loops": [], "events": [{"k":0,"type":"Dealloc"}],
              "command": { "op": "Free", "ptr": "rC" } } ],
          "else": [] } }
    ] },
    { "tid": 1, "body": [
      { "label": "t1.1", "loc": [13,2], "loops": [], "events": [{"k":0,"type":"R"}],
        "command": { "op": "ReadPtr", "order": "rlx", "dst": "rv", "ptr": "rC" } },
      { "label": "t1.2", "loc": [14,2], "loops": [], "events": [{"k":0,"type":"W"}],
        "command": { "op": "WritePtr", "order": "rlx", "ptr": "rcu", "val": {"int": 0} } }
    ] }
  ],
  "futures": [
    { "execution": 5,
      "edges": [
        ["t1.1#0", "t0.3#0"],          // deref rC  →  free rC  (cross-thread, via rf)
        ["t0.1#0", "t0.2#0"]           // read rcu  →  branch
        // NB (bug): NO edge ["t1.1#0","t1.2#0"]  (deref → rcu-exit) — relaxed, reorderable ⇒ UAF
      ] }
  ]
}
```
Rendered Isabelle (sketch):
```
prog_uaf_t1 = [ t1_1 is ReadPtr rlx rv rC,  t1_2 is WritePtr rlx rcu 0 ]
```
**The fix** (`uaf-bug-fixed.lit`): `t1.2` becomes `WritePtr rel rcu 0` (and an `acq` enter), and
`futures` **gains** the edge `["t1.1#0","t1.2#0"]` (deref → release-exit) — the discriminating
edge from §5 / `tab-fut-step-fix`, which keeps the free out of the horizon until the deref.

## 6. CAS as one instruction, three events
```json
{ "label": "i.11", "loc": [11,2], "loops": ["L_inc"], "events": [
    {"k":0,"type":"R"}, {"k":1,"type":"Branch"}, {"k":2,"type":"W"} ],
  "command": { "op": "Cas", "order_r": "acq", "order_w": "rel",
               "dst": "r", "loc": "C", "expected": {"reg":"s"}, "new": {"reg":"n"} } }
```
Event-labels `i.11#0` (R), `i.11#1` (Branch), `i.11#2` (W); on a failing CAS the `W` (`#2`) is
absent. `Φ` edges reference these event-labels.

## 7. Open decisions (v0.2 / Spike B)
- Instruction-label = `t.seq` vs source `line:col` (§2). *(v0.1 impl uses `t<tid>.<seq>` /
  `g.<seq>`, 1-based pre-order per thread.)*
- Control flow as **nested** `then`/`else`/`body` (impl) vs a **flat** labelled list with branch
  targets — renderer's job either way; nested is the readable first cut.
- The `loops`/`iter` encoding (§2) — validated best-effort on `cas_aba.lit`
  (`t0.4@1:1#0`, `t0.7@1:1#2`); **validate fully on RCU** (real retry loops).
- **"After-threads" statements (v0.2):** a top-level statement following the threads block
  (e.g. the trailing `rv := *rC` in `cas_aba.lit`) is currently bucketed into `init`, since the
  schema has no epilogue section. Decide: add a `"fini"`/`"epilogue"` array, or keep folding into
  `init` (documented).
- §0 boundary confirmed for v0.1: MoRDor emits the schema; repo renders Isabelle.
- **Grammar gaps found by the W3 renderer (add in v0.2):** `Do` (do-while) op appears in
  `cas_aba` but is not in §3 (renderer treats it like `While`); and `Faa`/`Cas` carry an
  `rmw_op` field (`"strong"`) not in the §3 operand table (currently dropped). Add both to §3.
- **Provenance decision (Spike B / §4 Q1):** the digest is **hand-authored + machine-checked**
  against the `isa` structural dump; the W3 renderer is a fallback. So `isa` is the *check
  oracle* for the program, and the *source of truth* for Φ.
