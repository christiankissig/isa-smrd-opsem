# Spike A — RCU MoRDor bridge (loops/iter validation)

Date: 2026-06-07 (sc=1 on rcu-1/rcu-3); **updated 2026-06-09** (iter-labels validated on a
minimal retry-loop fixture — see "Resolution" below).
Relates to the v0.2 open item of `docs/MORDOR_ISA_FORMAT.md`: RCU loops/iter on a real retry loop.

MoRDor binary: `/home/christian/workspace/mordor/_build/default/cli/main.exe`
Inputs: `programs/rcu-1.lit` (single thread), `programs/rcu-3.lit` (3 threads, `|||`-separated),
and the local fixture `rcu-inc-loop.lit` (single-thread inc() retry loop only).

## Resolution (2026-06-09): `@loop:iter` labels validated on a real RCU retry loop

The README's earlier recommendation (a) — "a minimal CAS-retry fixture small enough to
terminate at sc≥2 so a future edge lands inside the retry loop" — is **done**. Fixture
`rcu-inc-loop.lit` is the inc() retry loop only (reclaim/sync dropped, single thread,
`rN=1`/one node) so it stays small.

- **`--step-counter 2` TERMINATES on this fixture**: 2:13 wall, peak RSS 2.0 GB, exit 0
  (full rcu-1 at sc=2 never finished — this fixture is small enough). sc=1 produces only setup
  events (loop body elided, 0 RF edges, nothing new).
- **`@loop:iter` labels ARE emitted on the RCU retry loop** at sc=2. The retry loop is
  `g.9` (`op:Do`, `loop_id 1`); its body statements `g.10..g.15` carry `loops:[1]` and their
  events appear in future edges as `g.N@1:1#k` — including the **RMW sub-events**:
  `g.12@1:1#1` (Faa write), `g.15@1:1#0`/`g.15@1:1#2` (Cas read/write). 18 futures, 8 distinct
  iter-bearing endpoint labels. This is the paper's `t.<stmt>@<loop_id>:<iter>#<event>` form,
  now exercised by RCU (not just `cas_aba`).
- **Init-scope events DO carry iter labels** (`g.N@1:1#k`). This *resolves the earlier worry*
  (problem #3 below) that single-thread/init-scope loops could not carry `@iter` slots — they
  can; the `g.` prefix is orthogonal to the iter suffix.
- **Only iter 1 appears, even at sc=2** (no `@1:2`; futures place edges *within* one
  representative iteration + to the post-loop write `g.16#0`). This is consistent with
  **episodicity**: the loop's dependency structure is captured by a single posterior iteration,
  so no inter-iteration (`iter 1→iter 2`) edges are needed. The lb-reset collapses iterations
  rather than producing cross-iteration future edges. (Q4 — "how event-labels carry iter for the
  lb-reset" — answered: each iteration relabels; the future stays single-iteration.)

Artifacts: `rcu-inc-loop.lit`, `rcu-inc-loop_isa_sc1.json` (baseline, no `@`),
`rcu-inc-loop_isa_sc2.json` (39 KB, the validated iter-label output).

---

## (Original 2026-06-07 findings on rcu-1/rcu-3 follow)

## TL;DR

- A terminating, output-producing invocation **was found**: `futures`/`executions` at
  `--step-counter 1` on **both** rcu-1 (single thread) and rcu-3 (3 threads). Sub-second, cheap.
- `--step-counter 2` does **NOT** terminate on rcu-1 (timed out at 120s *and* at 280s, RSS
  ballooning past 2.3 GB and still climbing). So **sc=1 is the largest bound that terminates**.
- The **rolled-loop structure** of the `isa` format is present and correct on RCU (every loop
  carries a `loop_id`; every body statement carries its enclosing `loops: [id]` nesting).
- The **`@loop:iter` event-label form is NOT exercised by RCU** at the terminating bound. RCU's
  computed futures only place dependency edges among non-loop *setup* events, so no edge endpoint
  ever lands inside a loop body — hence zero `@`/iter labels appear in either RCU `isa` output.
  The iter form itself is implemented and works (verified on `cas_aba_isa.json`), just not
  triggered by RCU. **Net: rolled structure validated on RCU; unrolled iter-labels remain
  unvalidated on RCU.**

## Runtimes / counts (all with `timeout`, `/usr/bin/time -v`)

| program | command | step-counter | result | wall | peak RSS |
|---|---|---|---|---|---|
| rcu-1 | executions | 1 | 2 executions | 0.20s | 0.35 GB |
| rcu-1 | executions | 2 | **timeout** (exit 124) | >120s | 2.29 GB |
| rcu-1 | futures (isa) | 1 | 2 executions / 8 events | 0.20s | 0.35 GB |
| rcu-1 | futures (isa) | 2 | **timeout** (exit 124) | >120s, retried >280s, still not done | >2.3 GB |
| rcu-3 | futures (isa) | 1 | 8 executions (minimised from 8) | 0.40s | 0.93 GB |
| rcu-3 | executions | 1 | (json emitted) | <1s | <1 GB |

## Working invocations (copy/paste)

```bash
BIN=/home/christian/workspace/mordor/_build/default/cli/main.exe
cd /home/christian/workspace/mordor

# single-thread RCU, isa output
timeout 120 "$BIN" futures --single programs/rcu-1.lit --step-counter 1 \
  --output-mode isa --output-file .../rcu1_isa.json

# 3-thread RCU, isa output
timeout 120 "$BIN" futures --single programs/rcu-3.lit --step-counter 1 \
  --output-mode isa --output-file .../rcu3_isa.json
```

`--step-counter 2` on rcu-1 is the smallest bound that blows up; do not run it unbounded.

## Artifacts in this directory

- `rcu1_isa.json` — rcu-1 futures `isa` output, sc=1 (the v0.2 retry-loop target, single thread).
- `rcu3_isa.json` — rcu-3 futures `isa` output, sc=1 (3 threads; loop bodies live in `threads`).
- `rcu1_executions_sc1.json`, `rcu3_executions_sc1.json` — `executions` cross-check exports.

## What the RCU loops/iter encoding looks like

The `isa` document (`format_version 0.1`) has keys
`format_version, program, orders, init, threads, futures`.

The program is emitted **rolled** as a statement tree. Each statement node:

```jsonc
{ "label": "t0.4", "loc": [L,C], "loops": [],
  "command": { "op": "Do", "cond": {...}, "loop_id": 1, "body": [ ...statements... ] },
  "events":  [ { "k": 0, "type": "Branch" } ] }
```

- **Loop construct**: `op: "Do"` carries `loop_id`. The retry `do { ... } while (rsucc=0)` loop is
  `loop_id 1`; the three `do { rtemp:=*(rcu+i) } while (rtemp=1)` spin loops are `loop_id 2,3,4`.
- **Loop nesting per statement**: the `loops` array lists enclosing loop ids. Retry-loop body
  statements (the relaxed write/write, `Faa`, read, write, `Cas`) are each tagged `loops: [1]`.
- **Thread vs init scope**: rcu-1 is single-thread, so the whole program lands in `init` with
  `g.N` labels and `threads: []`. rcu-3 has 3 threads → `init` holds the shared malloc/init prefix
  (`g.*`) and `threads` holds three bodies (`tid 0/1/2`) with `t0.*/t1.*/t2.*` labels. Each thread
  re-uses the same 4-loop shape, so loop ids run 1–4 (t0), 5–8 (t1), 9–12 (t2): 12 loops total.
- **Event labels in `futures` edges**: `<statement-label>#<event-index>`, e.g. `g.2#0`, `t0.3#0`.
  RCU edges only ever touch setup events (`Alloc`s and the pre-loop `*(rrcu+tid):=1` write `t*.3`),
  never loop-body events. Confirmed: 56 future edges across rcu-3's 8 executions use only the
  9 labels `{g.2#0,g.3#0,g.4#0,g.5#0,g.6#0,g.7#0,t0.3#0,t1.3#0,t2.3#0}` — none inside any loop.

### The `@loop:iter` label form (NOT seen on RCU, but real)

`docs/MORDOR_ISA_FORMAT.md` specifies loop-iteration labels of the form `t0.7@1:1#2`
(= `t<tid>.<stmt>@<loop_id>:<iter>#<event>`). These are emitted **only on event labels of events
that are both inside a loop AND referenced by a future edge**. In both RCU `isa` outputs the
character `@` appears **0 times**, because no RCU future edge reaches a loop-body event at sc=1.

The form is genuinely implemented — `workspace/spikes/uaf-bridge/cas_aba_isa.json` contains
`t0.4@1:1#0`, `t0.7@1:1#2`, `t1.4@2:2#1`, etc. So the iter encoding works; RCU just doesn't
trigger it.

## Problems / notes for the format spec (v0.2)

1. **Cannot positively validate iter-labels on RCU at a terminating bound.** sc=1 unrolls each
   loop once and yields no inter-iteration / loop-body future edges, so no `@iter` label is
   produced; sc≥2 (which would give multiple iterations and intra-loop dependence) does not
   terminate within minutes. The episodicity bound that would make a multi-iteration future set
   finite-and-cheap is not realised by raw `--step-counter` here.
2. **`futures` produce 0 RF edges at sc=1** (debug log: `RF edges: 0`, `reads: 0`), even for
   rcu-3 where three threads contend on `rC`. The minimal/deduplicated future set elides RF, which
   is *why* loop-body reads (the `Faa`/`Cas`/spin reads) never become edge endpoints. If the spec
   wants RCU to exercise iter-labels, the futures need to retain (or a different mode needs to
   surface) edges into loop bodies.
3. **init-scope loops carry no iter labels at all.** In rcu-1 the retry loop is a `Do` in `init`
   with `loop_id 1` and body `loops: [1]`, but init events are labelled `g.N#k` with no thread and
   no `@iter` slot. Whether the global/init section is *meant* to support per-iteration labels (vs
   only `threads`) is an open question for the format spec — single-thread litmus tests put the
   whole program, loops included, into `init`.
4. **Step-counter blow-up is the practical blocker.** rcu-1 sc=2 reaches >2.3 GB and does not
   finish in 280s; `--step-counter-per-loop` (default 2) was not separately tuned but the global
   bound dominates. Any RCU iter-label validation needs either an episodicity-aware bound or a
   smaller hand-rolled retry-loop fixture rather than full rcu-1/rcu-3 at sc≥2.

## Recommendation

For validating the loops/iter interchange encoding on a *real retry loop*, sc=1 confirms the
rolled structure but not the unrolled labels. Next step is either (a) a minimal 2-thread
CAS-retry fixture (à la cas-aba) small enough to terminate at sc≥2 so a future edge lands inside
the retry loop, or (b) make `futures` retain a loop-body RF edge so the existing rcu fixtures emit
`@loop:iter`. cas-aba already demonstrates the label form, so the format itself is not blocked.
