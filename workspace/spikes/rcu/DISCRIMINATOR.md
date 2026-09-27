# RCU bug/fix safety-edge discriminator (Spike A-RCU)

Date: 2026-06-09. Spike A-RCU.

Goal: check that the RCU no-use-after-free safety edge (the I6 release on the
exit write `*(rrcu + rtid) := 0`) behaves like the paper's UAF discriminator
(`tab-fut-step-bug` vs `-fix`): a gating ppo/DP future edge from the last
loop-body dereference to the exit write that is **present in the release (fixed)
version and absent in the relaxed (bug) version**.

## Verdict

**YES — RCU reproduces the UAF-style safety gating.**

Making the exit write a RELEASE store adds exactly three future (Φ) edges, all
into the exit write `g.16#0`, and removes none. They are present in 18/18 fixed
futures and 0/18 relaxed futures. The release order is what creates the
dependence edges that order the loop body's dereference/RMW before the exit
write; under a relaxed exit write those orderings are absent.

## Release-store syntax (verified)

`*(rrcu + rtid) :rel= 0;`

The `:rel=` token is the release-store assignment. Confirmed two ways:
- working example: `mordor/programs/uaf-bug-fixed.lit` uses `*rcu :acq= 1;` and
  `*rcu :rel= 0;`.
- lexer: `mordor/src/lexer.mll` maps `":rel="` → `Parser.COLONREL`
  (and `":acq="`, `":rlx="`, `":sc="` analogously). `isa_export.ml` emits the
  store with `"order": "rel"`.

The fixed fixture `rcu-inc-loop-fixed.lit` is byte-identical to
`rcu-inc-loop.lit` except line 24/25: the exit write `*(rrcu + rtid) := 0;`
becomes `*(rrcu + rtid) :rel= 0;`. Confirmed in the emitted JSON: `g.16` command
is `{"op":"WritePtr","order":"rel", ...}` in fixed vs `"order":"rlx"` (implicit)
in relaxed.

## Run commands + cost (both at `--step-counter 2`, `--output-mode isa`)

```bash
BIN=/home/christian/workspace/mordor/_build/default/cli/main.exe
cd /home/christian/workspace/mordor

# relaxed (bug)
"$BIN" futures --single .../rcu/rcu-inc-loop.lit       --step-counter 2 \
  --output-mode isa --output-file .../rcu/rcu-inc-loop_isa_sc2.json

# fixed (I6 release)
"$BIN" futures --single .../rcu/rcu-inc-loop-fixed.lit --step-counter 2 \
  --output-mode isa --output-file .../rcu/rcu-inc-loop-fixed_isa_sc2.json
```

| run | result | wall | peak RSS | events | executions |
|---|---|---|---|---|---|
| relaxed `rcu-inc-loop.lit`        | exit 0 | 2:44.90 | 2.03 GB | 18 | 18 |
| fixed `rcu-inc-loop-fixed.lit`    | exit 0 | 0:24.83 | 1.21 GB | 18 | 18 |

(Same event/execution counts; the fixed run is faster and lighter because the
extra release-ordering prunes the search.) Debug stderr was redirected to
`/tmp/*_sc2_err.log`.

## Discriminator edge(s)

Event labels are `g.<stmt>@<loop_id>:<iter>#<event>` for loop-body events and
`g.<stmt>#<event>` for the post-loop exit write. The retry loop is `loop_id 1`.
Relevant statements (from the fixed JSON program tree):

- `g.13@1:1#0` — the dereference `rv := *rs` (`ReadPtr`, R#0). **This is the last
  loop-body load of the protected location chain.**
- `g.14@1:1#0` — `*rn := rv+1` (`WritePtr`, W#0).
- `g.15@1:1#2` — the `Cas`'s write sub-event (W#2).
- `g.16#0` — the exit write `*(rrcu+rtid) := 0` (W#0; release in fixed, relaxed
  in bug). This is the RCU "leave critical section / publish quiescent" store.

Edges present ONLY in FIXED (release), absent in RELAXED:

| edge | meaning | relaxed | fixed |
|---|---|---|---|
| `g.13@1:1#0 → g.16#0` | last loop-body deref `rv:=*rs` → exit write | ABSENT (0/18) | PRESENT (18/18) |
| `g.14@1:1#0 → g.16#0` | `*rn:=rv+1` → exit write | ABSENT (0/18) | PRESENT (18/18) |
| `g.15@1:1#2 → g.16#0` | Cas write → exit write | ABSENT (0/18) | PRESENT (18/18) |

Edges present ONLY in RELAXED: **none** (R−F = ∅).

The **primary discriminator named by the hypothesis** is
`g.13@1:1#0 → g.16#0`: the read in the loop body (`rv := *rs`, the dereference of
the just-fetched pointer) ordered before the post-loop exit write. It is exactly
present-in-fixed / absent-in-relaxed. The other two (`g.14`, `g.15` → exit) are
the same gating phenomenon on the adjacent body write and the Cas write.

Edge totals: relaxed 64 distinct edges, fixed 67 — the delta is precisely these
3 added edges, nothing else changes.

## How to reproduce the comparison

```python
import json
def alledges(f):
    return {(e[0],e[1]) for fut in json.load(open(f))['futures'] for e in fut['edges']}
R=alledges('rcu-inc-loop_isa_sc2.json'); F=alledges('rcu-inc-loop-fixed_isa_sc2.json')
print(sorted(F-R))  # the 3 discriminator edges
print(sorted(R-F))  # []
```

## Artifacts

- `rcu-inc-loop.lit` — relaxed (bug) fixture.
- `rcu-inc-loop-fixed.lit` — fixed (I6 release) fixture (`:rel=` on exit write).
- `rcu-inc-loop_isa_sc2.json` — relaxed Φ output, sc=2 (regenerated 2026-06-09).
- `rcu-inc-loop-fixed_isa_sc2.json` — fixed Φ output, sc=2.
