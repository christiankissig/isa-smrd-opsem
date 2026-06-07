# Spike A / W3 — mordor → Φ bridge (UAF example) — VALIDATED 2026-06-07

Validates the pipeline that turns a mordor analysis into a labelled future set Φ, on the
paper's minimal use-after-free example. See REWORK_PLAN.md → §5.

## Commands (mordor at /home/christian/workspace/mordor)
```
BIN=mordor/_build/default/cli/main.exe
$BIN executions --single mordor/programs/uaf-bug.lit       --output-mode json --output-file uaf_exec.json
$BIN futures    --single mordor/programs/uaf-bug.lit       --output-mode json --output-file uaf_futures.json
$BIN executions --single mordor/programs/uaf-bug-fixed.lit --output-mode json --output-file uaf_fixed_exec.json
$BIN futures    --single mordor/programs/uaf-bug-fixed.lit --output-mode json --output-file uaf_fixed_futures.json
python3 spike_join.py
```

## `isa` output (the specified interchange format — mordor-side implemented 2026-06-07)
- `uaf_isa.json`, `uaf_fixed_isa.json`, `cas_aba_isa.json` — `futures --output-mode isa` per
  `docs/MORDOR_ISA_FORMAT.md` v0.1. uaf-bug/fixed reproduce the bug/fix discriminating edge;
  cas_aba shows RMW sub-events + loop-iteration labels. Command:
  `mordor futures --single P.lit --output-mode isa --output-file P_isa.json`.

## Files
- `uaf_exec.json`, `uaf_fixed_exec.json` — `executions` export: labelled events
  (`id`, `type` ∈ I/A/W/R/D/T, `location`, `rval`/`wval`, `rmod`/`wmod`, `thread`) **+**
  relations `po/dp/ppo/rf/rmw` per execution. **The one-stop source for Φ.**
- `uaf_futures.json`, `uaf_fixed_futures.json` — `futures` export: `(e1,e2)` integer pairs
  (non-strict JSON — normalise `()`→`[]`). Used only as a cross-check.
- `spike_join.py` — joins `executions` into a labelled Φ = `{ identity ∪ (ppo∪dp) per exec }`,
  cross-checks vs `futures`, and reports the bug/fix discriminating edge. Seed for the real
  generator `scripts/generate_phi.py`.

## Result
- **Bridge sound:** every execution's `identity ∪ (ppo∪dp)` equals a `futures` entry —
  **8/8** (bug), **2/2** (fixed).
- **Reproduces the paper's fix:** bug has deref `R rC` → exit `W rcu` **absent** from ppo
  (⇒ UAF); fixed has the exit `wmod=Release` and that ppo edge **present** (⇒ free gated) —
  exactly `tab-fut-step-bug` vs `-fix`. Both run < 1 s.
- Symbolic locations are CJK glyphs: `一` = rC, `二` = rcu.
