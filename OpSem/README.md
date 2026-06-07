# OpSem — Episodic operational semantics (reusable ★ — AFP candidate)

The paper's core: the `command` datatype (one constructor per appendix rule) + generic
per-command effect rules (emitting actions), config `(σ, ρ, H)`, and the inductive
transition relation contextual in the future set Φ:

```
prog, Φ ⊢ (σ, ρ, H) → (σ', ρ', H')
```

with the four future-stepping rules (non-lb/non-branch, lb-with-reset, then, else) and a
**client locale** (`fixes prog Φ`). Clients (`clients/UAF_Bug`, `clients/RCU`) are
interpretations. *(Stretch: finiteness/soundness/completeness meta-theorems.)*

**Status:** to be built fresh (REWORK_PLAN.md → Phase 3). Empty scaffolding.
AFP submission **undecided** (on the fence) — keep AFP-capable but uncommitted.
