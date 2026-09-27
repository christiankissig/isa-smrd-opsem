# OpSem — Episodic operational semantics (reusable ★ — AFP candidate)

The paper's core: the `command` datatype (one constructor per appendix rule) + generic
per-command effect rules (emitting actions), config `(σ, ρ, H)`, and the inductive
transition relation contextual in the future set Φ:

```
prog, Φ ⊢ (σ, ρ, H) → (σ', ρ', H')
```

with the four future-stepping rules (non-lb/non-branch, lb-with-reset, then, else) and a
**client locale** (`fixes prog Φ`). Clients (`clients/UAF_Bug`, `clients/RCU`) are
interpretations.

**Status:** built, zero `sorry`.
