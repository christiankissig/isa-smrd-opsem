# MemSem — memory semantics (reusable ★ — AFP candidate)

Program state σ (`viswrite`, `memory`, `φ` path-predicate, `RF`) and action effects
`σ ⤳ₜ σ'` (read/write/alloc/dealloc/fence).

**Currently holds the existing RC11/SEFM memory imports** awaiting the SMRD re-evaluation
(REWORK_PLAN.md → §2, Spike C):
- `PSem.thy` — provenance/memory model (`posem`).
- `OpSem_definite.thy` — definite operational semantics (has the `wfs_2_preserved` sorries).

The base C11 memory model is the `c11_opsem/` submodule (surrey: `mods`/`thrView`/
`visible_writes`/timestamp-mo/release-acquire) — **RC11 coherence**, to be evaluated against
SMRD (which admits the UAF that RC11 forbids). Outcome: likely a thinner SMRD σ with ordering
delegated to Φ. AFP-candidate once SMRD-faithful and zero-`sorry`.
