# MemSem — memory semantics (reusable ★ — AFP candidate)

Program state σ (`viswrite`, `memory`, `φ` path-predicate, `RF`) and action effects
`σ ⤳ₜ σ'` (read/write/alloc/dealloc/fence).

**Status:** built, zero `sorry`. A thin SMRD σ with ordering delegated to Φ, replacing the
earlier RC11 memory imports (see `docs/SPIKE_C_smrd_memsem.md`). SMRD admits the UAF that
RC11 coherence forbids.
