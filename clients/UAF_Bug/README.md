# Client: UAF-bug

The paper's minimal 2-thread use-after-free example, as an instantiation of `OpSem`:
`prog_uaf_bug` / `prog_uaf_fixed` (labelled `command` data, from `uaf-bug.lit` /
`uaf-bug-fixed.lit`) + `Φ_uaf{,_fixed}` (generated from mordor — bridge already validated,
see `workspace/spikes/uaf-bridge/`).

**Goal:** bug variant *reaches* a config where `Dealloc rC` is enabled while the deref
`Read rC` is pending (UAF reachable); fixed variant *excludes* it (release edge keeps the
free out of `horizonΦ_{H₀}`) — matching the paper's `tab-fut-step-bug` / `-fix`.

**Status:** to be built fresh (REWORK_PLAN.md → Phase 4). Empty scaffolding.
