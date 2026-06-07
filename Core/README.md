# Core (reusable ★ — AFP candidate)

Shared vocabulary for the whole stack: actions, labels (`pc · loopfun · iter`),
memory orders, locations, values, expressions. No semantics — just the types both
`MemSem` (actions/σ) and `EventStruct` (Φ over labelled actions) depend on, so they
don't depend on each other.

**Status:** to be built fresh (REWORK_PLAN.md → Phase 1). Empty scaffolding.
**Freeze the action/label interface early** (Spike B) so `MemSem ∥ EventStruct` proceed
without churn.
