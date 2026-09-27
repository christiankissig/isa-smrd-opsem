# Core (reusable ★ — AFP candidate)

Shared vocabulary for the whole stack: actions, labels (`pc · loopfun · iter`),
memory orders, locations, values, expressions. No semantics — just the types both
`MemSem` (actions/σ) and `EventStruct` (Φ over labelled actions) depend on, so they
don't depend on each other.

**Status:** built, zero `sorry`. The action/label interface is frozen per
`docs/SPIKE_B_label_digest_design.md`.
