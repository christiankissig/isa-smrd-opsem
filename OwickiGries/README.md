# OwickiGries (reusable ★ — **first AFP target**)

A generic Owicki-Gries / rely-guarantee program logic over an **abstract transition system**
(a locale: `fixes` state + atomic step; with its own standard interleaving semantics and a
self-contained **soundness** proof). Assertions, parallel composition, interference freedom,
proof rules.

**Critical:** independent of the Episodic `OpSem` — depends only on HOL (no `Core`/`MemSem`/
`EventStruct`/`OpSem`/`c11_opsem`/SEFM imports). The Episodic `OpSem` connects later as one
*interpretation* (in `clients/RCU`). See REWORK_PLAN.md → §3 (priority 1), Phase 5.

**Status:** to be built fresh. Empty scaffolding.
