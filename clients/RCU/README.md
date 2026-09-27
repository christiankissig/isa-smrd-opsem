# Client: RCU

The pre-rework RCU futures-enumeration development that used to live here has been
**RETIRED** (W4 hygiene): it was the "wrong future set" (the 114-constructor
`Futures` enumeration), with the I7 per-future proof explosion (~12 000 sorries),
and it is subsumed by the reworked Episodic spine (Core / MemSem / EventStruct /
OpSem and the `clients/UAF_Bug` worked example).

Deleted in the retirement:
- **Program model:** `RCU_state`, `RCU_atomics`, `RCU_prog`, `RCU_mrd`.
- **Futures machinery:** `RCU_futures`, `RCU_futures_inequalities` (auto-generated,
  ~1 MB / 12 113 lines), plus `scripts/generate_futures_inequalities.py` and
  `create_scripts.zsh` (the dead generators for these files).
- **Invariants / preconds:** `RCU_maininvs`, `RCU_preconds(_2)`, `RCU_local`,
  `RCU_aux`.
- **Step / safety proofs:** `RCU_I/R/S_steps`, `RCU_steps(_unified)`, `RCU_wm_*`,
  `RCU_wm_proofs_old_*` (the admitted per-future explosion).
- The SEFM imports they depended on, `MemSem/PSem.thy` and
  `MemSem/OpSem_definite.thy` (their content is folded into `MemSem/MemSem.thy`).

What survives here:
- **`RCU_prog_digest.thy` / `RCU_inc_loop_digest.thy`** — the GENERATED mordor
  digests (provisional placeholder types, import only `Main`). These are the
  structural source-of-truth for the reworked RCU client and are built by the
  legacy `MRD_C11_RCU` session for archival/reference.
