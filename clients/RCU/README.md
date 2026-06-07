# Client: RCU (existing pre-rework formalization)

The full RCU algorithm formalization as it stood before the rework. **Most of this is to be
replaced or retired** per REWORK_PLAN.md → §6 triage; it is kept here as the RCU client area
while the new layered stack is built and RCU is re-instantiated on top of it.

Notable contents (see §6 for per-file disposition):
- **Program model:** `RCU_state` (PC labels + state record + the 114-ctor `Futures` datatype
  = the "wrong future set"), `RCU_atomics` (operand-baked atomics), `RCU_prog`, `RCU_mrd`.
- **Futures machinery (retire):** `RCU_futures`, `RCU_futures_inequalities` (12,113 lines).
- **Invariants/preconds:** `RCU_maininvs`, `RCU_preconds(_2)`, `RCU_local`, `RCU_aux`.
- **Step/safety proofs:** `RCU_I/R/S_steps`, `RCU_steps(_unified)`, `RCU_wm_*`,
  `RCU_wm_proofs_old_*` (admitted per-future explosion incl. I7 ≈ 12 000 sorries).

Target: a thin client = `prog_RCU` (labelled `command` data) + `Φ_RCU` (mordor) + no-UAF
proof via `Ownership`.
