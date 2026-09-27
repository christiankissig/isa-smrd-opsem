# Spike D — Frozen triage table + sorry/oops baseline

**Date frozen:** 2026-06-07
**Scope:** every `.thy` under `clients/RCU/` (60), `MemSem/` (2), `c11_opsem/` (8) = **70 theory files**.
This document freezes the per-file disposition + the sorry/oops baseline for tracking the burndown.

Dispositions: **KEEP** (reuse ~as-is) · **ADAPT** (refactor into a target layer) · **RETIRE** (delete; subsumed)
· **REPLACE** (delete; rebuilt differently) · **EVAL** (decision pending a spike) · **SPLIT** (parts go different ways).

---

## 1. Sorry / oops baseline (the §9 eval anchor)

**Grand total: 12342 `sorry`, 2 `oops`** (counted with `grep -oE '\bsorry\b' / '\boops\b'`).

### Totals by disposition
| Disposition | files | sorry | oops |
|---|---:|---:|---:|
| RETIRE      | 47 | 12330 | 1 |
| REPLACE     |  9 |     3 | 0 |
| ADAPT       |  4 |     7 | 1 |
| EVAL        |  6 |     2 | 0 |
| SPLIT       |  1 |     0 | 0 |
| KEEP        |  3 |     0 | 0 |
| **Total**   | **70** | **12342** | **2** |

(KEEP = the 3 c11_opsem litmus files with zero sorries that are RETIRE-from-build but proof-clean;
they carry no debt. The MessagePassing `oops` and the surrey/proof-rules files are folded into RETIRE/EVAL below.)

### Biggest contributors (all in the RETIRE `RCU_wm_proofs_old*` explosion)
| File | sorry |
|---|---:|
| `RCU_wm_proofs_old_I7_preserves_pre_block_global_pre.thy` (13790 lines) | **12013** |
| `RCU_wm_proofs_old_I8_preserves_pre_block_global_pre.thy` | 109 |
| `RCU_wm_proofs_old_I6_preserves_pre_block_global_pre.thy` | 97 |
| `RCU_wm_proofs_old_showing_block_cond_pres_local.thy` | 41 |
| `RCU_wm_proofs_old_showing_det_block_pres_global.thy` | 26 |
| `RCU_wm_proofs_old_I5_preserves_pre_block_global_pre.thy` | 12 |
| `RCU_wm_proofs_old_I11_preserves_block_cond_global_pre.thy` | 10 |
| `RCU_wm_proofs_old_I12_preserves_pre_block_global_pre.thy` | 6 |
| `RCU_local.thy` | 7 (+1 oops) |
| `RCU_futures.thy`, `RCU_steps.thy`, `...local_2`, `sigma_obs_preserved_forall` | 3 each |
| `RCU_wm_proofs_old_I11_preserves_pre_block_global_pre.thy` | 3 |
| `MemSem/OpSem_definite.thy` | 2 |
| `I13`, `method`, `..._FAAZ`, `RCU_aux` | 1 each |

**Key fact for §9:** ~99.8% of all debt (12326 / 12342) lives in the RETIRE
`RCU_wm_proofs_old*` per-future explosion; **12013 of those (97%) are a single file (I7)**.
Once the §6 RETIRE rows are deleted, the surviving debt is only **12 sorries**:
`RCU_local` (7), `RCU_futures` (3, REPLACE — disappears with `Φ_RCU`), `OpSem_definite` (2).
The "12 000-sorry explosion" the rework targets is therefore concentrated and deletable, not diffuse.

### The 2 oops
- `clients/RCU/RCU_local.thy` (1 oops, `po_local_critsec_isar` dead-end) — ADAPT host.
- `c11_opsem/MessagePassing.thy` (1 oops) — RETIRE-from-build litmus example.

---

## 2. Frozen disposition table

### Sessions / submodule / build
| Artifact | §6 | Frozen | Target / note |
|---|---|---|---|
| `c11_opsem` submodule (`MRD_C11_OPSEM`) | EVAL→dissolve | **EVAL→dissolve** | AFP forbids submodule; absorb needed parts. **Resolvable now** (mechanics), but content fate gated by Spike C. |
| `ROOT` / `ROOT.old` / `ROOT~` | REPLACE | **REPLACE** | Per-session ROOTs (§3). |

### `c11_opsem/` (8 thy)
| File | §6 | Frozen | sorry/oops | Note |
|---|---|---|---|---|
| `OpSem.thy` (surrey RC11) | EVAL §2 | **EVAL (Spike C)** | 0/0 | Basis of `MemSem` or replaced — gated on SMRD eval. |
| `OpSem_Proof_Rules.thy` | EVAL | **EVAL (Spike C)** | 0/0 | Likely ADAPT into MemSem/OpSem; salvage value high (read/write/update_trans rules). |
| `LB`, `LBDataAddCtrl`, `MessagePassing`, `PartialConditional`, `RNG`, `SimpleLBDataAddCtrl` | RETIRE from build | **RETIRE** (keep ≤2 as regression examples) | 0/0 except `MessagePassing` 0/**1 oops** | Litmus; drop from build. |

### `MemSem/` (2 thy) — SEFM imports
| File | §6 | Frozen | sorry/oops | Note |
|---|---|---|---|---|
| `PSem.thy` | EVAL §2 | **EVAL (Spike C)** | 0/0 | Fold provenance into MemSem or RETIRE. |
| `OpSem_definite.thy` | EVAL §2 | **EVAL (Spike C)** | **2**/0 | The 2 sorries are `wfs_2_preserved` (l.30/31: `wfs σ'`, writes-not-covered). §9 warm-up *only if §2 keeps the file*. Repair `*_step*`/`_repaired` snapshots (untracked, ~30) → RETIRE. |

### RCU program model
| File | §6 | Frozen | sorry/oops | Note |
|---|---|---|---|---|
| `RCU_state.thy` | SPLIT | **SPLIT** | 0/0 | pc type (drop S7) + registers/ownership → Core/RCU; `Futures`+`futures_list`+`futures` field → RETIRE. |
| `RCU_atomics.thy` | ADAPT | **ADAPT** | 0/0 | Refactor into `OpSem` command instances. |
| `RCU_prog.thy` | REPLACE | **REPLACE** | 0/0 | By `step` + `prog_RCU` data. |
| `RCU_mrd.thy` | ADAPT | **ADAPT** | 0/0 | Align ppo/DP to mordor → EventStruct. |
| `RCU_futures.thy` | REPLACE | **REPLACE** | **3**/0 | → generated `Φ_RCU`; the 3 sorries vanish with the file. |
| `RCU_futures_inequalities.thy` (12113 lines) | RETIRE | **RETIRE** | 0/0 | Deleted with `futures_to_line_unique`. |

### RCU invariants / preconditions / proofs
| File | §6 | Frozen | sorry/oops | Note |
|---|---|---|---|---|
| `RCU_maininvs.thy` | REPLACE | **REPLACE** | 0/0 | Re-express over (σ,ρ,H). |
| `RCU_preconds.thy` | RETIRE | **RETIRE** | 0/0 | Per-history preconds subsumed. |
| `RCU_preconds_2.thy` | RETIRE | **RETIRE** | 0/0 | Older copy. |
| `RCU_local.thy` | EVAL→ADAPT/RETIRE | **ADAPT/RETIRE** (resolvable now) | **7**/**1 oops** | Salvage local lemmas (see §3); drop the rest. Not Spike-C-gated. |
| `RCU_aux.thy` | RETIRE | **RETIRE** | **1**/0 | `futures_one_step` scratch. |
| `RCU_steps.thy` | RETIRE | **RETIRE** | **3**/0 | Superseded per-line `step_I*` lemmas. |
| `RCU_I_steps.thy` / `RCU_R_steps.thy` / `RCU_S_steps.thy` | REPLACE | **REPLACE** | 0/0 | One step-preserves-invariant proof. |
| `RCU_steps_unified.thy` | REPLACE | **REPLACE** | 0/0 | Top-level safety theorem. |
| `RCU_wm_prelim.thy` | ADAPT | **ADAPT** | 0/0 | Salvage WM lemmas (see §3). |
| `RCU_wm_preblock.thy` | REPLACE | **REPLACE** | 0/0 | pre/post-block = horizon discipline. *(Note: contains a duplicated `I5_preserves_pre_block` lemma name — harmless, file is being deleted.)* |
| `RCU_wm_proofs.thy` (umbrella) | RETIRE | **RETIRE** | 0/0 | — |
| `RCU_wm_proofs_old.thy` (master, 42 lines) | RETIRE | **RETIRE** | 0/0 | Umbrella import of the per-lemma split. |
| `RCU_wm_proofs_old_*.thy` (40 per-lemma files) | RETIRE | **RETIRE** | **12326**/0 | Admitted per-future explosion; see §1 contributors. Includes I1–I14 (I11×3), R1–R5, S1–S7, `cas_res`, `covered_exists_after_step`, `finished`, `method`, `showing_block_cond_pres_{global,local,local_2}`, `showing_det_block_pres_global{,_CAS,_FAAZ}`, `sigma_obs_preserved_forall`, `supporting_block_cond_sep`. |

### Scripts / scratch (not .thy — listed for completeness)
`scripts/generate_futures*.py` → **REPLACE** by `generate_phi.py`; `RCU_test.thy`/`current.thy` (in `workspace/scratch/`) → **RETIRE**; editor backups / `*.thy_new` / repair snapshots → **RETIRE**.

---

## 3. Salvage list (ADAPT rows — lift these lemmas before retiring the host)

### `RCU_wm_prelim.thy` → `MemSem` / `OpSem` support (26 lemmas, **0 sorry** — clean salvage)
Worth lifting (failed/successful-CAS and `d_obs`/`c_obs` preservation, the SMRD-relevant CAS reasoning):
- `Failed_CAS_preserves_d_obs_1`, `Failed_CAS_preserves_d_obs_supporting_for_later`, `Failed_CAS_preserves_d_obs_3`
- `Succ_CAS_preserves_d_obs_1`, `CAS_preserves_d_obs_7`, `CAS_preserves_d_obs_8`, `CAS_preserves_d_obs_9`
- `relating_step_to_update_trans_1`, `d_obs_other_representation_2` (Rule DV-Other)
- `FAAZ_expanded_is_Up`, `FAAZ_step_is_Up` (FAAZ↔Up bridge — relevant to CAS-acquire-only, §2 Q4)
- `c_obs_t_Rd_pres_c_obs`, `c_obs_tdash_Rd_pres_c_obs`
- `shows_WM_local_corr_1_I5I7`, `_1_I6`, `_1_I8_to_I11`, `_2`, `_3`, `_supp2/3/4` — RCU-specific; lift only the generic memory-model cores, drop the I-step-tied parts.
- Drop: `testingthisone3..7` (scratch).

### `RCU_local.thy` → salvage then RETIRE the rest (7 sorry + 1 oops)
- Salvageable definitions worth re-expressing over (σ,ρ,H): `prog_future_precond_inv`, `critsec_futures`, the `pre_I*/pre_R*/pre_S*` per-PC precondition shapes (l.335–710) — re-keyed to labels in the new client (drop S7).
- `relate_history_to_future_in_prog_state` (1 sorry), `po_local`, `po_local_critsec` (3 sorries + 1 oops dead-end `po_local_critsec_isar`) — these are the "unpacking singletons in futures" admits; **do not lift**, they are artifacts of the retired futures field. RETIRE.

### `RCU_atomics.thy`, `RCU_mrd.thy` (0 sorry)
- `RCU_atomics`: ownership-transfer / allocation atomics → re-express as `OpSem` `command` instances (operands as args).
- `RCU_mrd`: ppo/DP relation defs → align to mordor's `ppo`/`dp` in `EventStruct`.

---

## 4. EVAL rows — Spike C (SMRD) dependence

**Gated on Spike C / §2 (SMRD memory eval) — decide before MemSem is built:**
- `c11_opsem/OpSem.thy` (surrey RC11) — keep/relax/replace.
- `c11_opsem/OpSem_Proof_Rules.thy` — ADAPT target depends on which σ survives.
- `MemSem/PSem.thy` — fold into MemSem vs retire.
- `MemSem/OpSem_definite.thy` — retire vs fold; finishing its 2 `wfs_2_preserved` sorries is worthwhile **only if §2 keeps it** (it is otherwise the §9 tool-validation warm-up regardless).

**Resolvable NOW (not Spike-C-gated):**
- `RCU_local.thy` EVAL→ADAPT/RETIRE — decided here (salvage defs §3, retire futures-tied lemmas).
- `c11_opsem` submodule dissolution — mechanical (own session); only *which content* is absorbed waits on Spike C.
- All litmus RETIRE-from-build rows.

---

## 5. Disposition corrections / flags after inspection

1. **No row is wrong** — every §6 disposition holds after file inspection. Refinements only:
2. **`RCU_local` EVAL resolved to ADAPT(salvage defs)+RETIRE(futures-tied lemmas)** — §6 left it `EVAL→ADAPT/RETIRE`; it does **not** depend on Spike C and is frozen here as resolved.
3. **Counts confirmed against Appendix A:** I7 = **12013** (Appendix "≈12 000" ✓); `RCU_futures_inequalities` = **12113 lines** (Appendix "12,113" ✓); master `RCU_wm_proofs_old.thy` = 42 lines (umbrella, 0 sorry).
4. **§6 names a `showing_det_block_pres_global_FAAZ` file** (1 sorry) present on disk and covered by the blanket `RCU_wm_proofs_old*` RETIRE row — confirmed, no separate row needed.
5. **`RCU_wm_preblock.thy` has a duplicated `I5_preserves_pre_block` lemma name** (l.95 and l.146) — cosmetic only; file is REPLACE/delete, so no action.
6. **Surviving post-RETIRE debt is just 12 sorries** (RCU_local 7, RCU_futures 3→vanishes with Φ_RCU, OpSem_definite 2) — this is the honest burndown floor the §9 metric starts from after the pure-deletion sweep (W4).
