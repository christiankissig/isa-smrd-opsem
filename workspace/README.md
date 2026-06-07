# workspace — spike & work artifacts (not part of any session)

Non-source artifacts that fall out along the rework path. Nothing here is imported by an
Isabelle session; it is kept for provenance and reproducibility.

- **`spikes/`** — de-risking spikes. See `spikes/uaf-bridge/` for the validated mordor → Φ
  bridge (W3/Spike A).
- **`snapshots/`** — the ~49 `OpSem_definite.thy_step*` / `_repaired` iterative-repair
  snapshots of the `wfs_2_preserved` proof, and `*.thy_new` candidate proofs. Kept until
  §2 decides the fate of `OpSem_definite`; then prune to the winner (REWORK_PLAN.md → Phase 7).
- **`scratch/`** — throwaway theories (`current.thy`, `RCU_test.thy`), superseded ROOT
  variants (`ROOT.old`, `ROOT~`), and editor backups.
- **`notes.txt`, `proof-structure.otl`, `generated_futures.txt`** — working notes / outputs.
