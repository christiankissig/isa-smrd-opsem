(* Legacy RCU session.

   SUPERSEDED by the per-layer reworked sessions (Core / MemSem / EventStruct /
   OpSem / OwickiGries / Ownership and the clients/* sessions); see the per-layer
   ROOT files and the Makefile.

   The pre-rework RCU futures-enumeration development that this session used to
   build (RCU_state / RCU_prog / RCU_futures / RCU_futures_inequalities /
   RCU_wm_proofs_old_* and the I/R/S step proofs) has been RETIRED -- it was the
   "wrong future set" (114-ctor enumeration, the I7 ~12000-sorry explosion),
   subsumed by the Episodic spine.  The legacy SEFM imports it depended on
   (PSem.thy, OpSem_definite.thy) have likewise been retired; the reworked
   MemSem session folds their content in (see MemSem/MemSem.thy).

   What survives in clients/RCU are the two GENERATED MoRDor digests
   (RCU_prog_digest, RCU_inc_loop_digest) -- the structural source-of-truth for
   the reworked RCU client.  They import only Main, so this session builds them
   for archival / reference; the real RCU client is being rebuilt in the spine
   style over the Core/OpSem types. *)

session MRD_C11_RCU = "HOL" +
  directories
    "clients/RCU"
  theories
    RCU_prog_digest
    RCU_inc_loop_digest

  export_files
    "./"
