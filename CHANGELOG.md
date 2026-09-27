# Changelog

All notable changes to this project are documented in this file. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/).

## [0.1.0] - 2026-09-27

First public release.

### Added

- **Core**: labels, memory orders, expressions, the abstract action alphabet, the abstract
  command language, and the `LABEL is INSTRUCTION` program digest.
- **MemSem**: a thin sMRD memory semantics, with program state
  σ = (viswrite, memory, φ, RF) and action effects σ ⤳ₜ σ'.
- **EventStruct**: preserved program order, semantic dependency, executions, futures Φ,
  histories, `horizonΦ_H`, and episodicity.
- **OpSem**: the Episodic operational semantics, with command → action rules, the step
  relation `step prog Φ` contextual in a future set Φ, and a client locale.
- **OwickiGries**: a generic Owicki-Gries framework over an abstract transition system, with
  its soundness proof (`og_safety`, `og_sound`).
- **Ownership**: an instantiation of OwickiGries in which ownership disjointness discharges
  interference freedom (`ownership_interference_free`).
- **Ownership_UAF**: use-after-free safety as a corollary of the ownership discipline
  (`uaf_safe`).
- **UAF_Bug** client: the minimal two-thread use-after-free example. `uaf_reachable_bug`
  shows the use-after-free is reachable in the buggy program, and `uaf_excluded_fixed` shows
  it is excluded in the fixed program, over a Φ enriched with the release handshake edge.
- **RCU_Client**: RCU as program-as-data over Core, covering the loop-free fragment.
- `scripts/generate_phi.py`: renders MoRDor `isa`-mode JSON into Isabelle theories holding
  the program digest and the future set Φ, and derives release handshake edges from
  MoRDor's per-execution reads-from relation.
- `docs/MORDOR_ISA_FORMAT.md`: the MoRDor ↔ Isabelle interchange format, schema v0.1.
- `make` targets per session, `make gate` for a clean build of every session, and a CI
  workflow running `make ci` on the official Isabelle2025 release.

All sessions listed in the Makefile build without `sorry` and without `quick_and_dirty`.

[0.1.0]: https://github.com/christiankissig/isa-smrd-opsem/releases/tag/v0.1.0
