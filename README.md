# rcu-c11-opsem

[![build](https://github.com/christiankissig/rcu-c11-opsem/actions/workflows/build.yml/badge.svg)](https://github.com/christiankissig/rcu-c11-opsem/actions/workflows/build.yml)

Isabelle/HOL formal verification that the **RCU** (Read-Copy-Update) algorithm has
**no use-after-free** under a **C11 weak-memory operational semantics** with the
**Episodic Loops / MRD** (Modified Represents Dependence) model, where the transition
relation is contextual in a fixed future set Φ:

```
prog, Φ ⊢ (σ, ρ, H) → (σ', ρ', H')
```

The development is a **stack of self-contained, reusable Isabelle sessions**, several
intended for the **Archive of Formal Proofs (AFP)**, with Φ generated from the **mordor**
event-structure tool. It replaces an earlier monolithic proof that encoded futures as an
enumerated datatype (which exploded the proof goals); that legacy development has been
retired.

## Status

The whole reusable spine builds **zero `sorry`** under the strict AFP gate
(`make gate`: a from-clean rebuild with **no** `quick_and_dirty`).

| Layer / session | State |
|---|---|
| **OwickiGries + Ownership** (Track A — first AFP target) | ✅ **proven**, zero `sorry`, non-`quick_and_dirty`; AFP metadata finalised, PDFs render |
| **Core** (labels, actions, commands, digest) | ✅ built, zero `sorry` |
| **MemSem** (thin SMRD σ + action effects) | ✅ built, zero `sorry` |
| **EventStruct** (ppo, DP, Φ, horizon, episodicity) | ✅ built, zero `sorry` |
| **OpSem** (command→action rules, `step prog Φ`) | ✅ built, zero `sorry` |
| **UAF_Bug** client (paper's minimal bug/fix) | ✅ `uaf_reachable_bug` **proven**; `uaf_excluded_fixed` **proven** over a handshake-enriched Φ (see caveat) |
| **RCU_Client** (`prog_RCU` as program-as-data over Core) | ✅ built; loop-free fragment only — **no end-to-end no-UAF theorem yet** |
| `Φ_RCU` generation (mordor bridge) | ⏳ open: derive the cross-thread handshake edge in the generator; drive the full multi-thread Φ to termination |
| Legacy RCU proofs (`MRD_C11_RCU`) | 🗄️ **retired** (deleted); only the generated mordor digests survive |

## Architecture

Bottom-up; each reusable layer (★ = AFP-candidate) imports only layers below it.

```
Core ★        labels (pc·loopfun·iter), memory orders, expressions,
              the abstract action alphabet, the abstract command language,
              and the digested `LABEL is INSTRUCTION` program.  No semantics.
MemSem ★      σ = (viswrite, memory, φ, RF) + action effects σ ⤳ₜ σ'  (SMRD).
EventStruct ★ ppo, DP, executions, futures Φ, histories, horizonΦ_H, episodicity.
OpSem ★       command→action rules + inductive `step prog Φ`; client locale.

OwickiGries ★ + Ownership ★   — INDEPENDENT vertical (1st AFP target):
              generic Owicki-Gries over an abstract transition system + soundness,
              with Ownership as a concrete instantiation (ownership ⟹ non-interference,
              use-after-free safety).  Depends only on HOL.

Clients:      UAF_Bug (paper's minimal bug/fix) · RCU_Client (RCU as program-as-data).
```

`OwickiGries`/`Ownership` are deliberately decoupled from the Episodic stack and meet it
only at the RCU client's interpretation theory — which is what lets them be the first AFP
submission. Full rationale in [`docs/W1_owicki_gries_design.md`](docs/W1_owicki_gries_design.md).

## Building

Requires **Isabelle2025-vsce** (the [isabelle-emacs](https://github.com/m-fleury/isabelle-emacs)
fork) with a built `HOL` heap (`isabelle build -b HOL`). The reworked layers also build on the
official **Isabelle2025** (see CI). Theory sources use ASCII Isabelle symbol notation
(`\<forall>`, `\<open>…\<close>`), not raw Unicode glyphs.

```bash
make all         # build the whole reworked stack (non-q&d): Core, MemSem,
                 #   EventStruct, OpSem, OwickiGries, Ownership, UAF_Bug, RCU_Client
make core        # Core         (shared vocabulary)
make memsem      # MemSem        (thin SMRD memory semantics; needs Core)
make eventstruct # EventStruct   (event structures, Φ, horizon; needs Core)
make opsem       # OpSem         (Episodic step relation; needs MemSem + EventStruct)
make uaf         # UAF_Bug       (paper's bug/fix client; needs OpSem)
make rcu-client  # RCU_Client    (RCU program-as-data; needs OpSem)
make og          # OwickiGries
make ownership   # Ownership     (needs OwickiGries); alias: make track-a
make gate        # from-CLEAN rebuild of the whole stack — the zero-sorry AFP gate
make ci          # what CI runs (strict gate on mature layers + spine compile-check)
make rcu         # the legacy MRD_C11_RCU session (now just the generated digests)
make dry         # confirm the reworked layers are up to date (no recompile)
make clean       # remove editor backups / autosaves
make help        # list targets
```

Override the prover binary with `make ISABELLE=/path/to/isabelle <target>`.

Each layer is its own session; cross-layer imports use session-qualified theory
names (e.g. `imports "Core.Core"`, `imports "OpSem.OpSem"`). Equivalent raw invocations:
`isabelle build -d Core Core`,
`isabelle build -d Core -d MemSem MemSem`,
`isabelle build -d OwickiGries -d Ownership Ownership`.

## Repository layout

```
Core/            ★ shared vocabulary (Core.thy + ROOT)             [built]
MemSem/          ★ thin SMRD memory semantics (MemSem.thy + ROOT)  [built]
EventStruct/     ★ event-structure semantics (EventStruct.thy + ROOT)  [built]
OpSem/           ★ Episodic operational semantics (OpSem.thy + ROOT)   [built]
OwickiGries/     ★ generic Owicki-Gries framework (proven) + ROOT + metadata
Ownership/       ★ ownership instantiation (proven) + ROOT + metadata
clients/UAF_Bug/   minimal use-after-free example (paper's headline)
clients/RCU/       RCU_Client.thy (program-as-data) + generated mordor digests + ROOT
c11_opsem/         base C11 memory model (formerly a git submodule; now in-tree)
scripts/           Φ generators (generate_phi.py)
workspace/         non-source artifacts: spikes/ (mordor→Φ bridge), snapshots/, scratch/
docs/              SPIKE_*, W1 design, MORDOR_ISA_FORMAT, PARALLEL_WORKSTREAMS
ROOT               legacy session MRD_C11_RCU (builds only the surviving digests)
Makefile           build targets (above)
```

## The mordor → Φ bridge

Φ is computed by the **mordor** tool from the SMRD event structure and rendered into Isabelle
by `scripts/generate_phi.py`. The interchange format is specified in
[`docs/MORDOR_ISA_FORMAT.md`](docs/MORDOR_ISA_FORMAT.md); the validated UAF bridge lives under
`workspace/spikes/uaf-bridge/`.

**Open modeling obligation.** `uaf_excluded_fixed` is proven over a Φ enriched with the
cross-thread handshake DP edge `release-exit → reclaimer-read` (`t1.3#0 → t0.1#0`) that orders
the reclaimer's read after the reader's release. That edge is currently **added by hand with a
justification**, not emitted by single-program mordor `futures`; the retained
`uaf_config_fixed_horizon_counterexample` witnesses that the un-enriched Φ cannot exclude. The
next step is to **derive** the handshake edge in `generate_phi.py` (or via a MemSem
branch-feasibility argument) so the exclusion is end-to-end from the generator. Driving the full
multi-thread `Φ_RCU` to termination remains the other open task.

## Documentation

- [`docs/PARALLEL_WORKSTREAMS.md`](docs/PARALLEL_WORKSTREAMS.md) — workstream breakdown + dependency cut + status.
- [`docs/W1_owicki_gries_design.md`](docs/W1_owicki_gries_design.md) — the Owicki-Gries / Ownership design.
- [`docs/MORDOR_ISA_FORMAT.md`](docs/MORDOR_ISA_FORMAT.md) — the mordor↔Isabelle interchange format.
- `docs/SPIKE_{B,C,D}*` — label-digest, SMRD MemSem, and triage design notes.

## What remains

The reusable spine and both AFP-bound vertical entries are complete and zero-`sorry`. The
RCU end-to-end no-use-after-free theorem is still open; it needs (1) the handshake edge derived
in the generator (above), (2) the OpSem loop / `lb`-reset rule so `prog_RCU`'s `While` bodies
step, and (3) the full multi-thread `Φ_RCU`.
</content>
</invoke>
