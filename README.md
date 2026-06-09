# rcu-c11-opsem

Isabelle/HOL formal verification that the **RCU** (Read-Copy-Update) algorithm has
**no use-after-free** under a **C11 weak-memory operational semantics** with the
**Episodic Loops / MRD** (Modified Represents Dependence) model, where the transition
relation is contextual in a fixed future set Φ:

```
prog, Φ ⊢ (σ, ρ, H) → (σ', ρ', H')
```

The development is being re-engineered (the *rework*) from a monolithic, futures-as-an
-enumerated-datatype proof into a **stack of self-contained, reusable Isabelle sessions**,
several intended for the **Archive of Formal Proofs (AFP)**, with Φ generated from the
**mordor** event-structure tool. See [`REWORK_PLAN.md`](REWORK_PLAN.md) for the full plan
and [`docs/PARALLEL_WORKSTREAMS.md`](docs/PARALLEL_WORKSTREAMS.md) for the live workstream
status.

## Status

| Layer / session | State |
|---|---|
| **OwickiGries + Ownership** (Track A — first AFP target) | ✅ **proven**, zero `sorry`, builds without `quick_and_dirty` |
| **Core** (labels, actions, commands, digest) | ✅ built, zero `sorry` |
| MemSem · EventStruct · OpSem (Episodic stack) | ⏳ to do (unblocked) |
| `Φ_RCU` generation (mordor bridge) | ⏳ in progress (the schedule long-pole) |
| Legacy RCU proofs (`MRD_C11_RCU`) | 🗄️ retained, mostly `sorry`/superseded — being replaced layer by layer |

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

Clients:      UAF_Bug (paper's minimal bug/fix) · RCU (the full no-UAF proof).
```

`OwickiGries`/`Ownership` are deliberately decoupled from the Episodic stack and meet it
only at the RCU client's interpretation theory — which is what lets them be the first AFP
submission. Full rationale in [`docs/W1_owicki_gries_design.md`](docs/W1_owicki_gries_design.md).

## Building

Requires **Isabelle2025-vsce** (the [isabelle-emacs](https://github.com/m-fleury/isabelle-emacs)
fork) with a built `HOL` heap (`isabelle build -b HOL`). Theory sources use ASCII Isabelle
symbol notation (`\<forall>`, `\<open>…\<close>`), not raw Unicode glyphs.

```bash
make all        # build the reworked layers: Core + Track A  (no quick_and_dirty)
make core       # the Core session
make track-a    # Track A = OwickiGries + Ownership (the first AFP target)
make gate       # from-CLEAN rebuild of Core + Track A — the zero-sorry AFP gate
make rcu        # the legacy MRD_C11_RCU session (quick_and_dirty)
make dry        # confirm Core + Track A are up to date (no recompile)
make clean      # remove editor backups / autosaves
make help       # list targets
```

Override the prover binary with `make ISABELLE=/path/to/isabelle <target>`.

Equivalent raw invocations: `isabelle build -d Core Core`,
`isabelle build -d TrackA Track_A`,
`isabelle build -o quick_and_dirty=true -D . -d c11_opsem MRD_C11_RCU`.

## Repository layout

```
Core/            ★ shared vocabulary (Core.thy + ROOT)             [built]
MemSem/          ★ memory semantics (currently legacy PSem/OpSem_definite)
EventStruct/     ★ event-structure semantics (scaffolding)
OpSem/           ★ Episodic operational semantics (scaffolding)
OwickiGries/     ★ generic Owicki-Gries framework (proven) + ROOT
Ownership/       ★ ownership instantiation (proven) + ROOT
TrackA/ROOT        combined verification session for OwickiGries + Ownership
clients/RCU/       the existing RCU_*.thy (pre-rework client; being replaced)
clients/UAF_Bug/   minimal use-after-free example (paper's headline)
c11_opsem/         base C11 memory model (formerly a git submodule; now in-tree)
scripts/           Φ generators (generate_phi.py; old generate_futures* retiring)
workspace/         non-source artifacts: spikes/ (mordor→Φ bridge), snapshots/, scratch/
docs/              SPIKE_*, W1 design, MORDOR_ISA_FORMAT, PARALLEL_WORKSTREAMS
ROOT               legacy session MRD_C11_RCU
Makefile           build targets (above)
```

## The mordor → Φ bridge

Φ is computed by the **mordor** tool from the SMRD event structure and rendered into Isabelle
by `scripts/generate_phi.py`. The interchange format is specified in
[`docs/MORDOR_ISA_FORMAT.md`](docs/MORDOR_ISA_FORMAT.md); the validated UAF bridge lives under
`workspace/spikes/uaf-bridge/`. Driving `Φ_RCU` to termination is the current open task.

## Documentation

- [`REWORK_PLAN.md`](REWORK_PLAN.md) — the layered-rework master plan (architecture, triage, phases, risks).
- [`docs/PARALLEL_WORKSTREAMS.md`](docs/PARALLEL_WORKSTREAMS.md) — finer workstream breakdown + dependency cut + status.
- [`docs/W1_owicki_gries_design.md`](docs/W1_owicki_gries_design.md), `docs/SPIKE_{A,B,C,D}*` — design notes.
- [`CLAUDE.md`](CLAUDE.md) — build/architecture guidance for automated tooling.

**Caveat.** The legacy RCU proofs (`clients/RCU/`, `MRD_C11_RCU`) are heavily WIP — many
lemmas are `sorry`'d and the futures-as-constants enumeration explodes the proof goals. The
rework replaces them layer by layer; see the §6 triage in `REWORK_PLAN.md`.
