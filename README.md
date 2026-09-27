# isa-smrd-opsem

[![build](https://github.com/christiankissig/isa-smrd-opsem/actions/workflows/build.yml/badge.svg)](https://github.com/christiankissig/isa-smrd-opsem/actions/workflows/build.yml)

Isabelle/HOL formal verification that the **RCU** (Read-Copy-Update) algorithm has
**no use-after-free** under a **C11 weak-memory operational semantics** with the
**Episodic Loops / MRD** (Modified Represents Dependence) model, where the transition
relation is contextual in a fixed future set Φ:

```
prog, Φ ⊢ (σ, ρ, H) → (σ', ρ', H')
```

The development is a **stack of self-contained, reusable Isabelle sessions**, with Φ
generated from the [**mordor**](https://github.com/christiankissig/mordor)
event-structure tool.

## Architecture

Bottom-up; each reusable layer imports only layers below it.

```
Core          labels (pc·loopfun·iter), memory orders, expressions,
              the abstract action alphabet, the abstract command language,
              and the digested `LABEL is INSTRUCTION` program.  No semantics.
MemSem        σ = (viswrite, memory, φ, RF) + action effects σ ⤳ₜ σ'  (SMRD).
EventStruct   ppo, DP, executions, futures Φ, histories, horizonΦ_H, episodicity.
OpSem         command→action rules + inductive `step prog Φ`; client locale.

OwickiGries + Ownership   — INDEPENDENT vertical:
              generic Owicki-Gries over an abstract transition system + soundness,
              with Ownership as a concrete instantiation (ownership ⟹ non-interference,
              use-after-free safety).  Depends only on HOL.

Clients:      UAF_Bug (paper's minimal bug/fix) · RCU_Client (RCU as program-as-data).
```

`OwickiGries`/`Ownership` are deliberately decoupled from the Episodic stack and meet it
only at the RCU client's interpretation theory, so they stand on their own.
Full rationale in [`docs/W1_owicki_gries_design.md`](docs/W1_owicki_gries_design.md).

## Building

Requires **Isabelle2025** (or newer) — the official release from
<https://isabelle.in.tum.de> — with a built `HOL` heap (`isabelle build -b HOL`). This is what
CI uses (`make ci`); no fork is needed. (The [isabelle-emacs](https://github.com/m-fleury/isabelle-emacs)
/ `-vsce` fork still works for interactive development, but is optional.) Theory sources use
ASCII Isabelle symbol notation (`\<forall>`, `\<open>…\<close>`), not raw Unicode glyphs.

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
make gate        # from-CLEAN rebuild of the whole stack — the zero-sorry gate
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
Core/              shared vocabulary (Core.thy + ROOT)             [built]
MemSem/            thin SMRD memory semantics (MemSem.thy + ROOT)  [built]
EventStruct/       event-structure semantics (EventStruct.thy + ROOT)  [built]
OpSem/             Episodic operational semantics (OpSem.thy + ROOT)   [built]
OwickiGries/       generic Owicki-Gries framework (proven) + ROOT + metadata
Ownership/         ownership instantiation (proven) + ROOT + metadata
clients/UAF_Bug/   minimal use-after-free example (paper's headline)
clients/RCU/       RCU_Client.thy (program-as-data) + generated mordor digests + ROOT
c11_opsem/         base C11 memory model (formerly a git submodule; now in-tree)
scripts/           Φ generators (generate_phi.py)
workspace/         non-source artifacts: spikes/ (mordor→Φ bridge)
docs/              SPIKE_*, W1 design, MORDOR_ISA_FORMAT
ROOT               legacy session MRD_C11_RCU (builds only the surviving digests)
Makefile           build targets (above)
```

## The mordor → Φ bridge

The future set Φ is not hand-written: it is computed by the **mordor** event-structure tool
(<https://github.com/christiankissig/mordor>) and rendered into Isabelle by
`scripts/generate_phi.py`.

**mordor exports futures.** Given a program (a `.lit` file), mordor's `isa` output mode
(`src/isa_export.ml`) emits a single versioned JSON document — specified in
[`docs/MORDOR_ISA_FORMAT.md`](docs/MORDOR_ISA_FORMAT.md) (schema v0.1) — that carries both:

- the **program** (the straight-line `init` preamble plus each thread's *rolled* body, with full
  operands, memory orders, RMW-as-one-instruction, and nested `If`/`While`/`Do`); and
- the **futures**: `"futures": [ { "execution": N, "edges": [[e1,e2], …] }, … ]` — one edge set
  per SMRD execution, where each edge is a `ppo ∪ DP` (preserved-program-order ∪ dependence)
  dependence over **event-labels** of the form `<instr-label>[@<loop-id>:<iter>]#<k>`
  (`g.N` for init scope, `tT.N` for thread `T`; `#k` is the event index within an instruction,
  so a CAS/FAA RMW shares one instruction-label across its sub-events `#0,#1,#2`).

`scripts/generate_phi.py` consumes that JSON and emits an Isabelle theory containing (1) the
digested program as `LABEL is INSTRUCTION` entries, and (2) the future set as a concrete constant
`Φ_<prog>` — a set of edge-sets over event-labels, one set per execution (the renderer adds the
reflexive closure mordor omits). Keeping the Isabelle-specific notation here (not in mordor) is a
deliberate boundary so mordor stays prover-agnostic. The validated UAF bridge artifacts live under
`workspace/spikes/uaf-bridge/`.

**The cross-thread handshake edge is derived, not asserted.** `uaf_excluded_fixed` is proven over
a Φ enriched with the handshake DP edge `release-exit → reclaimer-read` (`t1.3#0 → t0.1#0`) that
orders the reclaimer's quiescence read after the reader's release. Single-program mordor `futures`
does not emit this synchronizes-with edge — but mordor's per-execution **reads-from** relation
(`rf`, in the `executions`-mode JSON) does. Given a companion executions document,
`generate_phi.py --executions EXEC.json` **derives** the handshake edges: for every `rf(W,R)`
whose writer `W` is a release-class write, it adds `W → R`, joining the executions' opaque
event-ids to the isa event-labels. This is execution-faithful (it uses mordor's computed `rf`, not
a structural guess) and selects exactly the synchronizing subset — the buggy variant's exit write
is relaxed, so it gains no edge and stays reachable. On the UAF fixtures this reproduces precisely
`t1.3#0 → t0.1#0` for the fixed program (in the freeing execution) and nothing for the bug. `UAF_Bug.thy`
currently defines the same edge by hand over Core types.

## Documentation

- [`docs/W1_owicki_gries_design.md`](docs/W1_owicki_gries_design.md) — the Owicki-Gries / Ownership design.
- [`docs/MORDOR_ISA_FORMAT.md`](docs/MORDOR_ISA_FORMAT.md) — the mordor↔Isabelle interchange format.
- `docs/SPIKE_{B,C,D}*` — label-digest, SMRD MemSem, and triage design notes.

