# OwickiGries (reusable ★ — **first AFP target**)

A generic Owicki-Gries / rely-guarantee program logic over an **abstract transition system**
(a locale: `fixes` an atomic-step relation over an abstract state; with its own standard
interleaving semantics and a self-contained **soundness** proof). Shallow assertions, parallel
composition, interference freedom, proof rules, an `og_safety` invariant and an `og_sound`
partial-correctness corollary.

**Critical:** independent of the Episodic `OpSem` — depends only on HOL (`imports Main`; no
`Core`/`MemSem`/`EventStruct`/`OpSem`/`c11_opsem`/SEFM imports). The Episodic `OpSem` connects
later as one *interpretation* (in `clients/RCU`). See `docs/W1_owicki_gries_design.md`,
REWORK_PLAN.md → §3 (priority 1), Phase 5.

**Status:** proofs complete, **zero `sorry`**, builds without `quick_and_dirty`. AFP-shaped:
`ROOT` (`chapter AFP`, `document_files "root.tex"`) + `document/root.tex` (abstract). A
`metadata` stub records the AFP TOML fields.

## Build

```bash
isabelle build -d OwickiGries OwickiGries                 # check only
isabelle build -o document=pdf -d OwickiGries OwickiGries # + PDF document
```

## AFP packaging

This is the **generic framework** half of the two-entry split. The sibling `Ownership` entry
imports it via the session-qualified name `imports "OwickiGries.OwickiGries"`. To submit:
register author id(s) in the AFP `metadata/authors`, fill the `date`/`authors` in `metadata`,
and drop the entry into the AFP repository tree (its `ROOT`, `document/root.tex`, and
`OwickiGries.thy`).
