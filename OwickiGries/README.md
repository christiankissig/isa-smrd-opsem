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

## Terminology: "atomics" are threads/resources/access-agnostic

This layer's `atomics` function (an outline's `(precondition, action) set`) and
`interference_free` are deliberately generic: `'act` is fully abstract, and a
"thread" here is nothing more than an outline's index into the `Ts` list. There
is no built-in notion of a resource or of who acts. The companion `Ownership`
entry is where that structure gets layered on: it instantiates `'act` as a pair
`'p × 'act` (an acting process `'p`, i.e. its notion of "thread", tupled with an
untagged operation) and equips the operation with an `acquires`/`releases`
footprint over an abstract resource type `'r`. See the `atomics` and
`interference_free` doc comments in `OwickiGries.thy` for the full bridge (incl.
how `Ownership.ownership_interference_free` relates its process tag back to the
list-index notion of thread used here).

## Build

```bash
isabelle build -d OwickiGries OwickiGries                 # check only
isabelle build -o document=pdf -o document_output=output -c -d OwickiGries OwickiGries # + PDF document
```

`document_output` tells Isabelle where to copy the built PDF (default: nowhere — it
stays embedded in the session's build database); `-c` forces a clean rebuild, since
`isabelle build` otherwise skips sessions it considers already up to date and won't
regenerate the document. The PDF lands at `OwickiGries/output/document.pdf`.

## AFP packaging

This is the **generic framework** half of the two-entry split. The sibling `Ownership` entry
imports it via the session-qualified name `imports "OwickiGries.OwickiGries"`. To submit:
register author id(s) in the AFP `metadata/authors`, fill the `date`/`authors` in `metadata`,
and drop the entry into the AFP repository tree (its `ROOT`, `document/root.tex`, and
`OwickiGries.thy`).
