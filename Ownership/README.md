# Ownership (reusable ★ — **first AFP target**)

`Ownership` as a concrete **implementation/instantiation of `OwickiGries`**: the ownership
predicate, the transfer discipline (locality / footprint / fresh acquisition), the exclusivity
invariant, interference-freedom via ownership disjointness, and a use-after-free-safety
corollary (`uaf_safe`).

Packaged with `OwickiGries` as the **first AFP submission**, over the abstract transition
system — independent of the Episodic stack. Imports its sibling via the session-qualified name
`imports "OwickiGries.OwickiGries"`. See `docs/W1_owicki_gries_design.md`, REWORK_PLAN.md → §3,
Phase 5.

**Status:** proofs complete, **zero `sorry`**, builds without `quick_and_dirty`. AFP-shaped:
`ROOT` (`chapter AFP`, `session Ownership = OwickiGries + ...`, `document_files "root.tex"`) +
`document/root.tex` (abstract). A `metadata` stub records the AFP TOML fields.

## Build

```bash
isabelle build -d OwickiGries -d Ownership Ownership                 # check only
isabelle build -o document=pdf -d OwickiGries -d Ownership Ownership # + PDF document
```

(Register each dependency dir with `-d`, non-recursively.)

## AFP packaging

This is the **instantiation** half of the two-entry split; the AFP entry `Ownership` depends on
the AFP entry `OwickiGries`. To submit: register author id(s) in `metadata/authors`, fill the
`date`/`authors` in `metadata`, and drop the entry (`ROOT`, `document/root.tex`,
`Ownership.thy`) into the AFP tree alongside `OwickiGries`.
