# Ownership (reusable ★ — **first AFP target**)

`Ownership` as a concrete **implementation/instantiation of `OwickiGries`**: the ownership
predicate, the transfer discipline (locality / footprint / fresh acquisition), the exclusivity
invariant, and interference-freedom via ownership disjointness.

The paper's use-after-free-safety corollary (`uaf_safe`) is a separate session,
`Ownership_UAF`, so this entry carries no client-specific content.

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
