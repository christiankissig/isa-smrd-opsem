# Ownership (reusable ★ — AFP-bound)

`Ownership` as a concrete **implementation/instantiation of `OwickiGries`**: the ownership
predicate, the transfer semantics (locality / footprint / fresh acquisition), the exclusivity
invariant, and interference-freedom via ownership disjointness.

The paper's use-after-free-safety corollary (`uaf_safe`) is a separate session,
`Ownership_UAF`, so this entry carries no client-specific content.

## Build

```bash
isabelle build -d OwickiGries -d Ownership Ownership                 # check only
isabelle build -o document=pdf -o document_output=output -c -d OwickiGries -d Ownership Ownership # + PDF document
```

(Register each dependency dir with `-d`, non-recursively.)

`document_output` tells Isabelle where to copy the built PDF (default: nowhere — it
stays embedded in the session's build database); `-c` forces a clean rebuild, since
`isabelle build` otherwise skips sessions it considers already up to date and won't
regenerate the document. The PDF lands at `Ownership/output/document.pdf`.

## AFP packaging

This is the **instantiation** half of the two-entry split; the AFP entry `Ownership` depends on
the AFP entry `OwickiGries`.
