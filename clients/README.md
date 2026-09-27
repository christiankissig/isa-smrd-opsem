# Clients

Program instantiations of the reusable stack — a program supplied as labelled `command`
data + a concrete `Φ` (generated from mordor) + a safety proof. Not AFP targets themselves
(optionally AFP examples).

- **`UAF_Bug/`** — the paper's minimal 2-thread use-after-free example (`uaf-bug.lit` /
  `uaf-bug-fixed.lit`): bug reachable vs fixed excluded. The fast validation of the stack.
- **`RCU/`** — the RCU algorithm as program-as-data over `Core`, with the generated mordor
  digests. Loop-free fragment only; no end-to-end no-use-after-free theorem yet.
