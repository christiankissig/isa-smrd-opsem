# Clients

Program instantiations of the reusable stack — a program supplied as labelled `command`
data + a concrete `Φ` (generated from mordor) + a safety proof. Not AFP targets themselves
(optionally AFP examples).

- **`UAF_Bug/`** — the paper's minimal 2-thread use-after-free example (`uaf-bug.lit` /
  `uaf-bug-fixed.lit`): bug reachable vs fixed excluded. The fast validation of the stack.
  To be built fresh (Phase 4).
- **`RCU/`** — the full RCU algorithm (no use-after-free, via `Ownership`). **Currently holds
  the existing pre-rework RCU formalization** — mostly to be replaced/retired per the
  REWORK_PLAN.md → §6 triage. The 114-future enumeration here is the "wrong future set".
