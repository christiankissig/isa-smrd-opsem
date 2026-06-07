# rcu-c11-opsem

## Overview

C11 Operational Semantics for the RCU algorithm

## Getting Started

Tested with the Isabelle2023-vsce branch of https://github.com/m-fleury/isabelle-emacs.git

## Structure of the Package

ROOT has the package metadata

Top-level theories currently are
* RCU\_local
* RCU\\_steps_unified

Additions of this package
* RCU\_state defines the program state
* RCU\_mrd defines the MRD-derived relations for preserved program order and 
  semantic dependencies
* RCU\_futures defines the futures derived from program model and MRD-derived 
  relations
* RCU\_local defines local invariants
* RCU\_steps proves invariant by program steps
* RCU\_aux contains auxiliary proofs

C11 Operational Semantics
* submodule included at c11\_opsem

Imported from the SEFM paper
* PSem contains the memory model and associated definitions and properties
* OpSem\_definite contains definitions and properties related to the 
  operational semantics
* RCU\_prog contains the program model
* RCU\_atomics defines atomics used in program model
* RCU\_wm\_proofs is a proxy for all proofs related to the weak memory model;
  RCU\_wm\_proofs is a prerequisit for the theories below
  * RCU\_wm\_prelim contains preliminary proofs realted to the weak memory model
  * RCU\_wm\_preblock contains proofs establishing pre- and post-block invariants
* RCU\_I\_steps proves pre-conditions invariant for steps in inc() method
* RCU\_R\_steps proves pre-conditions invariant for steps in reclaim() method
* RCU\_S\_steps proves pre-conditions invariant fro steps in sync() method
* RCU\_steps\_supporting contains supporting proofs
* RCU\_steps\_unified contains the unified proofs

**Caveat** The package is heavily WIP. Commented out lemmas especially in the 
SEFM imported sections need fixes, and so do sorry'ed out proofs. Performance 
remains a major issue across the proofs as the shift to future explodes the 
proof goals and branches for the proof tactics used to explore.

Top-level theories currently are
* RCU\_local
* RCU\_steps\_unified

## Futures Checklist ##

Side note: the following shows, that we need to automate futures away, or at
least review which should history and what we can decide based on the history.

When adding new futures
[] add constructor to Futures in RCU\_state.thy
[] add future to futures\_list in RCU\_state.thy
[] add future extension to futures\_to\_lines in RCU\_futures.thy
[] add history mapping to futures\_by\_history and futures\_with\_history in 
   RCU\_futures.thy
[] add future to scripts/generate\_futures\_inequalities.py and regenerate 
   RCU\_futures\_inequalities.thy
[] add to preCond in RCU\_preconds.thy
[] add to sigma\_obs in RCU\_maininvs.thy
[] add history to block\_conds in RCU\_maininvs.thy
[] ... more?

## Build in Isabelle

From the work directory with the `rcu-c11-opsem/ROOT` file, build in Isabelle as follows 

```
isabelle build -o quick_and_dirty=true -v -D .
```

For further build options to be included as `-o OPTION=VALUE`, see

```
isabelle options -l -t build
```
