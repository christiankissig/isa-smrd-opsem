# Makefile for rcu-c11-opsem
#
# Requires Isabelle2025-vsce (the isabelle-emacs fork) for interactive work, but
# the reworked layers also build on the OFFICIAL Isabelle2025 (see CI). Override
# the prover binary with e.g.  make ISABELLE=/path/to/isabelle core
#
# The reworked layers build with NO quick_and_dirty -- that is the real
# Archive-of-Formal-Proofs gate (zero sorry, builds from clean). They are proper
# per-layer Isabelle sessions; cross-layer imports use session-qualified theory
# names (e.g. `imports "Core.Core"`). The legacy RCU development (MRD_C11_RCU)
# still needs quick_and_dirty and is built by the `rcu` target.
#
# Gate status (2026-06-10): Core, MemSem, OwickiGries, Ownership build clean with
# NO quick_and_dirty (zero sorry). The Episodic spine above MemSem -- EventStruct,
# OpSem, and the UAF_Bug client -- still carries TWO documented open sorries, so it
# does NOT yet pass the strict gate:
#   * EventStruct.thy  `episodic_single_iteration_window` (finiteness; W8b/OpSem-full)
#   * UAF_Bug.thy      `uaf_excluded_fixed`               (the handshake-Phi long pole)
# So `make all` / `make gate` (non-q&d) are EXPECTED to fail on those two until they
# are discharged -- that is the gate doing its job. Use `make spine` (quick_and_dirty)
# to compile the spine through the sorries and produce heaps for downstream work.

ISABELLE ?= isabelle

# All reworked-layer session directories (registered for every build; the target
# session selects what is actually built, with dependencies built automatically).
DIRS := -d Core -d MemSem -d EventStruct -d OpSem -d OwickiGries -d Ownership -d clients/UAF_Bug -d clients/RCU

# The full reworked stack, leaves last (dependencies build automatically).
SESSIONS := Core MemSem EventStruct OpSem OwickiGries Ownership UAF_Bug RCU_Client

# The mature, genuinely zero-sorry layers (the strict non-q&d gate). The Episodic
# spine (EventStruct/OpSem/UAF_Bug/RCU_Client) is excluded here because it sits on
# OpSem, which still carries two documented open sorries; it is compile-checked
# separately under quick_and_dirty. (RCU_Client itself adds no sorry.)
CLEAN_SESSIONS := Core MemSem OwickiGries Ownership
SPINE_SESSIONS := EventStruct OpSem UAF_Bug RCU_Client

.DEFAULT_GOAL := help

.PHONY: help all core memsem eventstruct opsem og ownership track-a uaf rcu-client spine gate ci rcu legacy dry clean

help:
	@echo "rcu-c11-opsem -- Isabelle build targets"
	@echo
	@echo "  make all         build the whole reworked stack (non-q&d; fails on the 2 open sorries)"
	@echo "  make core        Core        -- shared vocabulary (AFP layer 1)"
	@echo "  make memsem      MemSem       -- thin SMRD memory semantics (layer 2; needs Core)"
	@echo "  make eventstruct EventStruct  -- event structures, Phi, horizon (layer 3; needs Core)"
	@echo "  make opsem       OpSem        -- Episodic step relation (layer 4; needs MemSem+EventStruct)"
	@echo "  make uaf         UAF_Bug      -- paper UAF client (needs OpSem)"
	@echo "  make rcu-client  RCU_Client   -- reworked RCU client, data-as-program (needs OpSem; q&d via spine)"
	@echo "  make og          OwickiGries -- generic Owicki-Gries framework"
	@echo "  make ownership   Ownership  -- ownership instantiation (needs OwickiGries); alias: track-a"
	@echo "  make spine       EventStruct+OpSem+UAF_Bug WITH quick_and_dirty (WIP route; compiles through sorries)"
	@echo "  make ci          what CI runs: strict non-q&d gate on the mature layers + q&d compile-check of the spine"
	@echo "  make gate        from-CLEAN non-q&d rebuild of the WHOLE stack -- the (aspirational) zero-sorry AFP gate"
	@echo "  make rcu         legacy MRD_C11_RCU session (quick_and_dirty)"
	@echo "  make dry         confirm the reworked sessions are up to date (isabelle build -n)"
	@echo "  make clean       remove editor backups / autosaves / .marks sidecars"
	@echo
	@echo "  Open sorries (block the strict gate): EventStruct episodic_single_iteration_window,"
	@echo "  UAF_Bug uaf_excluded_fixed. make all/gate fail on these by design; make spine builds through."
	@echo
	@echo "  Override the prover:  make ISABELLE=/path/to/isabelle <target>"

# --- reworked, AFP-bound layers (Episodic stack + the OG/Ownership vertical) ---

all:
	$(ISABELLE) build $(DIRS) $(SESSIONS)

core:
	$(ISABELLE) build $(DIRS) Core

memsem:
	$(ISABELLE) build $(DIRS) MemSem

eventstruct:
	$(ISABELLE) build $(DIRS) EventStruct

opsem:
	$(ISABELLE) build $(DIRS) OpSem

uaf:
	$(ISABELLE) build $(DIRS) UAF_Bug

# RCU_Client sits on OpSem (open sorries), so build it through quick_and_dirty like
# the rest of the spine. RCU_Client adds no sorry of its own.
rcu-client:
	$(ISABELLE) build -o quick_and_dirty=true $(DIRS) RCU_Client

og:
	$(ISABELLE) build $(DIRS) OwickiGries

# Ownership pulls in OwickiGries; `track-a` is kept as an alias.
ownership track-a:
	$(ISABELLE) build $(DIRS) Ownership

# WIP route: compile the Episodic spine through its two open sorries (quick_and_dirty),
# so downstream work has heaps. Drop this once the sorries are discharged (then it is
# subsumed by `make all`).
spine:
	$(ISABELLE) build -o quick_and_dirty=true $(DIRS) $(SPINE_SESSIONS)

# Enforce the actual acceptance gate: clean build, no quick_and_dirty, zero sorry,
# across the WHOLE stack. Currently fails on the 2 documented spine sorries by design.
gate:
	$(ISABELLE) build -c $(DIRS) $(SESSIONS)

# CI gate (used by .github/workflows/build.yml): strict zero-sorry, non-q&d build of
# the mature layers, PLUS a quick_and_dirty compile-check of the in-progress spine
# (which still carries 2 documented sorries). Green => mature layers are AFP-clean
# AND the spine compiles structurally. This stays green while the spine is finished;
# once its sorries are discharged, fold the spine into the first line and drop this.
ci:
	$(ISABELLE) build $(DIRS) $(CLEAN_SESSIONS)
	$(ISABELLE) build -o quick_and_dirty=true $(DIRS) $(SPINE_SESSIONS)

# --- legacy RCU development ---------------------------------------------------

rcu legacy:
	$(ISABELLE) build -o quick_and_dirty=true -v -D . -d c11_opsem MRD_C11_RCU

# --- utilities ----------------------------------------------------------------

# Confirm the reworked sessions are up to date without recompiling
# (`-n` reuses existing build databases, so it needs them built first).
dry:
	$(ISABELLE) build -n $(DIRS) $(SESSIONS)

clean:
	@find . -path ./.git -prune -o -type f \
	    \( -name '*~' -o -name '#*#' -o -name '.*.marks' \) -print -delete
	@echo "cleaned editor backups / autosaves / marks"
