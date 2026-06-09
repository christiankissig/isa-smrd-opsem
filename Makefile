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

ISABELLE ?= isabelle

# All reworked-layer session directories (registered for every build; the target
# session selects what is actually built, with dependencies built automatically).
DIRS := -d Core -d MemSem -d OwickiGries -d Ownership

.DEFAULT_GOAL := help

.PHONY: help all core memsem eventstruct opsem og ownership track-a gate rcu legacy dry clean

help:
	@echo "rcu-c11-opsem -- Isabelle build targets"
	@echo
	@echo "  make all        build all reworked layers (Core, MemSem, OwickiGries, Ownership)"
	@echo "  make core       Core      -- shared vocabulary (AFP layer 1)"
	@echo "  make memsem     MemSem     -- thin SMRD memory semantics (layer 2; needs Core)"
	@echo "  make og         OwickiGries -- generic Owicki-Gries framework"
	@echo "  make ownership  Ownership  -- ownership instantiation (needs OwickiGries); alias: track-a"
	@echo "  make gate       from-CLEAN rebuild of all layers -- the zero-sorry AFP gate"
	@echo "  make rcu        legacy MRD_C11_RCU session (quick_and_dirty)"
	@echo "  make dry        confirm the reworked layers are up to date (isabelle build -n)"
	@echo "  make clean      remove editor backups / autosaves / .marks sidecars"
	@echo
	@echo "  Override the prover:  make ISABELLE=/path/to/isabelle <target>"

# --- reworked, AFP-bound layers (Episodic stack + the OG/Ownership vertical) ---

all:
	$(ISABELLE) build $(DIRS) Core MemSem OwickiGries Ownership

core:
	$(ISABELLE) build $(DIRS) Core

memsem:
	$(ISABELLE) build $(DIRS) MemSem

og:
	$(ISABELLE) build $(DIRS) OwickiGries

# Ownership pulls in OwickiGries; `track-a` is kept as an alias.
ownership track-a:
	$(ISABELLE) build $(DIRS) Ownership

# Enforce the actual acceptance gate: clean build, no quick_and_dirty, zero sorry.
gate:
	$(ISABELLE) build -c $(DIRS) Core MemSem OwickiGries Ownership

# --- legacy RCU development ---------------------------------------------------

rcu legacy:
	$(ISABELLE) build -o quick_and_dirty=true -v -D . -d c11_opsem MRD_C11_RCU

# --- utilities ----------------------------------------------------------------

# Confirm the reworked sessions are up to date without recompiling
# (`-n` reuses existing build databases, so it needs them built first).
dry:
	$(ISABELLE) build -n $(DIRS) Core MemSem OwickiGries Ownership

clean:
	@find . -path ./.git -prune -o -type f \
	    \( -name '*~' -o -name '#*#' -o -name '.*.marks' \) -print -delete
	@echo "cleaned editor backups / autosaves / marks"
