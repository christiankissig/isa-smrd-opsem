# Makefile for rcu-c11-opsem
#
# Requires Isabelle2025-vsce (the isabelle-emacs fork). Override the prover
# binary with e.g.  make ISABELLE=/path/to/isabelle core
#
# The reworked layers (Core, Track A) build with NO quick_and_dirty -- that is
# the real Archive-of-Formal-Proofs gate (zero sorry, builds from clean). The
# legacy RCU development (MRD_C11_RCU) still needs quick_and_dirty and is built
# by the `rcu` target.

ISABELLE ?= isabelle

.DEFAULT_GOAL := help

.PHONY: help all core track-a og ownership gate rcu legacy dry clean

help:
	@echo "rcu-c11-opsem -- Isabelle build targets"
	@echo
	@echo "  make all        build the reworked layers: Core + Track A (no quick_and_dirty)"
	@echo "  make core       build the Core session (shared vocabulary; AFP layer 1)"
	@echo "  make track-a    build Track A = OwickiGries + Ownership (first AFP target)"
	@echo "  make gate       from-CLEAN rebuild of Core + Track A -- the zero-sorry AFP gate"
	@echo "  make rcu        build the legacy MRD_C11_RCU session (quick_and_dirty)"
	@echo "  make dry        confirm Core + Track A are up to date (isabelle build -n)"
	@echo "  make clean      remove editor backups / autosaves / .marks sidecars"
	@echo
	@echo "  Override the prover:  make ISABELLE=/path/to/isabelle <target>"

# --- reworked, AFP-bound layers (Episodic stack) ------------------------------

all: core track-a

core:
	$(ISABELLE) build -d Core Core

# OwickiGries + Ownership are verified together via the combined Track_A session
# (a single, valid AFP-entry structure). `og`/`ownership` are aliases.
track-a og ownership:
	$(ISABELLE) build -d TrackA Track_A

# Enforce the actual acceptance gate: clean build, no quick_and_dirty, zero sorry.
gate:
	$(ISABELLE) build -c -d Core Core
	$(ISABELLE) build -c -d TrackA Track_A

# --- legacy RCU development ---------------------------------------------------

rcu legacy:
	$(ISABELLE) build -o quick_and_dirty=true -v -D . -d c11_opsem MRD_C11_RCU

# --- utilities ----------------------------------------------------------------

# Confirm the reworked sessions are up to date without recompiling
# (`-n` reuses existing build databases, so it needs them built first).
dry:
	$(ISABELLE) build -n -d Core -d TrackA Core Track_A

clean:
	@find . -path ./.git -prune -o -type f \
	    \( -name '*~' -o -name '#*#' -o -name '.*.marks' \) -print -delete
	@echo "cleaned editor backups / autosaves / marks"
