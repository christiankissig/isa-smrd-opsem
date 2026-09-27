# Makefile for isa-smrd-opsem
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
# Gate status (2026-08-12): the WHOLE reworked stack passes the strict gate --
# `make gate` (clean rebuild, no quick_and_dirty) is green across Core, MemSem,
# EventStruct, OpSem, OwickiGries, Ownership, Ownership_UAF and both clients, with
# zero sorry. The two sorries this header used to track are discharged:
#   * EventStruct.thy  `episodic_single_iteration_window` (finiteness; W8b/OpSem-full)
#   * UAF_Bug.thy      `uaf_excluded_fixed`               (the handshake-Phi long pole)
# So nothing in the reworked stack needs quick_and_dirty any more; `make spine` is
# now just a convenience subset build, kept for the shorter edit/compile loop.

ISABELLE ?= isabelle

# All reworked-layer session directories (registered for every build; the target
# session selects what is actually built, with dependencies built automatically).
DIRS := -d Core -d MemSem -d EventStruct -d OpSem -d OwickiGries -d Ownership -d Ownership_UAF -d clients/UAF_Bug -d clients/RCU

# The full reworked stack, leaves last (dependencies build automatically).
SESSIONS := Core MemSem EventStruct OpSem OwickiGries Ownership Ownership_UAF UAF_Bug RCU_Client

# Every session is now zero-sorry, so the strict gate covers the whole stack;
# CLEAN_SESSIONS is kept as an alias of SESSIONS so existing scripts / CI configs
# referring to it keep working. SPINE_SESSIONS remains a useful SUBSET for the
# Episodic spine on its own (a shorter loop while working above MemSem), not a
# quarantine for unfinished proofs.
CLEAN_SESSIONS := $(SESSIONS)
SPINE_SESSIONS := EventStruct OpSem UAF_Bug RCU_Client

# Sessions that carry a document/root.tex and can therefore be presented as PDF.
# Isabelle does NOT synthesise a root.tex, so a session without one fails the
# document build; run `isabelle mkroot` in a session dir (and add the resulting
# `document_files "root.tex"` to its ROOT) to add it to this list.
DOC_SESSIONS := OwickiGries Ownership

.DEFAULT_GOAL := help

.PHONY: help all core memsem eventstruct opsem og ownership track-a uaf rcu-client spine gate ci rcu legacy doc dry clean

help:
	@echo "isa-smrd-opsem -- Isabelle build targets"
	@echo
	@echo "  make all         build the whole reworked stack (non-q&d, zero sorry)"
	@echo "  make core        Core        -- shared vocabulary (AFP layer 1)"
	@echo "  make memsem      MemSem       -- thin SMRD memory semantics (layer 2; needs Core)"
	@echo "  make eventstruct EventStruct  -- event structures, Phi, horizon (layer 3; needs Core)"
	@echo "  make opsem       OpSem        -- Episodic step relation (layer 4; needs MemSem+EventStruct)"
	@echo "  make uaf         UAF_Bug      -- paper UAF client (needs OpSem)"
	@echo "  make rcu-client  RCU_Client   -- reworked RCU client, data-as-program (needs OpSem)"
	@echo "  make og          OwickiGries -- generic Owicki-Gries framework"
	@echo "  make ownership   Ownership  -- ownership instantiation (needs OwickiGries); alias: track-a"
	@echo "  make ownership-uaf Ownership_UAF -- UAF corollary of Ownership, kept out of the AFP entry"
	@echo "  make spine       the Episodic spine only (EventStruct+OpSem+both clients) -- shorter edit/compile loop"
	@echo "  make ci          what CI runs: the strict non-q&d, zero-sorry gate over every session"
	@echo "  make gate        from-CLEAN non-q&d rebuild of the WHOLE stack -- the zero-sorry AFP gate (green)"
	@echo "  make rcu         legacy MRD_C11_RCU session (quick_and_dirty)"
	@echo "  make doc         build the session PDFs ($(DOC_SESSIONS)) into <session>/output/document.pdf"
	@echo "  make dry         confirm the reworked sessions are up to date (isabelle build -n)"
	@echo "  make clean       remove editor backups / autosaves / .marks sidecars"
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

rcu-client:
	$(ISABELLE) build $(DIRS) RCU_Client

og:
	$(ISABELLE) build $(DIRS) OwickiGries

# Ownership pulls in OwickiGries; `track-a` is kept as an alias.
ownership track-a:
	$(ISABELLE) build $(DIRS) Ownership

ownership-uaf:
	$(ISABELLE) build $(DIRS) Ownership_UAF

# The Episodic spine on its own -- a shorter loop when working above MemSem. Subsumed
# by `make all`; no quick_and_dirty (the spine is zero-sorry like everything else).
spine:
	$(ISABELLE) build $(DIRS) $(SPINE_SESSIONS)

# The acceptance gate: clean build, no quick_and_dirty, zero sorry, across the WHOLE
# stack. Green as of 2026-08-12.
gate:
	$(ISABELLE) build -c $(DIRS) $(SESSIONS)

# CI gate (used by .github/workflows/build.yml): the strict zero-sorry, non-q&d build
# of every session. Green => the whole stack is AFP-clean. (This used to be two lines,
# the second a quick_and_dirty compile-check of the then-unfinished spine; the spine's
# sorries are discharged, so the strict build now covers it.)
ci:
	$(ISABELLE) build $(DIRS) $(SESSIONS)

# --- legacy RCU development ---------------------------------------------------

rcu legacy:
	$(ISABELLE) build -o quick_and_dirty=true -v -D . -d c11_opsem MRD_C11_RCU

# --- documentation ------------------------------------------------------------

# Build the LaTeX/PDF presentation of the sessions that have a document/root.tex.
# Each PDF lands in <session>/output/document.pdf (output/ is gitignored).
# Needs a LaTeX installation (lualatex, per the default document_build engine).
# `isabelle document` (rather than `build -o document=pdf`) is used deliberately:
# it presents from the existing session build instead of being a no-op whenever
# the heaps are already up to date.
doc:
	@for s in $(DOC_SESSIONS); do \
	    $(ISABELLE) document $(DIRS) -O $$s/output $$s || exit 1; \
	done

# --- utilities ----------------------------------------------------------------

# Confirm the reworked sessions are up to date without recompiling
# (`-n` reuses existing build databases, so it needs them built first).
dry:
	$(ISABELLE) build -n $(DIRS) $(SESSIONS)

clean:
	@find . -path ./.git -prune -o -type f \
	    \( -name '*~' -o -name '#*#' -o -name '.*.marks' \) -print -delete
	@echo "cleaned editor backups / autosaves / marks"
