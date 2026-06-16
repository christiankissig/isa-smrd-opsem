#!/usr/bin/env python3
"""generate_phi.py  --  repo-side renderer ("W3") for the mordor -> Isabelle bridge.

Consumes a mordor `isa`-mode JSON document (schema v0.1, see
docs/MORDOR_ISA_FORMAT.md) and emits an Isabelle/HOL theory containing:

  (1) the *digested program* as a list of `LABEL is INSTRUCTION` entries
      (one definition per thread + an `init` digest), with full operands,
      memory orders, RMW-as-one-instruction, and nested If/While/Do; and
  (2) the future set `Phi` (rendered `\\<Phi>_<prog>`) as a concrete constant:
      a set of edge-sets over event-labels, one set per execution.

Boundary decision (REWORK_PLAN.md s5, MORDOR_ISA_FORMAT.md s0): mordor emits the
JSON schema; THIS script renders Isabelle.  The Isabelle type defs emitted here
are PROVISIONAL / WIP placeholders, to be replaced by the Core types from Spike B.

Usage:
    scripts/generate_phi.py INPUT.json [-o OUTPUT.thy] [--theory NAME]

With no -o the theory is printed to stdout.  The Isabelle theory name must match
the output file stem; when -o is given the stem is used, otherwise NAME (or a
name derived from the program) is used.
"""

import argparse
import json
import os
import re
import sys


# --------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------

# Memory-order constructors declared by PROVISIONAL_TYPES below.  Any order
# value seen in the document that is NOT one of these is rendered verbatim but
# triggers a stderr warning (it would not typecheck against the provisional
# `mem_order` datatype).
KNOWN_ORDERS = ("rlx", "acq", "rel", "acq_rel", "sc")

# event-label grammar (MORDOR_ISA_FORMAT.md s2/s4):
#   <instr-label>[@<loop-id>:<iter>]#<k>
# where <instr-label> is "g.<seq>" (init scope) or "t<tid>.<seq>" (thread scope).
_EVLABEL_RE = re.compile(
    r"^(?P<instr>(?:g|t\d+)\.\d+)"     # instruction-label: g.N or tT.N
    r"(?:@(?P<loop>\d+):(?P<iter>\d+))?"  # optional @loop:iter (rolled-loop unrolling)
    r"#(?P<k>\d+)$"                    # event index
)


def iss(s):
    """Render a python str as an Isabelle ''...'' string literal."""
    return "''%s''" % s


def parse_evlabel(lbl):
    """Best-effort structural parse of an event-label.

    Returns a dict {instr, loop, iter, k, scope} or None if the label does not
    match the expected grammar.  `scope` is 'init' for g.* labels and 'thread'
    for t*.* labels.  Used only for validation / warnings; the renderer always
    emits the label verbatim so unrecognised forms still pass through losslessly.
    """
    m = _EVLABEL_RE.match(lbl)
    if not m:
        return None
    d = m.groupdict()
    d["scope"] = "init" if d["instr"].startswith("g.") else "thread"
    return d


def sanitize(name):
    """Turn a program name (e.g. 'uaf-bug-fixed.lit') into an Isabelle ident
    fragment (e.g. 'uaf_bug_fixed')."""
    base = os.path.basename(name)
    if base.endswith(".lit"):
        base = base[:-4]
    out = []
    for ch in base:
        out.append(ch if (ch.isalnum() or ch == "_") else "_")
    frag = "".join(out).strip("_")
    if not frag:
        frag = "prog"
    if frag[0].isdigit():
        frag = "p_" + frag
    return frag


# --------------------------------------------------------------------------
# expression / operand rendering
# --------------------------------------------------------------------------

def render_expr(e):
    """Render an expr / cond / val / ptr / loc operand as an `expr` term.

    Accepts: {"int":n} | {"reg":r} | {"eq":[..]} | {"add":[..]} | {<op>:[..]}
             | bare register string | bare int.
    """
    if isinstance(e, bool):
        return "(EInt %d)" % (1 if e else 0)
    if isinstance(e, int):
        return "(EInt %d)" % e if e >= 0 else "(EInt (%d))" % e
    if isinstance(e, str):
        # a bare register holding an address (e.g. Free's "ptr": "rC")
        return "(EReg %s)" % iss(e)
    if isinstance(e, dict):
        if "int" in e:
            n = e["int"]
            return "(EInt %d)" % n if n >= 0 else "(EInt (%d))" % n
        if "reg" in e:
            return "(EReg %s)" % iss(e["reg"])
        if "eq" in e:
            a, b = e["eq"]
            return "(EEq %s %s)" % (render_expr(a), render_expr(b))
        if "add" in e:
            a, b = e["add"]
            return "(EAdd %s %s)" % (render_expr(a), render_expr(b))
        # generic fall-back for any other unary/binary/n-ary operator
        op, args = next(iter(e.items()))
        if not isinstance(args, list):
            args = [args]
        return "(EOp %s [%s])" % (iss(op), ", ".join(render_expr(x) for x in args))
    raise ValueError("cannot render expr: %r" % (e,))


# --------------------------------------------------------------------------
# command rendering
# --------------------------------------------------------------------------

_warned_orders = set()


def _rmw_note(cmd):
    """Inline Isabelle comment carrying the RMW `rmw_op` field (strong/weak),
    which has no slot in the provisional `command` datatype.  Empty if absent."""
    rmw = cmd.get("rmw_op")
    if rmw is None:
        return ""
    return r" \<comment> \<open>rmw_op: %s\<close>" % rmw


def render_order(o):
    """Render a memory order as a bare `mem_order` constructor.

    Orders are emitted verbatim (they are valid Isabelle idents).  An order not
    in KNOWN_ORDERS is passed through but warned about once, since it would not
    typecheck against the provisional `mem_order` datatype.
    """
    if o not in KNOWN_ORDERS and o not in _warned_orders:
        _warned_orders.add(o)
        sys.stderr.write(
            "warning: memory order %r is not one of %s; emitted verbatim "
            "(will not typecheck against provisional mem_order)\n"
            % (o, ", ".join(KNOWN_ORDERS)))
    return o


def render_command(cmd, indent):
    """Render one command.  `indent` is the column of the enclosing digest
    entry; nested control-flow digests are indented relative to it."""
    op = cmd["op"]

    if op == "Set":
        return "Set %s %s" % (iss(cmd["dst"]), render_expr(cmd["expr"]))
    if op == "ReadPtr":
        return "ReadPtr %s %s %s" % (render_order(cmd["order"]), iss(cmd["dst"]),
                                     render_expr(cmd["ptr"]))
    if op == "ReadVar":
        return "ReadVar %s %s %s" % (render_order(cmd["order"]), iss(cmd["dst"]),
                                     iss(cmd["var"]))
    if op == "ReadRef":
        return "ReadRef %s %s" % (iss(cmd["dst"]), iss(cmd["var"]))
    if op == "WritePtr":
        return "WritePtr %s %s %s" % (render_order(cmd["order"]),
                                      render_expr(cmd["ptr"]),
                                      render_expr(cmd["val"]))
    if op == "WriteVar":
        return "WriteVar %s %s %s" % (render_order(cmd["order"]), iss(cmd["var"]),
                                      render_expr(cmd["val"]))
    if op == "Faa":
        # RMW = ONE instruction, two events (R;W).  `rmw_op` (strong/weak) has no
        # slot in the provisional `command` type, so it is preserved as an inline
        # Isabelle comment rather than dropped (see header / MORDOR_ISA_FORMAT s7).
        return "Faa %s %s %s %s %s%s" % (
            render_order(cmd["order_r"]), render_order(cmd["order_w"]),
            iss(cmd["dst"]), render_expr(cmd["loc"]),
            render_expr(cmd["addend"]), _rmw_note(cmd))
    if op == "Cas":
        # RMW = ONE instruction, three events (R;Branch;W on success, no W on fail).
        return "Cas %s %s %s %s %s %s%s" % (
            render_order(cmd["order_r"]), render_order(cmd["order_w"]),
            iss(cmd["dst"]), render_expr(cmd["loc"]),
            render_expr(cmd["expected"]), render_expr(cmd["new"]),
            _rmw_note(cmd))
    if op == "Alloc":
        return "Alloc %s %s" % (iss(cmd["dst"]), render_expr(cmd["size"]))
    if op == "Free":
        return "Free %s" % render_expr(cmd["ptr"])
    if op == "Fence":
        return "Fence %s" % render_order(cmd["order"])
    if op == "If":
        sub = indent + "    "
        then_d = render_digest(cmd.get("then", []), sub)
        else_d = render_digest(cmd.get("else", []), sub)
        return "If %s\n%s%s\n%s%s" % (render_expr(cmd["cond"]),
                                      sub, then_d, sub, else_d)
    if op in ("While", "Do"):
        # `Do` (do-while) is not in MORDOR_ISA_FORMAT s3 v0.1 but appears in
        # cas_aba; treated like While (see s7 grammar gaps).  `loop_id` is
        # carried on the command in the impl; default to -1 if a future
        # producer omits it (renders as `(-1)`, an obvious sentinel).
        ctor = "While" if op == "While" else "Do"
        sub = indent + "    "
        body_d = render_digest(cmd.get("body", []), sub)
        loop_id = cmd.get("loop_id", -1)
        lid = "%d" % loop_id if loop_id >= 0 else "(%d)" % loop_id
        return "%s %s\n%s%s\n%s%s" % (ctor, render_expr(cmd["cond"]),
                                      sub, body_d, sub, lid)

    raise ValueError(
        "unknown command op %r (extend render_command / PROVISIONAL_TYPES "
        "to support it; see MORDOR_ISA_FORMAT.md s3)" % (op,))


def render_digest(instrs, indent):
    """Render a list of instructions as an Isabelle list of `LABEL is COMMAND`
    entries.  Empty -> `[]`."""
    if not instrs:
        return "[]"
    entries = []
    for ins in instrs:
        lbl = iss(ins["label"])
        cmd = render_command(ins["command"], indent)
        entries.append("%s%s is %s" % (indent, lbl, cmd))
    return "[\n" + ",\n".join(entries) + "\n" + indent + "]"


# --------------------------------------------------------------------------
# event -> instruction map (the digest's auxiliary table)
# --------------------------------------------------------------------------

def normalise_edges(edges, ctx=""):
    """Normalise a futures edge-set for rendering.

    The schema's `edges` are `(ppo u DP)` tuples over event-labels (s1/s4):
      * each `[e1, e2]` is read as the ordered pair `(e1, e2)`;
      * reflexive (identity) edges `(e, e)` are DROPPED -- the spec says the
        renderer/consumer takes reflexive closure, so they carry no information
        and would only clutter the set;
      * exact duplicates are removed;
      * order is preserved (first occurrence wins), which keeps the rendered
        set diffable against the source JSON.

    Unparseable event-labels are passed through verbatim but warned about.
    Returns a list of (src, dst) 2-tuples.
    """
    seen = set()
    out = []
    for e in edges:
        if not isinstance(e, (list, tuple)) or len(e) != 2:
            raise ValueError("malformed edge %r%s (expected a 2-element "
                             "[src, dst])" % (e, ctx))
        s, t = e[0], e[1]
        for lbl in (s, t):
            if parse_evlabel(lbl) is None:
                sys.stderr.write(
                    "warning: edge label %r%s does not match the event-label "
                    "grammar; emitted verbatim\n" % (lbl, ctx))
        if s == t:
            continue  # reflexive: dropped (consumer takes reflexive closure)
        if (s, t) in seen:
            continue  # duplicate
        seen.add((s, t))
        out.append((s, t))
    return out


def collect_events(instrs, acc):
    """Flatten the (possibly nested) instruction tree, collecting
    (event-label, instruction-label, event-type) triples."""
    for ins in instrs:
        lbl = ins["label"]
        for ev in ins.get("events", []):
            acc.append(("%s#%d" % (lbl, ev["k"]), lbl, ev["type"]))
        cmd = ins["command"]
        for key in ("then", "else", "body"):
            if key in cmd:
                collect_events(cmd[key], acc)
    return acc


# --------------------------------------------------------------------------
# handshake derivation: cross-thread synchronizes-with from reads-from
# --------------------------------------------------------------------------
#
# Single-program mordor `futures` (the isa JSON) carries only the (ppo u DP)
# edges within the program's preserved order; it does NOT emit the cross-thread
# synchronizes-with that a release/acquire handshake creates -- e.g. the RCU
# reclaimer's quiescence read reading-from the reader's release-exit.  That edge
# is, however, present in mordor's per-execution `rf` (reads-from) relation in
# the *executions*-mode JSON.  When such a companion document is supplied
# (--executions), we DERIVE the handshake edges rather than hand-adding them:
#
#   for every rf(w, r) whose writer w is a RELEASE-class write, add  w -> r.
#
# This is execution-faithful (it uses mordor's computed rf for that execution,
# not a structural guess) and selects exactly the synchronizing subset: a
# relaxed-write rf creates no ordering and is correctly excluded (which is why
# the buggy variant, whose exit write is relaxed, gains no edge and stays
# reachable).  The opaque executions event-ids are joined to the isa
# event-labels by robust signatures (writes by short-order + value, allocs by
# program order, reads by the location-name learned from those matches).

# mordor `executions` memory-order spelling -> schema short order
_EXEC_ORDER = {
    "Relaxed": "rlx", "Acquire": "acq", "Release": "rel",
    "AcqRel": "acq_rel", "Acq_Rel": "acq_rel", "SeqCst": "sc", "SC": "sc",
}
# write orders that publish a release (synchronize with a reading load)
_RELEASE_CLASS = {"Release", "AcqRel", "Acq_Rel", "SeqCst", "SC"}


def _ptr_name(operand):
    """Flatten a ptr/loc/var operand to a plain location name, or None."""
    if isinstance(operand, str):
        return operand
    if isinstance(operand, dict) and "reg" in operand:
        return operand["reg"]
    return None


def _coerce_int(v):
    """Best-effort int from an operand or an executions wval/rval string."""
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, int):
        return v
    if isinstance(v, dict) and "int" in v:
        return v["int"]
    if isinstance(v, str):
        try:
            return int(v)
        except ValueError:
            return None
    return None


def _event_k(ins, etype):
    """Index k of the first event of type etype in an instruction, or None."""
    for ev in ins.get("events", []):
        if ev.get("type") == etype:
            return ev["k"]
    return None


def _index_isa_memops(doc):
    """Index the isa program's memory ops with their thread and W/R event index.

    Walks init (thread None) + each thread body, descending into If/While/Do
    sub-digests (which inherit the enclosing thread).  Returns
    {writes, reads, allocs}, each a list of dicts."""
    writes, reads, allocs = [], [], []

    def walk(instrs, thread):
        for ins in instrs:
            cmd = ins["command"]
            op = cmd.get("op")
            lbl = ins["label"]
            if op in ("WritePtr", "WriteVar"):
                writes.append({
                    "label": lbl, "thread": thread, "order": cmd.get("order"),
                    "ptr": _ptr_name(cmd.get("ptr") if op == "WritePtr"
                                     else cmd.get("var")),
                    "val": _coerce_int(cmd.get("val")), "k": _event_k(ins, "W")})
            elif op in ("ReadPtr", "ReadVar"):
                reads.append({
                    "label": lbl, "thread": thread, "order": cmd.get("order"),
                    "ptr": _ptr_name(cmd.get("ptr") if op == "ReadPtr"
                                     else cmd.get("var")), "k": _event_k(ins, "R")})
            elif op in ("Faa", "Cas"):
                writes.append({
                    "label": lbl, "thread": thread, "order": cmd.get("order_w"),
                    "ptr": _ptr_name(cmd.get("loc")),
                    "val": _coerce_int(cmd.get("new") if op == "Cas"
                                       else cmd.get("addend")),
                    "k": _event_k(ins, "W")})
                reads.append({
                    "label": lbl, "thread": thread, "order": cmd.get("order_r"),
                    "ptr": _ptr_name(cmd.get("loc")), "k": _event_k(ins, "R")})
            elif op == "Alloc":
                allocs.append({"label": lbl, "thread": thread,
                               "ptr": cmd.get("dst")})
            for key in ("then", "else", "body"):
                if key in cmd:
                    walk(cmd[key], thread)

    walk(doc.get("init", []), None)
    for th in doc.get("threads", []):
        walk(th.get("body", []), th.get("tid"))
    return {"writes": writes, "reads": reads, "allocs": allocs}


def derive_handshake_edges(isa_doc, exec_doc):
    """Derive cross-thread release handshake edges from mordor's rf relation.

    Returns (edges, warnings): `edges` is a set of (src_label, dst_label)
    event-label pairs (W -> R for each rf(W,R) with W a release-class write);
    `warnings` records any rf edge whose endpoints could not be joined
    unambiguously to the isa labels (such edges are skipped, never guessed)."""
    warnings = []
    memops = _index_isa_memops(isa_doc)

    def match_write(order_short, val):
        cands = [w for w in memops["writes"]
                 if w["order"] == order_short and w["val"] == val]
        return cands[0] if len(cands) == 1 else None

    # global event table (ids are consistent across executions)
    ev_by_id = {}
    for ex in exec_doc.get("executions", []):
        for ev in ex.get("events", []):
            ev_by_id[ev["id"]] = ev

    # learn exec-location-name -> isa pointer-name
    loc2ptr = {}
    exec_allocs = sorted((ev for ev in ev_by_id.values() if ev.get("type") == "A"),
                         key=lambda ev: ev["id"])
    for ev, isa_a in zip(exec_allocs, memops["allocs"]):
        if ev.get("location") is not None and isa_a["ptr"] is not None:
            loc2ptr.setdefault(ev["location"], isa_a["ptr"])
    for ev in ev_by_id.values():
        if ev.get("type") != "W":
            continue
        m = match_write(_EXEC_ORDER.get(ev.get("wmod")), _coerce_int(ev.get("wval")))
        if m and ev.get("location") is not None and m["ptr"] is not None:
            loc2ptr.setdefault(ev["location"], m["ptr"])

    edges = set()
    for ex in exec_doc.get("executions", []):
        evmap = {ev["id"]: ev for ev in ex.get("events", [])}
        for pair in ex.get("rf", []):
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                continue
            w, r = evmap.get(pair[0]), evmap.get(pair[1])
            if not w or not r or w.get("type") != "W":
                continue
            if w.get("wmod") not in _RELEASE_CLASS:
                continue  # only release-class writes synchronize
            wm = match_write(_EXEC_ORDER.get(w.get("wmod")), _coerce_int(w.get("wval")))
            if wm is None:
                warnings.append("release write id%s could not be mapped to a "
                                "unique isa write" % pair[0])
                continue
            ptr = loc2ptr.get(r.get("location"))
            if ptr is None:
                warnings.append("rf reader id%s: unknown location %r"
                                % (pair[1], r.get("location")))
                continue
            rcands = [rd for rd in memops["reads"]
                      if rd["ptr"] == ptr and rd["thread"] != wm["thread"]]
            if len(rcands) != 1:
                warnings.append("rf reader id%s on %s: %d cross-thread isa reads "
                                "(need exactly 1)" % (pair[1], ptr, len(rcands)))
                continue
            edges.add(("%s#%d" % (wm["label"], wm["k"] or 0),
                       "%s#%d" % (rcands[0]["label"], rcands[0]["k"] or 0)))
    return edges, warnings


# --------------------------------------------------------------------------
# theory assembly
# --------------------------------------------------------------------------

PROVISIONAL_TYPES = r"""section \<open>PROVISIONAL / WIP encoding types\<close>

text \<open>
  The datatypes below are a minimal placeholder vocabulary so that the
  generated digest and \<open>\<Phi>\<close> are well-formed Isabelle.  They are
  intentionally lightweight and are TO BE REPLACED by the Core action /
  command / order types from Spike B.  Nothing here is meant to be definitive.
\<close>

datatype mem_order = rlx | acq | rel | acq_rel | sc

datatype expr =
    EInt int
  | EReg string
  | EEq expr expr
  | EAdd expr expr
  | EOp string "expr list"   \<comment> \<open>generic n-ary operator fall-back\<close>

type_synonym reg = string
type_synonym label = string
type_synonym loop_id = int

text \<open>One source instruction = one abstract \<open>command\<close> with full operands.
  An RMW (\<open>Faa\<close>, \<open>Cas\<close>) is a single command carrying several events.
  Control flow (\<open>If\<close>/\<open>While\<close>/\<open>Do\<close>) keeps the program \emph{rolled}: the
  branches/bodies are themselves digests.\<close>

datatype command =
    Set reg expr
  | ReadPtr mem_order reg expr
  | ReadVar mem_order reg string
  | ReadRef reg string
  | WritePtr mem_order expr expr
  | WriteVar mem_order string expr
  | Faa mem_order mem_order reg expr expr
  | Cas mem_order mem_order reg expr expr expr
  | Alloc reg expr
  | Free expr
  | Fence mem_order
  | If expr "(label \<times> command) list" "(label \<times> command) list"
  | While expr "(label \<times> command) list" loop_id
  | Do expr "(label \<times> command) list" loop_id

text \<open>The digest notation \<open>LABEL is INSTRUCTION\<close>.  (PROVISIONAL: \<open>is\<close> is a
  reserved outer-syntax keyword used in term-abbreviation patterns; should that
  clash, rename this mixfix when wiring in the Spike B Core types.)\<close>

definition entry :: "label \<Rightarrow> command \<Rightarrow> (label \<times> command)"  (infix "is" 49)
  where "lbl is cmd \<equiv> (lbl, cmd)"
"""


def render_theory(doc, theory_name, derived_edges=None):
    prog = doc.get("program", "prog")
    frag = sanitize(prog)
    orders = doc.get("orders", [])
    fmt = doc.get("format_version", "?")

    out = []
    a = out.append

    # ---- header ----------------------------------------------------------
    a("(*")
    a("  GENERATED FILE -- do not hand-edit.")
    a("")
    a("  Rendered by scripts/generate_phi.py (repo-side renderer, REWORK_PLAN.md s5 / W3)")
    a("  from a mordor `isa`-mode JSON document (schema v%s, docs/MORDOR_ISA_FORMAT.md)." % fmt)
    a("")
    a("  Source program : %s" % prog)
    a("  Producing cmd  : mordor futures --single %s --output-mode isa" % prog)
    a("                   (rendered: scripts/generate_phi.py <isa.json> -o <this file>)")
    a("  Memory orders  : %s" % ", ".join(orders))
    a("")
    a("  Contents:")
    a("    * provisional encoding types (WIP, to be replaced by Spike B Core types)")
    a("    * the digested program: per-thread `LABEL is INSTRUCTION` lists")
    a("    * \\<Phi>_%s : the future set, one edge-set over event-labels per execution" % frag)
    if derived_edges:
        a("      (ENRICHED with cross-thread release-handshake edges derived from a")
        a("       companion executions-mode JSON's reads-from relation -- see below)")
    a("")
    a("  Notes / faithfulness:")
    if derived_edges:
        a("    * Cross-thread release HANDSHAKE edges (W -> R) are DERIVED from")
        a("      mordor's per-execution reads-from (release-class writer) and added")
        a("      to \\<Phi>; single-program `futures` does not emit these synchronizes-")
        a("      with edges.  Each derived edge is flagged with an inline `text` note")
        a("      on the execution it augments (added only where both endpoints occur).")
    a("    * RMW (Faa/Cas) is ONE instruction carrying several events (Faa #0,#1;")
    a("      Cas #0,#1,#2 -- the W #2 is absent on a failing CAS).")
    a("    * Loop-iteration event-labels (e.g. t0.4@1:1#0) are rendered verbatim in \\<Phi>.")
    a("    * init-scope labels are g.* ; thread-scope labels are t<tid>.* .")
    a("    * Edges are normalised before rendering: reflexive (identity) edges are")
    a("      DROPPED (the consumer takes reflexive closure, MORDOR_ISA_FORMAT.md s1)")
    a("      and exact duplicates removed; first-occurrence order is preserved.")
    a("    * Faa/Cas `rmw_op` (strong/weak) has no slot in the provisional command")
    a("      type, so it is preserved as an inline Isabelle comment on the entry.")
    a("*)")
    a("")
    a("theory %s" % theory_name)
    a("  imports Main")
    a("begin")
    a("")
    a(PROVISIONAL_TYPES)
    a("")

    # ---- program digest --------------------------------------------------
    a(r"section \<open>Digested program: %s\<close>" % prog)
    a("")

    init = doc.get("init", [])
    a("definition prog_%s_init :: \"(label \\<times> command) list\" where" % frag)
    a("  \"prog_%s_init =" % frag)
    a(indent_block(render_digest(init, "     "), "  "))
    a("  \"")
    a("")

    thread_defs = []
    for th in doc.get("threads", []):
        tid = th["tid"]
        name = "prog_%s_t%d" % (frag, tid)
        thread_defs.append(name)
        a("definition %s :: \"(label \\<times> command) list\" where" % name)
        a("  \"%s =" % name)
        a(indent_block(render_digest(th.get("body", []), "     "), "  "))
        a("  \"")
        a("")

    # whole-program convenience: init + per-thread bodies
    a("definition prog_%s :: \"(label \\<times> command) list list\" where" % frag)
    allparts = ["prog_%s_init" % frag] + thread_defs
    a("  \"prog_%s = [%s]\"" % (frag, ", ".join(allparts)))
    a("")

    # ---- event -> instruction map ---------------------------------------
    triples = []
    collect_events(init, triples)
    for th in doc.get("threads", []):
        collect_events(th.get("body", []), triples)
    a(r"text \<open>Static event \<open>\<rightarrow>\<close> instruction map (event-label,")
    a(r"  instruction-label, type).  These are the \emph{rolled} event-labels (no")
    a(r"  \<open>@loop:iter\<close> suffix); the unrolled iter-labels appearing in \<open>\<Phi>\<close>")
    a(r"  collapse onto these via the \<open>lb\<close>-rule (MORDOR_ISA_FORMAT.md s2).\<close>")
    a("definition evmap_%s :: \"(string \\<times> string \\<times> string) list\" where" % frag)
    if triples:
        rows = ["  (%s, %s, %s)" % (iss(e), iss(i), iss(t)) for (e, i, t) in triples]
        a("  \"evmap_%s = [" % frag)
        a(",\n".join(rows))
        a("  ]\"")
    else:
        a("  \"evmap_%s = []\"" % frag)
    a("")

    # ---- futures / Phi ---------------------------------------------------
    a(r"section \<open>Future set \<open>\<Phi>\<close>\<close>")
    a("")
    a(r"text \<open>Each execution contributes one edge-set (\<open>(ppo \<union> dp)\<close> over")
    a(r"  event-labels); \<open>\<Phi>_%s\<close> is the set of those edge-sets.\<close>" % frag)
    if derived_edges:
        a(r"text \<open>This \<open>\<Phi>\<close> is ENRICHED with cross-thread release-handshake")
        a(r"  edges \<open>(W \<rightarrow> R)\<close> DERIVED from mordor's per-execution")
        a(r"  reads-from relation (release-class writer); these are the")
        a(r"  synchronizes-with that single-program \<open>futures\<close> omits.  Each is")
        a(r"  added only to executions whose event-labels already contain both")
        a(r"  endpoints, and is flagged inline below.\<close>")
    a("")

    exec_defs = []
    for fut in doc.get("futures", []):
        ex = fut["execution"]
        ename = "\\<Phi>_%s_exec%d" % (frag, ex)
        exec_defs.append(ename)
        edges = normalise_edges(fut.get("edges", []),
                                ctx=" (exec %s)" % ex)
        applied = []
        if derived_edges:
            labels = {l for (s, t) in edges for l in (s, t)}
            for (s, t) in sorted(derived_edges):
                if s in labels and t in labels and (s, t) not in edges:
                    edges.append((s, t))
                    applied.append((s, t))
        if applied:
            a(r"text \<open>exec %s: +%d derived release-handshake edge(s): %s\<close>"
              % (ex, len(applied),
                 "; ".join("%s \\<rightarrow> %s" % e for e in applied)))
        a("definition %s :: \"(string \\<times> string) set\" where" % ename)
        if edges:
            rows = ["  (%s, %s)" % (iss(s), iss(t)) for (s, t) in edges]
            a("  \"%s =" % ename)
            a("  {")
            a(",\n".join(rows))
            a("  }\"")
        else:
            a("  \"%s = {}\"" % ename)
        a("")

    a("definition \\<Phi>_%s :: \"(string \\<times> string) set set\" where" % frag)
    if exec_defs:
        a("  \"\\<Phi>_%s =" % frag)
        a("  { " + ",\n    ".join(exec_defs) + " }\"")
    else:
        a("  \"\\<Phi>_%s = {}\"" % frag)
    a("")

    a("end")
    a("")
    return "\n".join(out)


def indent_block(text, prefix):
    return "\n".join(prefix + line if line else line for line in text.split("\n"))


# --------------------------------------------------------------------------
# Core-typed Phi rendering (--core): emit \<Phi> over the REAL Core elabel
# types so a client proof (clients/UAF_Bug/UAF_Bug.thy) can consume it directly,
# instead of the provisional string-labelled placeholder above.
# --------------------------------------------------------------------------
#
# Event-labels map to Core terms via the shared helpers in the labels theory
# (UAF_Labels / RCU_Labels), selected with --labels-import:
#   g.<seq>#0           ->  ev0 (il Init <seq>)
#   t<t>.<seq>#0        ->  ev0 (il (Thr <t>) <seq>)
#   ...#<k>             ->  sub (il <own> <seq>) <k>     (RMW sub-events, k>0)
#   g.<seq>@<lp>:<it>#<k> ->  ev_it Init <seq> <lp> <it> <k>   (loop-iteration)
# and an edge whose endpoints are both NON-loop #0 uses the `edge` abbreviation
# (edge a b = (ev0 a, ev0 b)).  This is exactly the vocabulary the client proofs
# already use, so the generated \<Phi> is definitionally the proof's \<Phi>.
# Loop-iteration labels (with @loop:iter) render via `ev_it`, whose elabel
# records the enclosing loop (ilo_loops = [<lp>]) and the iteration
# (el_iters = [<it>]); the labels theory must provide that helper.

def _scope_owner(scope):
    """Map an event-label scope fragment ('g' / 't<tid>') to a Core `owner` term,
    or None if unrecognised."""
    if scope == "g":
        return "Init"
    if len(scope) > 1 and scope[0] == "t" and scope[1:].isdigit():
        return "(Thr %s)" % scope[1:]
    return None


def _core_iloc_term(instr, loop):
    """Render a NON-loop instruction-label (e.g. 'g.3' / 't1.3') as an `il OWN
    SEQ` Core term, or None if it carries a loop suffix / is unrecognised.

    A loop suffix is intentionally NOT renderable as a plain `il` (which fixes
    ilo_loops = []): loop-iteration event-labels go through `_core_evlabel_term`
    / `_core_edge_term`, which use the `ev_it` helper instead.  Returning None
    here guards against silently dropping the loop component."""
    if loop is not None:
        return None
    scope, _, seq = instr.partition(".")
    if not seq.isdigit():
        return None
    own = _scope_owner(scope)
    if own is None:
        return None
    return "il %s %s" % (own, seq)


def _core_evlabel_term(lbl):
    """Render an event-label as a Core `elabel` term (or None).

    Three cases:
      * non-loop, k=0   ->  ev0 (il OWN SEQ)
      * non-loop, k>0   ->  sub (il OWN SEQ) k
      * loop-iteration  ->  ev_it OWN SEQ LOOP ITER k

    `ev_it` (a shared helper in the labels theory) builds the elabel whose iloc
    records the enclosing loop (ilo_loops = [LOOP]) and whose el_iters records
    the iteration ([ITER]); see MORDOR_ISA_FORMAT.md s2/s4 for the label grammar
    g.<seq>@<loop>:<iter>#<k>."""
    d = parse_evlabel(lbl)
    if d is None:
        return None
    if d["loop"] is not None:
        scope, _, seq = d["instr"].partition(".")
        if not seq.isdigit():
            return None
        own = _scope_owner(scope)
        if own is None:
            return None
        return "ev_it %s %s %s %s %s" % (own, seq, d["loop"], d["iter"], d["k"])
    iloc = _core_iloc_term(d["instr"], d["loop"])
    if iloc is None:
        return None
    k = int(d["k"])
    return "ev0 (%s)" % iloc if k == 0 else "sub (%s) %d" % (iloc, k)


def _core_edge_term(src, dst):
    """Render one edge.  A both-#0, NON-loop edge uses the `edge` abbreviation
    over ilocs; otherwise an explicit (elabel, elabel) pair built from
    `_core_evlabel_term` (which handles loop-iteration labels via `ev_it`).
    None if unrenderable."""
    ds, dt = parse_evlabel(src), parse_evlabel(dst)
    if (ds and dt and ds["k"] == "0" and dt["k"] == "0"
            and ds["loop"] is None and dt["loop"] is None):
        il_s = _core_iloc_term(ds["instr"], ds["loop"])
        il_t = _core_iloc_term(dt["instr"], dt["loop"])
        if il_s and il_t:
            return "edge (%s) (%s)" % (il_s, il_t)
    es, et = _core_evlabel_term(src), _core_evlabel_term(dst)
    if es and et:
        return "(%s, %s)" % (es, et)
    return None


def render_core_phi(doc, theory_name, derived_edges=None, labels_import="UAF_Labels"):
    """Render ONLY the future set \<Phi>, over Core elabel types, importing the
    shared label helpers (`il`/`ev0`/`edge`) from `labels_import`."""
    prog = doc.get("program", "prog")
    frag = sanitize(prog)
    fmt = doc.get("format_version", "?")
    out = []
    a = out.append

    a("(*")
    a("  GENERATED FILE -- do not hand-edit.")
    a("")
    a("  Rendered by scripts/generate_phi.py --core (REWORK_PLAN.md s5 / W3) from a")
    a("  mordor isa-mode JSON document (schema v%s, docs/MORDOR_ISA_FORMAT.md)." % fmt)
    a("  Source program : %s" % prog)
    a("")
    a("  Emits \\<Phi>_%s over the REAL Core @{typ elabel} types (via the shared" % frag)
    a("  label helpers il/ev0/edge in %s), so the client proof consumes it" % labels_import)
    a("  directly: g.<seq>#0 = ev0 (il Init <seq>), t<t>.<seq>#0 = ev0 (il (Thr t) <seq>).")
    if derived_edges:
        a("")
        a("  \\<Phi> is ENRICHED with cross-thread release-handshake edges DERIVED from")
        a("  mordor's per-execution reads-from (release-class writer); flagged inline.")
    a("*)")
    a("")
    a("theory %s" % theory_name)
    a("  imports %s" % labels_import)
    a("begin")
    a("")
    a(r"text \<open>The future set \<open>\<Phi>_%s\<close> over Core @{typ elabel}, one" % frag)
    a(r"  edge-set per execution; rendered from the mordor isa JSON.\<close>")
    a("")

    exec_defs = []
    for fut in doc.get("futures", []):
        ex = fut["execution"]
        ename = "\\<Phi>_%s_exec%d" % (frag, ex)
        exec_defs.append(ename)
        edges = normalise_edges(fut.get("edges", []), ctx=" (exec %s)" % ex)
        applied = []
        if derived_edges:
            labels = {l for (s, t) in edges for l in (s, t)}
            for (s, t) in sorted(derived_edges):
                if s in labels and t in labels and (s, t) not in edges:
                    edges.append((s, t))
                    applied.append((s, t))
        rows = []
        for (s, t) in edges:
            term = _core_edge_term(s, t)
            if term is None:
                raise ValueError("cannot render core edge %s -> %s "
                                 "(unrecognised event-label grammar)"
                                 % (s, t))
            rows.append("  " + term)
        if applied:
            a(r"text \<open>exec %s: +%d derived release-handshake edge(s): %s\<close>"
              % (ex, len(applied),
                 "; ".join("%s \\<rightarrow> %s" % e for e in applied)))
        a("definition %s :: future where" % ename)
        if rows:
            a("  \"%s =" % ename)
            a("  {")
            a(",\n".join(rows))
            a("  }\"")
        else:
            a("  \"%s = {}\"" % ename)
        a("")

    a("definition \\<Phi>_%s :: Phi where" % frag)
    if exec_defs:
        a("  \"\\<Phi>_%s =" % frag)
        a("  { " + ",\n    ".join(exec_defs) + " }\"")
    else:
        a("  \"\\<Phi>_%s = {}\"" % frag)
    a("")
    a("end")
    a("")
    return "\n".join(out)


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("input", help="mordor isa-mode JSON document")
    p.add_argument("-o", "--output", help="output .thy file (default: stdout)")
    p.add_argument("--theory", help="Isabelle theory name (default: derived)")
    p.add_argument("--executions", metavar="EXEC.json",
                   help="companion mordor executions-mode JSON; enables deriving "
                        "cross-thread release handshake edges from its rf relation")
    p.add_argument("--core", action="store_true",
                   help="emit ONLY \\<Phi> over the REAL Core elabel types (via the "
                        "shared label helpers in --labels-import), for direct client "
                        "consumption, instead of the provisional string-labelled theory")
    p.add_argument("--labels-import", default="UAF_Labels",
                   help="theory providing il/ev0/edge for --core (default: UAF_Labels)")
    args = p.parse_args(argv)

    try:
        with open(args.input) as f:
            doc = json.load(f)
    except (OSError, ValueError) as exc:
        sys.stderr.write("error: cannot read isa JSON %r: %s\n"
                         % (args.input, exc))
        return 2

    if not isinstance(doc, dict):
        sys.stderr.write("error: isa document must be a JSON object, got %s\n"
                         % type(doc).__name__)
        return 2

    fmt = doc.get("format_version")
    if fmt != "0.1":
        sys.stderr.write(
            "warning: format_version is %r; this renderer targets schema "
            "v0.1 (MORDOR_ISA_FORMAT.md)\n" % (fmt,))

    if args.theory:
        theory_name = args.theory
    elif args.output:
        theory_name = os.path.splitext(os.path.basename(args.output))[0]
    else:
        theory_name = "Prog_%s_generated" % sanitize(doc.get("program", "prog"))

    derived = None
    if args.executions:
        try:
            with open(args.executions) as f:
                exec_doc = json.load(f)
        except (OSError, ValueError) as exc:
            sys.stderr.write("error: cannot read executions JSON %r: %s\n"
                             % (args.executions, exc))
            return 2
        derived, warns = derive_handshake_edges(doc, exec_doc)
        for w in warns:
            sys.stderr.write("warning (handshake): %s\n" % w)
        sys.stderr.write(
            "derived %d release-handshake edge(s) from %s: %s\n"
            % (len(derived), args.executions,
               ", ".join("%s->%s" % e for e in sorted(derived)) or "(none)"))

    try:
        if args.core:
            text = render_core_phi(doc, theory_name, derived_edges=derived,
                                   labels_import=args.labels_import)
        else:
            text = render_theory(doc, theory_name, derived_edges=derived)
    except (ValueError, KeyError) as exc:
        sys.stderr.write("error: failed to render %r: %s\n"
                         % (args.input, exc))
        return 2

    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
        sys.stderr.write("wrote %s (theory %s)\n" % (args.output, theory_name))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
