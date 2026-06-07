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
import sys


# --------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------

def iss(s):
    """Render a python str as an Isabelle ''...'' string literal."""
    return "''%s''" % s


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

def render_command(cmd, indent):
    """Render one command.  `indent` is the column of the enclosing digest
    entry; nested control-flow digests are indented relative to it."""
    op = cmd["op"]

    if op == "Set":
        return "Set %s %s" % (iss(cmd["dst"]), render_expr(cmd["expr"]))
    if op == "ReadPtr":
        return "ReadPtr %s %s %s" % (cmd["order"], iss(cmd["dst"]),
                                     render_expr(cmd["ptr"]))
    if op == "ReadVar":
        return "ReadVar %s %s %s" % (cmd["order"], iss(cmd["dst"]),
                                     iss(cmd["var"]))
    if op == "ReadRef":
        return "ReadRef %s %s" % (iss(cmd["dst"]), iss(cmd["var"]))
    if op == "WritePtr":
        return "WritePtr %s %s %s" % (cmd["order"], render_expr(cmd["ptr"]),
                                      render_expr(cmd["val"]))
    if op == "WriteVar":
        return "WriteVar %s %s %s" % (cmd["order"], iss(cmd["var"]),
                                      render_expr(cmd["val"]))
    if op == "Faa":
        # NB: schema field "rmw_op" (strong/weak) is not rendered (see header).
        return "Faa %s %s %s %s %s" % (cmd["order_r"], cmd["order_w"],
                                       iss(cmd["dst"]), render_expr(cmd["loc"]),
                                       render_expr(cmd["addend"]))
    if op == "Cas":
        return "Cas %s %s %s %s %s %s" % (
            cmd["order_r"], cmd["order_w"], iss(cmd["dst"]),
            render_expr(cmd["loc"]), render_expr(cmd["expected"]),
            render_expr(cmd["new"]))
    if op == "Alloc":
        return "Alloc %s %s" % (iss(cmd["dst"]), render_expr(cmd["size"]))
    if op == "Free":
        return "Free %s" % render_expr(cmd["ptr"])
    if op == "Fence":
        return "Fence %s" % cmd["order"]
    if op == "If":
        sub = indent + "    "
        then_d = render_digest(cmd.get("then", []), sub)
        else_d = render_digest(cmd.get("else", []), sub)
        return "If %s\n%s%s\n%s%s" % (render_expr(cmd["cond"]),
                                      sub, then_d, sub, else_d)
    if op in ("While", "Do"):
        ctor = "While" if op == "While" else "Do"
        sub = indent + "    "
        body_d = render_digest(cmd.get("body", []), sub)
        return "%s %s\n%s%s\n%s(%d)" % (ctor, render_expr(cmd["cond"]),
                                        sub, body_d, sub, cmd["loop_id"])

    raise ValueError("unknown command op: %r" % (op,))


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


def render_theory(doc, theory_name):
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
    a("")
    a("  Notes / faithfulness:")
    a("    * RMW (Faa/Cas) is ONE instruction carrying several events (#0,#1,#2).")
    a("    * Loop-iteration event-labels (e.g. t0.4@1:1#0) are rendered verbatim in \\<Phi>.")
    a("    * Edges are rendered as in the JSON; reflexive (identity) closure is left to")
    a("      the consumer (MORDOR_ISA_FORMAT.md s1).")
    a("    * Faa/Cas `rmw_op` (strong/weak) is present in the schema but NOT rendered here.")
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
    a(r"text \<open>Event \<open>\<rightarrow>\<close> instruction map (event-label, instruction-label, type).\<close>")
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
    a("")

    exec_defs = []
    for fut in doc.get("futures", []):
        ex = fut["execution"]
        ename = "\\<Phi>_%s_exec%d" % (frag, ex)
        exec_defs.append(ename)
        a("definition %s :: \"(string \\<times> string) set\" where" % ename)
        edges = fut.get("edges", [])
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
# main
# --------------------------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("input", help="mordor isa-mode JSON document")
    p.add_argument("-o", "--output", help="output .thy file (default: stdout)")
    p.add_argument("--theory", help="Isabelle theory name (default: derived)")
    args = p.parse_args(argv)

    with open(args.input) as f:
        doc = json.load(f)

    if args.theory:
        theory_name = args.theory
    elif args.output:
        theory_name = os.path.splitext(os.path.basename(args.output))[0]
    else:
        theory_name = "Prog_%s_generated" % sanitize(doc.get("program", "prog"))

    text = render_theory(doc, theory_name)

    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
        sys.stderr.write("wrote %s (theory %s)\n" % (args.output, theory_name))
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
