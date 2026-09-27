#!/usr/bin/env python3
"""W3/Spike A: MoRDor -> labelled Phi bridge, demonstrated on the UAF example.
Joins `executions` (event table + ppo/dp) into a labelled future set, cross-checks
against `futures`, and shows the bug-vs-fix horizon difference."""
import json, sys, re

def load(path):
    s = open(path).read(); s = s[s.find('{'):]
    return json.loads(s)

def load_futures(path):
    # futures JSON uses (e1,e2) tuple syntax, not strict JSON -> normalise
    s = open(path).read(); s = s[s.find('{'):]
    s = s.replace('(', '[').replace(')', ']')
    return json.loads(s)

def desc(ev):
    t = ev['type']; loc = ev.get('location','');
    val = ev.get('rval', ev.get('wval',''))
    names = {'I':'init','A':'alloc','W':'W','R':'R','D':'free','T':'fin'}
    base = names.get(t, t)
    if t in ('W','R'): return f"{base} {loc}={val}"
    if t in ('A','D'): return f"{base}({loc})"
    return base

def analyse(name, exec_path, fut_path):
    print(f"\n{'='*70}\n{name}\n{'='*70}")
    d = load(exec_path); execs = d['executions']
    fut = load_futures(fut_path)
    nfut = sum(len(e['futures']) for e in fut['executions'])
    print(f"executions: {len(execs)}   futures (from `futures`): {nfut}")

    # global id -> label (consistent across execs)
    idlabel = {}
    for ex in execs:
        for ev in ex['events']:
            idlabel[ev['id']] = desc(ev)

    # cross-check: future relation == identity ∪ (ppo∪dp) for some execution
    fut_sets = []
    for e in fut['executions']:
        for f in e['futures']:
            fut_sets.append(frozenset(tuple(p) for p in f))
    matched = 0
    for ex in execs:
        ids = [ev['id'] for ev in ex['events']]
        edges = set(map(tuple, ex['ppo'])) | set(map(tuple, ex['dp']))
        edges |= {(i,i) for i in ids}            # identity
        if frozenset(edges) in fut_sets: matched += 1
    print(f"cross-check: {matched}/{len(execs)} executions' (id ∪ ppo∪dp) match a `futures` entry")

    # locate the freed location and demonstrate the (un)ordering of free vs its deref
    for ex in execs:
        ids = [ev['id'] for ev in ex['events']]
        edges = set(map(tuple, ex['ppo'])) | set(map(tuple, ex['dp']))
        # reachability in ppo∪dp
        succ = {i:set() for i in ids}
        for a,b in edges:
            if a in succ: succ[a].add(b)
        def reach(a,b):
            seen=set(); stack=[a]
            while stack:
                x=stack.pop()
                for y in succ.get(x,()):
                    if y==b: return True
                    if y not in seen: seen.add(y); stack.append(y)
            return False
        frees = [ev for ev in ex['events'] if ev['type']=='D']
        for fr in frees:
            loc = fr['location']; fid = fr['id']
            derefs = [ev for ev in ex['events']
                      if ev['type']=='R' and ev.get('location')==loc]
            for dr in derefs:
                did = dr['id']
                f_b_d = reach(fid, did); d_b_f = reach(did, fid)
                if d_b_f: verdict = "deref → free  (SAFE: deref ordered before free)"
                elif f_b_d: verdict = "free → deref  (deref after free)"
                else: verdict = "UNORDERED  ⇒  USE-AFTER-FREE reachable"
                print(f"  exec id={ex['id']:>2}: free(id{fid} {loc}) vs deref(id{did} R {loc}={dr.get('rval')}): {verdict}")

    # horizon at H = ∅ for the first future: minimal events (no proper predecessor)
    ex0 = execs[0]; ids = [ev['id'] for ev in ex0['events']]
    edges = set(map(tuple, ex0['ppo'])) | set(map(tuple, ex0['dp']))
    has_pred = {b for (a,b) in edges if a!=b}
    horizon = [i for i in ids if i not in has_pred]
    print(f"  horizon(H=∅) of exec id={ex0['id']}: " +
          ", ".join(f"id{i}:{idlabel[i]}" for i in sorted(horizon)))

analyse("UAF-BUG (uaf-bug.lit)", "/tmp/uaf_exec.json", "/tmp/uaf_futures.json")
analyse("UAF-FIXED (uaf-bug-fixed.lit)", "/tmp/uaf_fixed_exec.json", "/tmp/uaf_fixed_futures.json")
