#!python

import re

pc = [p.strip() for p in """
  I1 | I2 | I3 | I4 | I5 | I6 | I7 | I8 | I9 
  | I10 | I11 | cas_res | I12  
  | R1 | R2 | R3 | R4 | R5
  | S1 | S2 | S3 | S4 | S5 | S6 | S7
  | I13 | I14
""".split("|") if p.strip() != ""]

pc_order = {p: i for i, p in enumerate(pc)}

ppo = [
  (("I1", "None"), ("I8", "None")),
  (("I2", "None"), ("I4", "None")),
  (("I3", "None"), ("I8", "None")),
  (("I4", "None"), ("I8", "None")),
  (("I5", "None"), ("I6", "None")),
  (("I6", "None"), ("I7", "None")),
  (("I7", "None"), ("I8", "None")),
  (("I8", "None"), ("I9", "None")),
  (("I9", "None"), ("I10", "None")),
  (("I10", "None"), ("I11", "None")),
  (("I11", "None"), ("cas_res", "None")),
  (("R1", "None"), ("R4", "None")),
  (("R1", "None"), ("R5", "None")),
  (("S1", "None"), ("S3", "None")),
  (("S2", "None"), ("S3", "None")),
  (("S3", "None"), ("S5", "None")),
  (("S4", "None"), ("S5", "None")),
  (("S6", "None"), ("S7", "None"))
]

dp = [
  (("cas_res", "None"), ("I12", "None")),
  (("cas_res", "None"), ("R1", "None")),
  (("cas_res", "None"), ("R2", "None")),
  (("R2", "None"), ("R3", "None")),
  (("R3", "None"), ("S1", "None")),
  (("R3", "None"), ("S2", "None")),
  (("R3", "None"), ("I13", "None")),
  (("R3", "None"), ("S1", "None")),
  (("R4", "None"), ("R5", "None")),
  (("R4", "None"), ("I13", "None")),
  (("S5", "None"), ("S4", "None")),
  (("S5", "None"), ("S6", "None")),
  (("S7", "None"), ("S6", "None")),
  (("S7", "None"), ("R4", "None")),
  (("R4", "None"), ("R5", "None")),
  (("R4", "None"), ("I13", "None"))
]

diag = [((p, "None"), (p, "None")) for p in pc]

rel = ppo + dp + diag

def sort_history(history):
    return sorted(history, key=lambda x: pc_order[x])

def history_to_str(history):
    return "[" + ",".join(history) + " ]"

def futures_to_str(futures):
    return "{{\n    " + ",\n    ".join([
        "((" + a + "," + b + "),(" + c + "," + d + "))" 
        for ((a,b),(c,d)) in futures
    ]) + "\n  }}"

def get_future_name(history):
    history = sort_history(history)
    initials = sorted(set([step[0:1] for step in history]))
    name = "F_"
    for initial in initials:
        name += initial + "".join([step[1:] for step in history if step[0:1] == initial])

    name = name.replace("1234567891011", "c")
    name = name.replace("1234567", "b")
    if re.match(r'F_I[0-9]', name):
        name = name.replace("F_I", "F_Ia")
    if name == "F_":
        name = "F_Ia"

    return name

def get_horizon(history):
    future = [pair 
              for pair in rel 
              if pair[0][0] not in history
    ]
    ran = [pair[1] 
           for pair in future 
           if pair[0] != pair[1]
    ]
    future = [pair
              for pair in future
              if pair[0] not in ran
    ]
    future = [pair
               for pair in future
               if pair[0] != pair[1]
               or len([p for p in future if p[0] == pair[0]]) == 1]
    return future

def extend_histories(history, horizon):
    histories = [sort_history(set(history + [pair[0][0]])) for pair in horizon]
    return histories

def get_all_futures():
    futures_with_histories = {
            get_future_name([]): ([], get_horizon([]))}
    for _ in range(100):
        new_futures_with_histories = []
        for (history, futures) in futures_with_histories.values():
            new_futures_with_histories += [(h, get_horizon(h)) for h in extend_histories(history, futures)]
        for (history, futures) in new_futures_with_histories:
            futures_with_histories[get_future_name(history)] = (history, futures)

    return futures_with_histories

def print_futures_datatype(all_futures):
    print("datatype Futures =")
    print("   F_e")
    for name in all_futures.keys():
        print(" | " + name)
    print(" | F_fail")
    print("")
    print("definition \"futures_list = [")
    print("   F_e")
    for name in all_futures.keys():
        print(" , " + name)
    print(" , F_fail")
    print("]\"")
    print("\n")

def print_futures_to_lines(all_futures):
    print("fun futures_to_lines :: \"Futures \\<Rightarrow> ((PC \\<times> Value option) \\<times> (PC \\<times> Value option)) set set\" where")
    print("\"futures_to_lines F_e = \n  {{}}\" |")
    for (name, (history, future)) in all_futures.items():
        print("\"futures_to_lines " + name + " =")
        print ("  " + futures_to_str(future) + "\" |")
    print("\"futures_to_lines F_fail = undefined\"")
    print("\n")

def print_futures_with_history(all_futures):
    print("definition \"futures_with_history \\<equiv> {")
    print(",\n".join(["  (" + history_to_str(history) + ", futures_to_lines " + name + ")" 
          for (name, (history, future)) in all_futures.items()]))
    print("}\"")
    print("\n")

def print_futures_by_history(all_futures):
    print("definition futures_by_history :: \"History \\<Rightarrow> (((PC \\<times> nat option) \\<times> PC \\<times> nat option) set set) option\" where")
    print("\"futures_by_history h \\<equiv>")
    print("\n  else ".join(["if h = " + history_to_str(history) + " then Some (futures_to_lines " + name + ")" 
          for (name, (history, future)) in all_futures.items()]))
    print("  else None")
    print("\"")
    print("\n")

def print_futures_to_lines_uniq(all_futures):
    duplicates = []
    for name1 in all_futures.keys():
        for name2 in all_futures.keys():
            if name1 != name2:
                if all_futures[name1][1] == all_futures[name2][1]:
                    duplicates += [(name1, name2)]
                    print("Equal futures: " + name1 + " " + name2)

    print("lemma futures_to_line_unique:")
    print("assumes \"F1 \\<noteq> F2\"")
    print("assumes \"F1 \\<noteq> F_fail\"")
    print("assumes \"F2 \\<noteq> F_fail\"")
    for (name1, name2) in duplicates:
        print("assumes \"F1 = " + name1 + " \\<longrightarrow> F2 \\<noteq> " + name2 + "\"")
        print("assumes \"F1 = " + name2 + " \\<longrightarrow> F2 \\<noteq> " + name1 + "\"")
    print("shows \"futures_to_lines F1 \\<noteq> futures_to_lines F2\"")
    print("\n")

def print_preconds(all_futures):
    print("definition preCond h ms t \\\\<equiv>")
    print("\n  else ".join([
        "if h = " + history_to_str(history) + " then pre_" + name + " ms t" 
        for (name, (history, future)) in all_futures.items()
    ]))
    print("  else False")
    print("\"")
    print("\n")
    print("lemmas preconds =")
    for (name, (history, future)) in all_futures.items():
        print("  pre_" + name + "_def")
    print("\n")


def print_sigma_obs(all_futures):
    print("definition \"sigma_obs ms \\<sigma> t \\<equiv>")
    print("\n  else ".join([
        "if history ms t = " + history_to_str(history) + " then [(rcu_0 + t) =\\<^sub>t 1] \\<sigma>" 

        for (name, (history, future)) in all_futures.items()
        if ("I12" not in history and "I7" in history
            or "I6" not in history and "I5" in history)
    ]))
    print("  else [(rcu_0 + t) =\\<^sub>t 0] \\<sigma>")
    print("\"")

all_futures = get_all_futures()

#print (all_futures)
print_futures_datatype(all_futures)
print_futures_to_lines(all_futures)
print_futures_with_history(all_futures)
print_futures_by_history(all_futures)
print_futures_to_lines_uniq(all_futures)
print_preconds(all_futures)
print_sigma_obs(all_futures)

print("\n")
print(str(len(all_futures)) + " futures generated")
