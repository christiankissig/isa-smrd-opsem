(*  Title:      Core/Core.thy
    Author:     RCU-C11-OpSem project (Episodic stack, layer 1: Core)

    Shared vocabulary for the Episodic-Loops operational semantics: program
    labels (the paper's (pc, loopfun, iter)), memory orders, expressions, the
    abstract action alphabet (what Phi and histories are built on), the abstract
    command language, and the digested `LABEL is INSTRUCTION` program.  No
    semantics live here -- MemSem owns action effects, EventStruct owns Phi, OpSem
    owns the step relation; all are written against these types.

    Frozen per docs/SPIKE_B_label_digest_design.md (the Core public API) and
    REWORK_PLAN.md sec 4.  Depends only on HOL (imports Main).

    Constructor names are de-clashed for a single namespace: `Assign` (not `Set`),
    `IfElse` (not HOL's `If`), and the command-level fence is `CFence` (the
    action-level one is `Fence`).
*)

theory Core
  imports Main "HOL-Library.Product_Lexorder" "HOL-Library.List_Lexorder"
begin

section \<open>Program labels\<close>

text \<open>The paper's formal label is @{text "(pc(l), loopfun(l), iter(l))"} with
  @{text "pc(l)"} a derived program point, not a hand-coded enum (REWORK sec 4).
  We split it into a STATIC instruction-label @{text iloc} (the digest key, =
  mordor @{text "t<tid>.<seq>"} + its enclosing loops) and a DYNAMIC event-label
  @{text elabel} = @{text iloc} + iteration-vector + sub-event index (the key of
  @{text Phi} and histories; an RMW instruction has several event-labels).\<close>

type_synonym tid    = nat
type_synonym loopid = nat
type_synonym iter   = nat

text \<open>Who owns an instruction: the thread-less init/preamble (mordor @{text "g.*"})
  or a thread.\<close>
datatype owner = Init | Thr tid

text \<open>Rank an owner: @{term Init} before all threads, threads by tid.  This is also
  the canonical linear order on owners (@{term Init} @{text "<"} all @{term Thr},
  threads by @{typ tid}).\<close>
fun owner_rank :: "owner \<Rightarrow> nat" where
  "owner_rank Init    = 0"
| "owner_rank (Thr t) = Suc t"

lemma owner_rank_inj: "owner_rank a = owner_rank b \<Longrightarrow> a = b"
  by (cases a; cases b) auto

instantiation owner :: linorder
begin
definition "less_eq_owner a b \<longleftrightarrow> owner_rank a \<le> owner_rank b"
definition "less_owner a b \<longleftrightarrow> owner_rank a < owner_rank b"
instance
  by intro_classes (auto simp: less_eq_owner_def less_owner_def owner_rank_inj)
end

text \<open>Static instruction-label = the digest key.  @{text ilo_loops} lists the
  enclosing loops, innermost LAST (empty outside loops).\<close>
record iloc =
  ilo_owner :: owner
  ilo_seq   :: nat
  ilo_loops :: "loopid list"

text \<open>Dynamic event-label = the paper's @{text "l = (pc, loopfun, iter)"}.
  @{text el_iters} carries one iteration per enclosing loop (same order as
  @{text ilo_loops}); @{text el_k} is the sub-event index (RMW: 0,1,2).\<close>
record elabel =
  el_iloc  :: iloc
  el_iters :: "iter list"
  el_k     :: nat

text \<open>The projections the step rules use.\<close>
definition pc :: "elabel \<Rightarrow> nat \<times> nat" where
  "pc l = (ilo_seq (el_iloc l), el_k l)"

definition loopfun :: "elabel \<Rightarrow> loopid list" where
  "loopfun l = ilo_loops (el_iloc l)"

definition iterf :: "elabel \<Rightarrow> loopid \<rightharpoonup> iter" where
  "iterf l = map_of (zip (ilo_loops (el_iloc l)) (el_iters l))"


subsection \<open>Canonical linear order on labels\<close>

text \<open>A self-contained @{class linorder} on the label types, so that downstream
  layers may form sorted lists, @{term Max}, and label sets.  The order key sorts
  by @{term owner_rank} first (@{term Init} before threads), then the syntactic
  loop nesting / iteration vector / position fields.  This is the CANONICAL order;
  the program-FAITHFUL order (where outer-loop iteration dominates inner-loop
  position, keyed by the static @{text hdr} table) is @{term elabel_lt} below.

  Records are tuples under a hidden polymorphic ``more'' slot, so the instance is
  declared on the @{text "_ext"} type constructor; @{typ iloc} = @{text "unit
  iloc_ext"} and @{typ elabel} = @{text "unit elabel_ext"} inherit it.\<close>

definition iloc_key :: "'a iloc_scheme \<Rightarrow> owner \<times> nat \<times> loopid list \<times> 'a" where
  "iloc_key r = (ilo_owner r, ilo_seq r, ilo_loops r, iloc.more r)"

lemma iloc_key_inj: "iloc_key x = iloc_key y \<Longrightarrow> x = y"
  by (rule iloc.equality) (simp_all add: iloc_key_def)

instantiation iloc_ext :: (linorder) linorder
begin
definition "less_eq_iloc_ext (a::'a iloc_ext) b \<longleftrightarrow> iloc_key a \<le> iloc_key b"
definition "less_iloc_ext (a::'a iloc_ext) b \<longleftrightarrow> iloc_key a < iloc_key b"
instance
  by intro_classes
     (auto simp: less_eq_iloc_ext_def less_iloc_ext_def less_le_not_le
                 iloc_key_inj order_trans antisym)
end

definition elabel_key :: "'a elabel_scheme \<Rightarrow> iloc \<times> iter list \<times> nat \<times> 'a" where
  "elabel_key r = (el_iloc r, el_iters r, el_k r, elabel.more r)"

lemma elabel_key_inj: "elabel_key x = elabel_key y \<Longrightarrow> x = y"
  by (rule elabel.equality) (simp_all add: elabel_key_def)

instantiation elabel_ext :: (linorder) linorder
begin
definition "less_eq_elabel_ext (a::'a elabel_ext) b \<longleftrightarrow> elabel_key a \<le> elabel_key b"
definition "less_elabel_ext (a::'a elabel_ext) b \<longleftrightarrow> elabel_key a < elabel_key b"
instance
  by intro_classes
     (auto simp: less_eq_elabel_ext_def less_elabel_ext_def less_le_not_le
                 elabel_key_inj order_trans antisym)
end


section \<open>Memory orders, registers, values, expressions\<close>

datatype mem_order = Rlx | Acq | Rel | Acq_rel | Sc

type_synonym reg  = string   \<comment> \<open>register name (mordor "reg")\<close>
type_synonym var  = string   \<comment> \<open>global symbolic variable x (read-var / write-var)\<close>
type_synonym sym  = nat      \<comment> \<open>symbolic value / symbolic location returned by alloc\<close>
type_synonym valu = int      \<comment> \<open>concrete integer literal\<close>

text \<open>Expressions; a boolean expression is just an expression (the condition slot).\<close>
datatype expr =
    EInt  int
  | EReg  reg
  | ESym  sym
  | EDeref expr
  | EAdd  expr expr | ESub expr expr | EMul expr expr | EDiv expr expr
  | EEq   expr expr | ELeq expr expr
  | ENot  expr      | EAnd expr expr | EOr  expr expr

type_synonym bexp = expr


section \<open>Actions (the level Phi and the memory transition are built on)\<close>

text \<open>One constructor per @{text "rules/actions:*"}.  Locations are symbolic
  (@{typ sym}) -- the evaluated targets, matching @{text "sigma.viswrite : Sym \<rightharpoonup> Write"}.\<close>
datatype action =
    Read    mem_order sym sym     \<comment> \<open>@{text "R_o x alpha"}: read symbol @{text alpha} at @{text x}\<close>
  | Write   mem_order sym expr    \<comment> \<open>@{text "W_o x e"}\<close>
  | Branch  bexp                  \<comment> \<open>guard / branch (leaves sigma fixed)\<close>
  | Fence   mem_order
  | AllocA  sym expr
  | DeallocA sym


section \<open>Commands and instructions\<close>

text \<open>One constructor per @{text "rules/commands:*"}, operand-generic (no baked
  @{text C}/@{text var_s}).  @{text IfElse}/@{text While} keep the program ROLLED:
  their bodies are themselves instruction lists.  @{text While} records its
  @{text loopid} (mordor @{text loop_id}).\<close>
datatype command =
    Assign   reg expr                                \<comment> \<open>i := e (no event)\<close>
  | ReadVar  mem_order reg var
  | ReadPtr  mem_order reg expr
  | ReadRef  reg var                                 \<comment> \<open>i := &x (no event)\<close>
  | WriteVar mem_order var expr
  | WritePtr mem_order expr expr
  | CFence   mem_order
  | Faa      mem_order mem_order reg expr expr
  | Cas      mem_order mem_order reg expr expr expr
  | Malloc   reg expr
  | Free     reg
  | IfElse   bexp "instr list" "instr list"
  | While    loopid bexp "instr list"
and instr = Instr (instr_loc: iloc) (instr_cmd: command)

text \<open>How many event-labels an instruction stands for (the @{text iloc}-to-@{text elabel}
  link): @{text Assign}/@{text ReadRef} emit none, @{text Faa} two, @{text Cas} three (the
  W is absent on a failing CAS, decided at step time), everything else one.\<close>
fun n_events :: "command \<Rightarrow> nat" where
  "n_events (Assign _ _)       = 0"
| "n_events (ReadRef _ _)      = 0"
| "n_events (Faa _ _ _ _ _)    = 2"
| "n_events (Cas _ _ _ _ _ _)  = 3"
| "n_events _                  = 1"


section \<open>The digested program\<close>

text \<open>The whole digest is an instruction list; the @{text owner} in each
  @{text iloc} separates the init preamble from each thread.\<close>
type_synonym program = "instr list"

text \<open>The paper's @{text "prog(o)"}: the rolled per-owner command map.\<close>
definition prog :: "program \<Rightarrow> owner \<Rightarrow> iloc \<rightharpoonup> command" where
  "prog P own =
     map_of (map (\<lambda>i. (instr_loc i, instr_cmd i))
                 (filter (\<lambda>i. ilo_owner (instr_loc i) = own) P))"

text \<open>The readable digest constructor @{text "LABEL is INSTRUCTION"}.  (Spike B
  residual 1, RESOLVED: the @{text "is"} mixfix delimiter parses cleanly in batch
  -- Isar's @{text "is"} is a command-level term-abbreviation keyword, not inner
  term syntax, so it does NOT clash.  The @{text "\<triangleq>"} fallback proved
  unnecessary.)\<close>
definition is_entry :: "iloc \<Rightarrow> command \<Rightarrow> instr"  ("(_ is/ _)" [61, 60] 60)
  where "is_entry l c = Instr l c"

lemma is_entry_simps [simp]:
  "instr_loc (l is c) = l" "instr_cmd (l is c) = c"
  by (simp_all add: is_entry_def)


section \<open>Label algebra for loop-boundary detection\<close>

text \<open>The paper orders labels lexicographically over loop indices to detect
  loop-boundary crossings.  We expose the order KEY and the @{text "iter(H)"}
  projection here; @{term okey} is parameterised by the static @{text hdr} table
  (loop-id to its @{text While} header @{text seq}) extracted once from a digest.

  Two orders coexist by design.  The CANONICAL @{class linorder} on @{typ elabel}
  (above, by @{term elabel_key}) is @{text hdr}-free, total, and good enough for
  sorted lists / @{term Max} / set machinery downstream.  The program-FAITHFUL
  order @{term elabel_lt} below threads the static @{text hdr} table so that an
  OUTER loop's iteration dominates an inner loop's position (the property the
  @{text lb} rule needs); its faithfulness for NESTED loops is unvalidated until
  the first RCU @{text Phi} exists (Spike B residual 2, Phi_RCU-gated), which is
  precisely why it stays a parameterised predicate rather than the typeclass
  order.\<close>

definition okey :: "(loopid \<Rightarrow> nat) \<Rightarrow> elabel \<Rightarrow> (nat \<times> nat) list" where
  "okey hdr l =
     map (\<lambda>(lp, i). (hdr lp, i)) (zip (rev (ilo_loops (el_iloc l))) (rev (el_iters l)))
     @ [(ilo_seq (el_iloc l), el_k l)]"

text \<open>The program-relative strict order on event-labels: lexicographic on
  @{term "(owner_rank, okey hdr)"}.\<close>
definition elabel_lt :: "(loopid \<Rightarrow> nat) \<Rightarrow> elabel \<Rightarrow> elabel \<Rightarrow> bool" where
  "elabel_lt hdr a b \<longleftrightarrow>
     (owner_rank (ilo_owner (el_iloc a)), okey hdr a)
       < (owner_rank (ilo_owner (el_iloc b)), okey hdr b)"

text \<open>The @{text lb} guard's per-loop iteration maximum over a history.\<close>
definition iter_H :: "(elabel \<times> action) set \<Rightarrow> loopid \<Rightarrow> iter" where
  "iter_H H lp = Max (insert 0 {i. \<exists>l a. (l, a) \<in> H \<and> iterf l lp = Some i})"

end
