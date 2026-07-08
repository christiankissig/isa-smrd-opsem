(*  Title:      OwickiGries/OwickiGries.thy
    Author:     Christian Kissig

    A generic Owicki-Gries / rely-guarantee program logic over an ABSTRACT
    transition system.  Depends only on HOL (imports Main); it is decoupled
    from the Episodic OpSem and the rest of the project, so that it (together
    with the sibling Ownership entry) can be submitted to the AFP on its own.
*)

theory OwickiGries
  imports Main
begin

section \<open>Shallow assertions\<close>

text \<open>An assertion is the set of states satisfying it.  This keeps the logic
  HOL-only and lets assertions mention any component of the (abstract) state.\<close>

type_synonym 's assn = "'s set"


section \<open>The command language (parameterised over abstract atomic actions)\<close>

text \<open>Basic statements are abstract atomic actions of type @{typ 'act}; guards
  are state predicates @{typ "'s set"}.\<close>

datatype ('act, 's) com =
    Atom 'act
  | Skip
  | Seq   "('act,'s) com" "('act,'s) com"
  | Cond  "'s set" "('act,'s) com" "('act,'s) com"
  | While "'s set" "('act,'s) com"


section \<open>The abstract transition-system locale\<close>

text \<open>The single fixed parameter is the atomic-step relation.  It is an
  arbitrary binary relation: NOT assumed total, deterministic, or always
  enabled.  This is what lets a (non-deterministic, horizon-guarded,
  history-dependent) Episodic OpSem step interpret it later (Risk 6).

  Locale inputs: OWN -- @{term astep} (unconstrained, no assumptions at all).
  INHERITED -- none: this is the root of the locale hierarchy used in this
  entry and its sibling @{text Ownership} (@{text ownership_system} below
  extends it); it has no parent locale of its own.\<close>

locale transition_system =
  fixes astep :: "'act \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
begin

subsection \<open>Sequential small-step semantics\<close>

inductive seq_step ::
  "('act,'s) com \<times> 's \<Rightarrow> ('act,'s) com \<times> 's \<Rightarrow> bool"
where
  Atom:   "astep a s s' \<Longrightarrow> seq_step (Atom a, s) (Skip, s')"
| Seq1:   "seq_step (c1, s) (c1', s') \<Longrightarrow> seq_step (Seq c1 c2, s) (Seq c1' c2, s')"
| Seq2:   "seq_step (Seq Skip c2, s) (c2, s)"
| CondT:  "s \<in> b \<Longrightarrow> seq_step (Cond b c1 c2, s) (c1, s)"
| CondF:  "s \<notin> b \<Longrightarrow> seq_step (Cond b c1 c2, s) (c2, s)"
| WhileT: "s \<in> b \<Longrightarrow> seq_step (While b c, s) (Seq c (While b c), s)"
| WhileF: "s \<notin> b \<Longrightarrow> seq_step (While b c, s) (Skip, s)"

subsection \<open>Parallel (interleaving) small-step semantics\<close>

text \<open>A parallel program is a list of sequential commands (one per thread); a
  configuration is the residual thread pool plus the shared state.\<close>

inductive par_step ::
  "(('act,'s) com list \<times> 's) \<Rightarrow> (('act,'s) com list \<times> 's) \<Rightarrow> bool"
where
  Par: "\<lbrakk> i < length cs; seq_step (cs ! i, s) (c', s') \<rbrakk>
          \<Longrightarrow> par_step (cs, s) (cs[i := c'], s')"

abbreviation par_steps ::
  "(('act,'s) com list \<times> 's) \<Rightarrow> (('act,'s) com list \<times> 's) \<Rightarrow> bool"
  where "par_steps \<equiv> par_step\<^sup>*\<^sup>*"

text \<open>A thread is terminated when its residual command is @{const Skip}; the
  whole program has terminated at @{term "replicate n Skip"}.\<close>

end  \<comment> \<open>@{locale transition_system}\<close>


section \<open>Annotated commands (Owicki-Gries proof outlines)\<close>

text \<open>A proof outline annotates each node with the assertion holding before it.
  A basic statement additionally carries its postcondition (the assertion that
  holds after the action), so that stepping does not lose it.\<close>

datatype ('act, 's) ann =
    ABasic "'s set" 'act "'s set"
  | ASkip  "'s set"
  | AComp  "('act,'s) ann" "('act,'s) ann"
  | ACond  "'s set" "'s set" "('act,'s) ann" "('act,'s) ann"
  | AWhile "'s set" "'s set" "('act,'s) ann"

text \<open>@{term pre}: the head assertion of an outline node.\<close>
primrec pre :: "('act,'s) ann \<Rightarrow> 's set" where
  "pre (ABasic P a Q)     = P"
| "pre (ASkip P)          = P"
| "pre (AComp c1 c2)      = pre c1"
| "pre (ACond P b c1 c2)  = P"
| "pre (AWhile P b c)     = P"

text \<open>@{term strip}: the underlying command (assertions erased).\<close>
primrec strip :: "('act,'s) ann \<Rightarrow> ('act,'s) com" where
  "strip (ABasic P a Q)    = Atom a"
| "strip (ASkip P)         = Skip"
| "strip (AComp c1 c2)     = Seq (strip c1) (strip c2)"
| "strip (ACond P b c1 c2) = Cond b (strip c1) (strip c2)"
| "strip (AWhile P b c)    = While b (strip c)"

text \<open>@{term assertions}: every assertion occurring in an outline.  For a basic
  statement this includes its post; for a loop, the exit assertion @{term "P \<inter> - b"}
  (so interference freedom covers the assertion that holds when the loop exits).\<close>
primrec assertions :: "('act,'s) ann \<Rightarrow> 's set set" where
  "assertions (ABasic P a Q)    = {P, Q}"
| "assertions (ASkip P)         = {P}"
| "assertions (AComp c1 c2)     = assertions c1 \<union> assertions c2"
| "assertions (ACond P b c1 c2) = insert P (assertions c1 \<union> assertions c2)"
| "assertions (AWhile P b c)    = insert P (insert (P \<inter> - b) (assertions c))"

text \<open>@{term atomics}: the @{text "(local-precondition, action)"} pair of every
  basic statement -- the atomic accesses a thread's outline can perform.

  This layer is deliberately silent on WHAT an action touches: @{typ 'act} is
  fully abstract here, and there is no notion of a "resource" or of who is
  "acting". A client instantiates that structure on top: the companion
  @{text Ownership} entry sets @{typ 'act} to a pair @{text "'p \<times> 'act"} of an
  acting process (@{typ 'p}, its notion of "thread") and an untagged operation,
  then equips that operation with an @{text acquires}/@{text releases}
  footprint over an abstract resource type @{typ 'r}. Under that
  instantiation, @{term atomics} yields exactly the @{text "(precondition,
  (thread, operation))"} triples the ownership discipline reasons about.\<close>
primrec atomics :: "('act,'s) ann \<Rightarrow> ('s set \<times> 'act) set" where
  "atomics (ABasic P a Q)    = {(P, a)}"
| "atomics (ASkip P)         = {}"
| "atomics (AComp c1 c2)     = atomics c1 \<union> atomics c2"
| "atomics (ACond P b c1 c2) = atomics c1 \<union> atomics c2"
| "atomics (AWhile P b c)    = atomics c"

lemma pre_in_assertions: "pre c \<in> assertions c"
  by (induction c) auto


section \<open>The proof system (in the locale context)\<close>

context transition_system
begin

subsection \<open>Local correctness (sequential Hoare, partial)\<close>

text \<open>The basic rule is in partial-correctness shape: it is vacuous when the
  abstract step is blocked (no successor), so guarded/non-deterministic atomic
  actions are fine.  A basic statement establishes its stored post @{text Q},
  which must entail the demanded post @{text R}.\<close>

inductive loc_correct :: "('act,'s) ann \<Rightarrow> 's set \<Rightarrow> bool" where
  Basic: "\<lbrakk> \<And>s s'. s \<in> P \<Longrightarrow> astep a s s' \<Longrightarrow> s' \<in> Q;  Q \<subseteq> R \<rbrakk>
            \<Longrightarrow> loc_correct (ABasic P a Q) R"
| Skip:  "P \<subseteq> Q \<Longrightarrow> loc_correct (ASkip P) Q"
| Comp:  "\<lbrakk> loc_correct c1 (pre c2); loc_correct c2 Q \<rbrakk>
            \<Longrightarrow> loc_correct (AComp c1 c2) Q"
| Cond:  "\<lbrakk> P \<inter> b \<subseteq> pre c1; P \<inter> (- b) \<subseteq> pre c2;
            loc_correct c1 Q; loc_correct c2 Q \<rbrakk>
            \<Longrightarrow> loc_correct (ACond P b c1 c2) Q"
| While: "\<lbrakk> P \<inter> b \<subseteq> pre c; P \<inter> (- b) \<subseteq> Q; loc_correct c P \<rbrakk>
            \<Longrightarrow> loc_correct (AWhile P b c) Q"

subsection \<open>Interference freedom\<close>

text \<open>An assertion @{term r} of one thread is stable under a foreign atomic
  action @{term "(P,a)"}.\<close>

definition if_pair :: "'s set \<Rightarrow> ('s set \<times> 'act) \<Rightarrow> bool" where
  "if_pair r pa \<longleftrightarrow> (\<forall>s s'. s \<in> r \<inter> fst pa \<longrightarrow> astep (snd pa) s s' \<longrightarrow> s' \<in> r)"

text \<open>Each thread's assertions (incl. its postcondition) survive every other
  thread's atomic actions.

  Note what "thread" means AT THIS LAYER: @{text Ts} is the thread vector,
  @{text "Ts ! i"} is thread @{text i}'s @{text "(outline, postcondition)"}
  pair, and thread identity is simply position in that list -- @{typ nat}, not
  some richer process type. A client that carries its own thread/process tag
  inside @{typ 'act} (as @{text Ownership}'s @{typ 'p} does) must separately
  relate that tag back to the list index @{text i}; see
  @{text Ownership.ownership_interference_free}'s injective @{text
  "proc :: nat \<Rightarrow> 'p"} map and well-tagging discipline for how that bridge is
  built without reopening this generic layer.\<close>

definition interference_free ::
  "(('act,'s) ann \<times> 's set) list \<Rightarrow> bool" where
  "interference_free Ts \<longleftrightarrow>
     (\<forall>i < length Ts. \<forall>j < length Ts. i \<noteq> j \<longrightarrow>
        (\<forall>r \<in> insert (snd (Ts!j)) (assertions (fst (Ts!j))).
           \<forall>pa \<in> atomics (fst (Ts!i)). if_pair r pa))"

subsection \<open>The Owicki-Gries judgement for a thread vector\<close>

definition og_parallel :: "(('act,'s) ann \<times> 's set) list \<Rightarrow> bool" where
  "og_parallel Ts \<longleftrightarrow>
     (\<forall>i < length Ts. loc_correct (fst (Ts!i)) (snd (Ts!i)))
     \<and> interference_free Ts"

definition og_pre :: "(('act,'s) ann \<times> 's set) list \<Rightarrow> 's set" where
  "og_pre Ts = (\<Inter>i \<in> {..< length Ts}. pre (fst (Ts!i)))"

definition og_post :: "(('act,'s) ann \<times> 's set) list \<Rightarrow> 's set" where
  "og_post Ts = (\<Inter>i \<in> {..< length Ts}. snd (Ts!i))"


section \<open>Annotated interleaving semantics (for the safety invariant)\<close>

text \<open>The same interleaving as @{const par_step}, but over annotated outlines,
  so a reachable configuration still carries each thread's current @{const pre}.\<close>

inductive ann_step ::
  "('act,'s) ann \<times> 's \<Rightarrow> ('act,'s) ann \<times> 's \<Rightarrow> bool"
where
  ABasic:  "astep a s s' \<Longrightarrow> ann_step (ABasic P a Q, s) (ASkip Q, s')"
| AComp1:  "ann_step (c1, s) (c1', s') \<Longrightarrow> ann_step (AComp c1 c2, s) (AComp c1' c2, s')"
| AComp2:  "ann_step (AComp (ASkip P) c2, s) (c2, s)"
| ACondT:  "s \<in> b \<Longrightarrow> ann_step (ACond P b c1 c2, s) (c1, s)"
| ACondF:  "s \<notin> b \<Longrightarrow> ann_step (ACond P b c1 c2, s) (c2, s)"
| AWhileT: "s \<in> b \<Longrightarrow> ann_step (AWhile P b c, s) (AComp c (AWhile P b c), s)"
| AWhileF: "s \<notin> b \<Longrightarrow> ann_step (AWhile P b c, s) (ASkip (P \<inter> - b), s)"

inductive ann_par_step ::
  "(('act,'s) ann list \<times> 's) \<Rightarrow> (('act,'s) ann list \<times> 's) \<Rightarrow> bool"
where
  AnnPar: "\<lbrakk> i < length acs; ann_step (acs ! i, s) (c', s') \<rbrakk>
             \<Longrightarrow> ann_par_step (acs, s) (acs[i := c'], s')"

abbreviation ann_par_steps ::
  "(('act,'s) ann list \<times> 's) \<Rightarrow> (('act,'s) ann list \<times> 's) \<Rightarrow> bool"
  where "ann_par_steps \<equiv> ann_par_step\<^sup>*\<^sup>*"

text \<open>The shape of @{text acs}, the first component of a configuration above:
  a list of annotated outlines, ONE PER THREAD, of type @{typ "('act,'s) ann
  list"}. Position in the list IS thread identity, matching the convention of
  the @{text Ts} vector consumed by @{const og_parallel} / @{const
  interference_free} above -- @{text "acs ! i"} is thread @{text i}'s CURRENT
  outline node at that configuration. @{const ann_par_step} only ever
  rewrites the stepped thread's own slot (@{text "acs[i := c']"}), so @{text
  "length acs"} is invariant across a run and every other thread's node is
  left untouched by a step that is not theirs; that is precisely what lets a
  configuration reached after other threads have moved still answer, for any
  fixed @{text i}, "what does thread @{text i} still need to hold" via
  @{text "pre (acs ! i)"}.\<close>


subsection \<open>Preservation lemmas for the safety induction\<close>

text \<open>Local correctness is preserved by a sequential step, and the step
  re-establishes the successor's precondition.\<close>
lemma ann_step_loc_correct:
  assumes "ann_step (c, s) (c', s')" and "loc_correct c Q" and "s \<in> pre c"
  shows "loc_correct c' Q \<and> s' \<in> pre c'"
  using assms
proof (induction c arbitrary: Q s c' s')
  case (ABasic P a Pst)
  from ABasic.prems(1) have c': "c' = ASkip Pst" and st: "astep a s s'"
    by (auto elim: ann_step.cases)
  from ABasic.prems(2) have bc: "\<And>x y. x \<in> P \<Longrightarrow> astep a x y \<Longrightarrow> y \<in> Pst"
    and sub: "Pst \<subseteq> Q" by (auto elim: loc_correct.cases)
  from bc[OF _ st] ABasic.prems(3) have "s' \<in> Pst" by simp
  thus ?case unfolding c' using sub by (auto intro: loc_correct.Skip)
next
  case (ASkip P)
  from ASkip.prems(1) show ?case by (auto elim: ann_step.cases)
next
  case (AComp c1 c2)
  from AComp.prems(2) have lc1: "loc_correct c1 (pre c2)" and lc2: "loc_correct c2 Q"
    by (auto elim: loc_correct.cases)
  from AComp.prems(1) consider
      (step1) c1'' where "ann_step (c1, s) (c1'', s')" "c' = AComp c1'' c2"
    | (step2) P where "c1 = ASkip P" "c' = c2" "s' = s"
    by (auto elim: ann_step.cases)
  thus ?case
  proof cases
    case (step1 c1'')
    from AComp.IH(1)[OF step1(1) lc1] AComp.prems(3)
    have "loc_correct c1'' (pre c2)" "s' \<in> pre c1''" by simp_all
    thus ?thesis using step1(2) lc2 by (auto intro: loc_correct.Comp)
  next
    case (step2 P)
    from lc1 step2(1) have "P \<subseteq> pre c2" by (auto elim: loc_correct.cases)
    thus ?thesis using step2 lc2 AComp.prems(3) by auto
  qed
next
  case (ACond P b c1 c2)
  from ACond.prems(2) have h: "P \<inter> b \<subseteq> pre c1" "P \<inter> (- b) \<subseteq> pre c2"
      "loc_correct c1 Q" "loc_correct c2 Q" by (auto elim: loc_correct.cases)
  from ACond.prems(1) consider
      (t) "s \<in> b" "c' = c1" "s' = s" | (f) "s \<notin> b" "c' = c2" "s' = s"
    by (auto elim: ann_step.cases)
  thus ?case using h ACond.prems(3) by cases auto
next
  case (AWhile P b c)
  from AWhile.prems(2) have h: "P \<inter> b \<subseteq> pre c" "P \<inter> (- b) \<subseteq> Q" "loc_correct c P"
    by (auto elim: loc_correct.cases)
  from AWhile.prems(1) consider
      (t) "s \<in> b" "c' = AComp c (AWhile P b c)" "s' = s"
    | (f) "s \<notin> b" "c' = ASkip (P \<inter> - b)" "s' = s"
    by (auto elim: ann_step.cases)
  thus ?case
  proof cases
    case t
    have "loc_correct (AComp c (AWhile P b c)) Q"
      using h(3) AWhile.prems(2) by (auto intro: loc_correct.Comp)
    thus ?thesis using t h(1) AWhile.prems(3) by auto
  next
    case f
    thus ?thesis using h(2) AWhile.prems(3) by (auto intro: loc_correct.Skip)
  qed
qed

text \<open>Stepping never invents assertions or atomics.\<close>
lemma ann_step_assertions: "ann_step (c, s) (c', s') \<Longrightarrow> assertions c' \<subseteq> assertions c"
  by (induction "(c,s)" "(c',s')" arbitrary: c s c' s' rule: ann_step.induct) auto

lemma ann_step_atomics: "ann_step (c, s) (c', s') \<Longrightarrow> atomics c' \<subseteq> atomics c"
  by (induction "(c,s)" "(c',s')" arbitrary: c s c' s' rule: ann_step.induct) auto

text \<open>A sequential step either leaves the state unchanged (a control step) or
  fires exactly the head's leftmost atom -- whose local precondition is the
  current @{const pre}.\<close>
lemma ann_step_fire:
  assumes "ann_step (c, s) (c', s')"
  shows "s = s' \<or> (\<exists>a. astep a s s' \<and> (pre c, a) \<in> atomics c)"
  using assms
proof (induction "(c,s)" "(c',s')" arbitrary: c s c' s' rule: ann_step.induct)
  case (ABasic a s s' P Q) thus ?case by auto
next
  case (AComp1 c1 s c1' s' c2) thus ?case by auto
next
  case AComp2 thus ?case by auto
next
  case ACondT thus ?case by auto
next
  case ACondF thus ?case by auto
next
  case AWhileT thus ?case by auto
next
  case AWhileF thus ?case by auto
qed


subsection \<open>The safety invariant\<close>

text \<open>Every thread's residual is locally correct w.r.t. its post, its current
  precondition holds, and its assertions/atomics are bounded by the original
  outline's (so interference freedom keeps applying).\<close>
definition og_inv ::
  "(('act,'s) ann \<times> 's set) list \<Rightarrow> ('act,'s) ann list \<Rightarrow> 's \<Rightarrow> bool" where
  "og_inv Ts acs s \<longleftrightarrow>
     length acs = length Ts
   \<and> (\<forall>i < length Ts. s \<in> pre (acs ! i))
   \<and> (\<forall>i < length Ts. loc_correct (acs ! i) (snd (Ts ! i)))
   \<and> (\<forall>i < length Ts. assertions (acs ! i) \<subseteq> assertions (fst (Ts ! i)))
   \<and> (\<forall>i < length Ts. atomics (acs ! i) \<subseteq> atomics (fst (Ts ! i)))"

lemma og_inv_init:
  assumes "og_parallel Ts" and "s \<in> og_pre Ts"
  shows "og_inv Ts (map fst Ts) s"
  using assms by (auto simp: og_inv_def og_parallel_def og_pre_def)

lemma og_inv_step:
  assumes "interference_free Ts"
      and "og_inv Ts acs s"
      and "ann_par_step (acs, s) (acs', s')"
  shows "og_inv Ts acs' s'"
proof -
  from assms(3) obtain i c'
    where i: "i < length acs" and st: "ann_step (acs ! i, s) (c', s')"
      and acs': "acs' = acs[i := c']"
    by (auto elim: ann_par_step.cases)
  from assms(2) have len: "length acs = length Ts"
    and preI: "\<And>k. k < length Ts \<Longrightarrow> s \<in> pre (acs ! k)"
    and lcI: "\<And>k. k < length Ts \<Longrightarrow> loc_correct (acs ! k) (snd (Ts ! k))"
    and asI: "\<And>k. k < length Ts \<Longrightarrow> assertions (acs ! k) \<subseteq> assertions (fst (Ts ! k))"
    and atI: "\<And>k. k < length Ts \<Longrightarrow> atomics (acs ! k) \<subseteq> atomics (fst (Ts ! k))"
    by (auto simp: og_inv_def)
  from i len have iT: "i < length Ts" by simp
  from ann_step_loc_correct[OF st lcI[OF iT] preI[OF iT]]
    have lc_i: "loc_correct c' (snd (Ts ! i))" and pre_i: "s' \<in> pre c'" by simp_all
  have as_i: "assertions c' \<subseteq> assertions (fst (Ts ! i))"
    using ann_step_assertions[OF st] asI[OF iT] by blast
  have at_i: "atomics c' \<subseteq> atomics (fst (Ts ! i))"
    using ann_step_atomics[OF st] atI[OF iT] by blast
  have pre_foreign: "s' \<in> pre (acs ! k)" if k: "k < length Ts" and ki: "k \<noteq> i" for k
  proof (cases "s = s'")
    case True thus ?thesis using preI[OF k] by simp
  next
    case False
    from ann_step_fire[OF st] False obtain a
      where astp: "astep a s s'" and mem: "(pre (acs ! i), a) \<in> atomics (acs ! i)" by blast
    from mem atI[OF iT] have mem': "(pre (acs ! i), a) \<in> atomics (fst (Ts ! i))" by blast
    have rmem: "pre (acs ! k) \<in> insert (snd (Ts ! k)) (assertions (fst (Ts ! k)))"
      using asI[OF k] pre_in_assertions[of "acs ! k"] by blast
    from \<open>interference_free Ts\<close> iT k ki
    have "\<forall>r \<in> insert (snd (Ts!k)) (assertions (fst (Ts!k))).
            \<forall>pa \<in> atomics (fst (Ts!i)). if_pair r pa"
      by (auto simp: interference_free_def)
    with rmem mem' have "if_pair (pre (acs ! k)) (pre (acs ! i), a)" by blast
    thus ?thesis using astp preI[OF k] preI[OF iT] by (auto simp: if_pair_def)
  qed
  show ?thesis unfolding og_inv_def
  proof (intro conjI allI impI)
    show "length acs' = length Ts" using acs' len by simp
  next
    fix k assume k: "k < length Ts"
    show "s' \<in> pre (acs' ! k)"
      using acs' i len k pre_i pre_foreign[OF k] by (cases "k = i") (simp_all add: acs')
  next
    fix k assume k: "k < length Ts"
    show "loc_correct (acs' ! k) (snd (Ts ! k))"
      using acs' i len k lc_i lcI[OF k] by (cases "k = i") (simp_all add: acs')
  next
    fix k assume k: "k < length Ts"
    show "assertions (acs' ! k) \<subseteq> assertions (fst (Ts ! k))"
      using acs' i len k as_i asI[OF k] by (cases "k = i") (simp_all add: acs')
  next
    fix k assume k: "k < length Ts"
    show "atomics (acs' ! k) \<subseteq> atomics (fst (Ts ! k))"
      using acs' i len k at_i atI[OF k] by (cases "k = i") (simp_all add: acs')
  qed
qed

lemma og_inv_steps:
  assumes "interference_free Ts"
      and "og_inv Ts acs s"
      and "ann_par_steps (acs, s) (acs', s')"
  shows "og_inv Ts acs' s'"
proof -
  have "og_inv Ts (fst p) (snd p)" if "ann_par_steps (acs, s) p" for p
    using that
  proof (induction rule: rtranclp_induct)
    case base thus ?case using assms(2) by simp
  next
    case (step y z)
    have "ann_par_step (fst y, snd y) (fst z, snd z)" using step.hyps(2) by simp
    from og_inv_step[OF assms(1) step.IH this] show ?case .
  qed
  from this[of "(acs', s')"] assms(3) show ?thesis by simp
qed


section \<open>Soundness\<close>

subsection \<open>Safety: the assertion network is an inductive invariant\<close>

text \<open>The reusable result Ownership/UAF consumes: from a state in the
  precondition, every reachable configuration satisfies every thread's current
  precondition.  This is the formal counterpart of "the logic gets stuck before
  witnessing the UAF".\<close>

theorem og_safety:
  assumes "og_parallel Ts"
      and "s \<in> og_pre Ts"
      and "ann_par_steps (map fst Ts, s) (acs, s')"
  shows "\<forall>i < length acs. s' \<in> pre (acs ! i)"
proof -
  have "interference_free Ts" using assms(1) by (simp add: og_parallel_def)
  moreover have "og_inv Ts (map fst Ts) s"
    using og_inv_init[OF assms(1,2)] .
  ultimately have "og_inv Ts acs s'"
    using og_inv_steps assms(3) by blast
  thus ?thesis by (auto simp: og_inv_def)
qed

subsection \<open>Strip simulation (annotated semantics refines the bare one)\<close>

text \<open>Any bare sequential step is matched by an annotated step with the same
  underlying command -- so a terminated bare run lifts to a terminated annotated
  run, letting @{thm og_safety} deliver the postcondition.\<close>
lemma strip_eq_Skip: "strip c = Skip \<Longrightarrow> \<exists>P. c = ASkip P"
  by (cases c) auto

lemma seq_step_sim:
  assumes "seq_step (strip c, s) (d, s')"
  shows "\<exists>c'. ann_step (c, s) (c', s') \<and> strip c' = d"
  using assms
proof (induction c arbitrary: s d s')
  case (ABasic P a Q)
  from ABasic.prems have "d = Skip" "astep a s s'"
    by (auto elim: seq_step.cases)
  thus ?case by (auto intro: ann_step.ABasic)
next
  case (ASkip P)
  from ASkip.prems show ?case by (auto elim: seq_step.cases)
next
  case (AComp c1 c2)
  from AComp.prems consider
      (s1) e1' where "seq_step (strip c1, s) (e1', s')" "d = Seq e1' (strip c2)"
    | (s2) "strip c1 = Skip" "d = strip c2" "s' = s"
    by (auto elim: seq_step.cases)
  thus ?case
  proof cases
    case (s1 e1')
    from AComp.IH(1)[OF s1(1)] obtain c1'
      where "ann_step (c1, s) (c1', s')" "strip c1' = e1'" by blast
    thus ?thesis using s1(2) by (auto intro: ann_step.AComp1)
  next
    case s2
    then obtain P where "c1 = ASkip P" using strip_eq_Skip by blast
    thus ?thesis using s2 by (auto intro: ann_step.AComp2)
  qed
next
  case (ACond P b c1 c2)
  from ACond.prems consider
      (t) "s \<in> b" "d = strip c1" "s' = s" | (f) "s \<notin> b" "d = strip c2" "s' = s"
    by (auto elim: seq_step.cases)
  thus ?case
  proof cases
    case t thus ?thesis by (auto intro: ann_step.ACondT)
  next
    case f thus ?thesis by (auto intro: ann_step.ACondF)
  qed
next
  case (AWhile P b c)
  from AWhile.prems consider
      (t) "s \<in> b" "d = Seq (strip c) (While b (strip c))" "s' = s"
    | (f) "s \<notin> b" "d = Skip" "s' = s"
    by (auto elim: seq_step.cases)
  thus ?case
  proof cases
    case t thus ?thesis by (auto intro: ann_step.AWhileT)
  next
    case f thus ?thesis by (auto intro: ann_step.AWhileF)
  qed
qed

lemma par_step_sim:
  assumes "par_step (map strip acs, s) (ds, s')"
  shows "\<exists>acs'. ann_par_step (acs, s) (acs', s') \<and> map strip acs' = ds"
proof -
  from assms obtain i c'
    where i: "i < length (map strip acs)"
      and st: "seq_step ((map strip acs) ! i, s) (c', s')"
      and ds: "ds = (map strip acs)[i := c']"
    by (auto elim: par_step.cases)
  from i have i': "i < length acs" by simp
  with st have "seq_step (strip (acs ! i), s) (c', s')" by simp
  from seq_step_sim[OF this] obtain d'
    where sd: "ann_step (acs ! i, s) (d', s')" and strip_d: "strip d' = c'" by blast
  have "ann_par_step (acs, s) (acs[i := d'], s')"
    using i' sd by (auto intro: ann_par_step.AnnPar)
  moreover have "map strip (acs[i := d']) = ds"
    using ds strip_d by (simp add: map_update)
  ultimately show ?thesis by blast
qed

lemma par_steps_sim:
  assumes "par_steps (map strip acs, s) (ds, s')"
  shows "\<exists>acs'. ann_par_steps (acs, s) (acs', s') \<and> map strip acs' = ds"
proof -
  have "\<exists>acs'. ann_par_steps (acs, s) (acs', snd p) \<and> map strip acs' = fst p"
    if "par_steps (map strip acs, s) p" for p
    using that
  proof (induction rule: rtranclp_induct)
    case base
    have "ann_par_steps (acs, s) (acs, s)" by (rule rtranclp.rtrancl_refl)
    thus ?case by auto
  next
    case (step y z)
    from step.IH obtain acs_y
      where steps_y: "ann_par_steps (acs, s) (acs_y, snd y)"
        and my: "map strip acs_y = fst y" by blast
    have "par_step (map strip acs_y, snd y) (fst z, snd z)"
      using step.hyps(2) my by simp
    from par_step_sim[OF this] obtain acs_z
      where stp: "ann_par_step (acs_y, snd y) (acs_z, snd z)"
        and mz: "map strip acs_z = fst z" by blast
    from steps_y stp have "ann_par_steps (acs, s) (acs_z, snd z)"
      by (rule rtranclp.rtrancl_into_rtrancl)
    thus ?case using mz by blast
  qed
  from this[of "(ds, s')"] assms show ?thesis by simp
qed

subsection \<open>Partial correctness (corollary)\<close>

theorem og_sound:
  assumes "og_parallel Ts"
  shows "\<forall>s \<in> og_pre Ts. \<forall>s'.
           par_steps (map (strip \<circ> fst) Ts, s) (replicate (length Ts) Skip, s')
             \<longrightarrow> s' \<in> og_post Ts"
proof (intro ballI allI impI)
  fix s s'
  assume sp: "s \<in> og_pre Ts"
    and run: "par_steps (map (strip \<circ> fst) Ts, s) (replicate (length Ts) Skip, s')"
  have "par_steps (map strip (map fst Ts), s) (replicate (length Ts) Skip, s')"
    using run by simp
  from par_steps_sim[OF this] obtain acs'
    where steps: "ann_par_steps (map fst Ts, s) (acs', s')"
      and ms: "map strip acs' = replicate (length Ts) Skip" by blast
  from ms have lenacs: "length acs' = length Ts" by (metis length_map length_replicate)
  have "interference_free Ts" using assms by (simp add: og_parallel_def)
  moreover have "og_inv Ts (map fst Ts) s" using og_inv_init[OF assms sp] .
  ultimately have inv: "og_inv Ts acs' s'" using og_inv_steps steps by blast
  have "\<forall>i < length Ts. s' \<in> snd (Ts ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length Ts"
    from ms i lenacs have "strip (acs' ! i) = Skip"
      by (metis nth_map nth_replicate)
    then obtain Q where q: "acs' ! i = ASkip Q" using strip_eq_Skip by blast
    from inv i have lc: "loc_correct (acs' ! i) (snd (Ts ! i))"
      and pr: "s' \<in> pre (acs' ! i)" by (auto simp: og_inv_def)
    from lc q have "loc_correct (ASkip Q) (snd (Ts ! i))" by simp
    hence "Q \<subseteq> snd (Ts ! i)" by (auto elim: loc_correct.cases)
    moreover from pr q have "s' \<in> Q" by simp
    ultimately show "s' \<in> snd (Ts ! i)" by blast
  qed
  thus "s' \<in> og_post Ts" by (auto simp: og_post_def)
qed

end  \<comment> \<open>@{locale transition_system}\<close>

end
