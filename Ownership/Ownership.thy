(*  Title:      Ownership/Ownership.thy
    Author:     RCU-C11-OpSem project (Track A, first AFP target)

    Ownership as a concrete IMPLEMENTATION of the generic Owicki-Gries
    framework (OwickiGries.thy).  An ownership predicate over an abstract
    transition system, a transfer discipline, the exclusivity invariant, the
    "ownership discharges interference-freedom" lemma, and a use-after-free
    safety corollary reproducing the paper's reasoning
    (rcu-c11-paper/example-uaf-bug-opsem.tex).

    Its ONLY dependency is the sibling OwickiGries entry (no Core/MemSem/
    EventStruct/OpSem/c11_opsem/SEFM).  Together they form the first AFP
    submission.  See docs/W1_owicki_gries_design.md, REWORK_PLAN.md (Decision 7,
    Phase 5, Risk 6).

    Status (2026-06-09): all proofs discharged; builds with no incomplete
    proofs and without quick_and_dirty.  Two skeleton fixes were needed during the proof
    phase: (1) owned_outline's type missed its postcondition argument
    ('s set); (2) ownership_interference_free conflated the OG thread index
    (nat) with the ownership process tag ('p) -- it now takes an explicit
    injective index-to-process map `proc` and the well-tagging discipline (the
    RCU client supplies these).
*)

theory Ownership
  imports "OwickiGries.OwickiGries"
begin

section \<open>The ownership-system locale\<close>

text \<open>Atomic actions are tagged with the acting process @{typ 'p}; resources
  have type @{typ 'r}.  The state @{typ 's} carries an ownership map
  @{term owns}.  Each (untagged) action declares an ownership footprint via
  @{term acquires} / @{term releases}.

  The transfer discipline (the three assumptions below) encodes the paper:
  threads instantly assume ownership of freshly allocated resources, gain
  ownership after reading the shared structure, and relinquish it at the
  rcu-exit / @{text free}.\<close>

locale ownership_system =
  transition_system astep
    for astep :: "('p \<times> 'act) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" +
  fixes owns     :: "'s \<Rightarrow> 'p \<Rightarrow> 'r set"
    and acquires :: "'act \<Rightarrow> 'r set"
    and releases :: "'act \<Rightarrow> 'r set"
  assumes
      \<comment> \<open>Locality: an action by @{text p} changes only @{text p}'s ownership.\<close>
      locality:    "\<lbrakk> astep (p, a) s s'; q \<noteq> p \<rbrakk> \<Longrightarrow> owns s' q = owns s q"
  and \<comment> \<open>Footprint: @{text p}'s ownership evolves exactly by its footprint.\<close>
      footprint:   "astep (p, a) s s' \<Longrightarrow> owns s' p = (owns s p \<union> acquires a) - releases a"
  and \<comment> \<open>Fresh acquisition: cannot acquire a resource currently owned by
        anyone (abstracts freezing/distinctness and the deref/free sequencing).\<close>
      fresh_acq:   "\<lbrakk> astep (p, a) s s'; r \<in> acquires a \<rbrakk> \<Longrightarrow> r \<notin> owns s q"
begin

section \<open>The ownership predicate (the paper's @{text "t \<in> own(s)"})\<close>

definition Owns :: "'p \<Rightarrow> 'r \<Rightarrow> 's set" where
  "Owns p r = {s. r \<in> owns s p}"

definition NotOwns :: "'p \<Rightarrow> 'r \<Rightarrow> 's set" where
  "NotOwns p r = {s. r \<notin> owns s p}"

lemma NotOwns_compl: "NotOwns p r = - Owns p r"
  by (auto simp: Owns_def NotOwns_def)


section \<open>Exclusivity invariant\<close>

definition exclusive :: "'s \<Rightarrow> bool" where
  "exclusive s \<longleftrightarrow> (\<forall>p q r. r \<in> owns s p \<longrightarrow> r \<in> owns s q \<longrightarrow> p = q)"

lemma exclusive_step:
  assumes "exclusive s" and "astep (p, a) s s'"
  shows   "exclusive s'"
  unfolding exclusive_def
proof (intro allI impI)
  fix x y r assume rx: "r \<in> owns s' x" and ry: "r \<in> owns s' y"
  have key: "r' \<in> owns s z \<or> (z = p \<and> r' \<in> acquires a)" if "r' \<in> owns s' z" for r' z
  proof (cases "z = p")
    case True with that footprint[OF assms(2)] show ?thesis by auto
  next
    case False with that locality[OF assms(2)] show ?thesis by auto
  qed
  from key[OF rx] key[OF ry] assms(1) fresh_acq[OF assms(2)] show "x = y"
    by (auto simp: exclusive_def)
qed

lemma exclusive_reach:
  assumes "exclusive s"
      and "(\<lambda>s s'. \<exists>p a. astep (p, a) s s')\<^sup>*\<^sup>* s s'"
  shows   "exclusive s'"
  using assms(2,1)
proof (induction rule: rtranclp_induct)
  case base thus ?case by simp
next
  case (step y z)
  from step.prems step.IH have "exclusive y" by blast
  moreover from step.hyps(2) obtain p a where "astep (p, a) y z" by blast
  ultimately show ?case using exclusive_step by blast
qed


section \<open>Ownership discharges interference freedom\<close>

text \<open>The crux: a foreign action (@{text "q \<noteq> p"}) leaves @{text "owns s p"}
  untouched, so ownership assertions tagged to another thread are automatically
  stable -- no @{term astep}-specific reasoning needed.\<close>

lemma foreign_preserves_Owns:
  assumes "q \<noteq> p" and "astep (q, a) s s'" and "s \<in> Owns p r"
  shows   "s' \<in> Owns p r"
  using assms(1,3) locality[OF assms(2)] by (auto simp: Owns_def)

lemma foreign_preserves_NotOwns:
  assumes "q \<noteq> p" and "astep (q, a) s s'" and "s \<in> NotOwns p r"
  shows   "s' \<in> NotOwns p r"
  using assms(1,3) locality[OF assms(2)] by (auto simp: NotOwns_def)

text \<open>An assertion is @{emph \<open>owned by\<close>} @{text p} if it is stable under every
  action of every other process.  @{const Owns} and @{const NotOwns} of @{text
  p} qualify (above).\<close>

definition own_stable :: "'p \<Rightarrow> 's set \<Rightarrow> bool" where
  "own_stable p r \<longleftrightarrow>
     (\<forall>q a s s'. q \<noteq> p \<longrightarrow> astep (q, a) s s' \<longrightarrow> s \<in> r \<longrightarrow> s' \<in> r)"

lemma Owns_own_stable:    "own_stable p (Owns p r)"
  unfolding own_stable_def using foreign_preserves_Owns by blast

lemma NotOwns_own_stable: "own_stable p (NotOwns p r)"
  unfolding own_stable_def using foreign_preserves_NotOwns by blast

text \<open>If every assertion of thread @{text j}'s outline is owned by @{text j},
  then the Owicki-Gries interference-freedom obligation holds by construction.
  This is the reusable "ownership disjointness implies non-interference".\<close>

definition owned_outline ::
  "'p \<Rightarrow> ('p \<times> 'act, 's) ann \<Rightarrow> 's set \<Rightarrow> bool" where
  "owned_outline j c Q \<longleftrightarrow> (\<forall>r \<in> insert Q (assertions c). own_stable j r)"

text \<open>The OG layer indexes threads by @{typ nat}; the ownership layer tags
  actions by the acting process @{typ 'p}.  The bridge is an injective
  index-to-process map @{term proc} together with the well-tagging discipline
  that every atom in thread @{text i}'s outline carries process @{term "proc i"}.
  Then a foreign thread (@{text "i \<noteq> j"}) acts under @{term "proc i \<noteq> proc j"},
  which @{const own_stable} of @{term "proc j"} covers.  The RCU client supplies
  @{term proc} (its threads act under their own id) and satisfies these by
  construction.\<close>

lemma ownership_interference_free:
  fixes proc :: "nat \<Rightarrow> 'p"
  assumes own:    "\<And>i. i < length Ts \<Longrightarrow> owned_outline (proc i) (fst (Ts!i)) (snd (Ts!i))"
      and tagged: "\<And>i P q a. i < length Ts \<Longrightarrow> (P, (q, a)) \<in> atomics (fst (Ts!i)) \<Longrightarrow> q = proc i"
      and inj:    "\<And>i j. i < length Ts \<Longrightarrow> j < length Ts \<Longrightarrow> proc i = proc j \<Longrightarrow> i = j"
  shows   "interference_free Ts"
  unfolding interference_free_def
proof (intro allI impI ballI)
  fix i assume i: "i < length Ts"
  fix j assume j: "j < length Ts" and ij: "i \<noteq> j"
  fix r assume r: "r \<in> insert (snd (Ts ! j)) (assertions (fst (Ts ! j)))"
  fix pa assume pa: "pa \<in> atomics (fst (Ts ! i))"
  obtain P q a where pa_eq: "pa = (P, (q, a))" by (cases pa) auto
  with tagged i pa have q: "q = proc i" by auto
  have "proc i \<noteq> proc j" using inj i j ij by blast
  with q have qj: "q \<noteq> proc j" by simp
  from own[OF j] r have "own_stable (proc j) r" by (auto simp: owned_outline_def)
  thus "if_pair r pa" using qj pa_eq by (auto simp: if_pair_def own_stable_def)
qed


section \<open>Use-after-free safety (the paper's corollary)\<close>

text \<open>The paper's Hoare rules instantiate as follows (informally; the concrete
  RCU program is supplied by the client in Phase 6):

  \<^item> rcu-exit  @{text "{} t2: rcu[t2]:=\<^sup>rel 0 {t2 \<notin> own(s)}"} :
                @{text "s \<in> releases a"}, post @{term "NotOwns t2 s"};
  \<^item> free      @{text "{t1 \<in> own(s)} t1: free(s) {t1 \<notin> own(s)}"} :
                @{text "s \<in> releases a"}, with precondition @{term "NotOwns t2 s"}
                for the safe-to-free side condition;
  \<^item> deref     @{text "{t2 \<in> own(s)} t2: v:=*s {}"} :
                precondition @{term "Owns t2 s"}.

  The UAF would co-enable @{text "free(s)"} (so @{term "NotOwns t2 s"}) with a
  still-pending @{text "deref(s)"} (so @{term "Owns t2 s"}); by @{thm og_safety}
  both threads' current preconditions hold at every reachable configuration, so
  the racy configuration is contradictory -- the logic is stuck before
  witnessing the UAF.\<close>

theorem uaf_safe:
  fixes Ts :: "(('p \<times> 'act, 's) ann \<times> 's set) list"
  assumes og:    "og_parallel Ts"
      and start: "s0 \<in> og_pre Ts"
      and run:   "ann_par_steps (map fst Ts, s0) (acs, s')"
      and i1:    "i1 < length acs" and i2: "i2 < length acs" and "i1 \<noteq> i2"
      \<comment> \<open>thread @{text i1} is about to @{text "free(s)"}; thread @{text i2} is
         about to @{text "deref(s)"}, hence still owns @{text s}:\<close>
      and free_pre:  "pre (acs ! i1) \<subseteq> NotOwns t2 s"
      and deref_pre: "pre (acs ! i2) \<subseteq> Owns t2 s"
  shows "False"
proof -
  from og_safety[OF og start run] i1 i2
  have "s' \<in> pre (acs ! i1)" and "s' \<in> pre (acs ! i2)" by blast+
  with free_pre deref_pre have "s' \<in> NotOwns t2 s" and "s' \<in> Owns t2 s" by auto
  thus False by (simp add: NotOwns_compl)
qed

end  \<comment> \<open>@{locale ownership_system}\<close>

end
