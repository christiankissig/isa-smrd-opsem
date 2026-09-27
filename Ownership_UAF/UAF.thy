(*  Title:      Ownership/UAF.thy
    Author:     Christian Kissig

    The paper's use-after-free safety corollary of the generic Ownership library,
    kept out of the `Ownership` session so that entry stays a clean AFP
    submission independent of any one client's story.
*)

theory UAF
  imports "Ownership.Ownership"
begin

context ownership_system
begin

section \<open>Use-after-free safety (the paper's corollary)\<close>

text \<open>The paper's Hoare rules instantiate as follows (informally; the concrete
  RCU program is supplied by the RCU client):

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

text \<open>Three points worth making explicit about the shape of @{thm [source]
  uaf_safe} above, since all three are easy to misread:

  \<^item> The shape of @{term acs}: a list of annotated outlines, one per thread
  (@{term ann_par_step} preserves @{term "length acs"}; see the note at its
  definition in @{text "OwickiGries.thy"}), where position IS thread identity --
  @{term "acs ! i"} is thread @{text i}'s CURRENT outline node at the reached
  configuration @{text "(acs, s')"}. So @{text i1} and @{text i2} above are
  not arbitrary labels; they pick out two THREADS' respective current
  positions in that one shared configuration.

  \<^item> @{term astep} is an INPUT to this theorem, not fixed by this theory.
  @{locale ownership_system} inherits it unconstrained from @{locale
  transition_system} (see the note at the end of @{text "Ownership.thy"}), and
  it enters the statement above solely through the @{text run} hypothesis --
  an @{term ann_par_steps} run, which threads @{term astep} through only via
  @{term ann_step}'s @{text ABasic} rule. So @{thm [source] uaf_safe} holds
  for ANY stepping relation satisfying the locale's three ownership axioms;
  instantiating it against a concrete semantics (the Episodic @{text OpSem},
  for RCU) is deferred client work, not something this proof needs.

  \<^item> @{text i1} and @{text i2} range over positions in the SAME reached
  configuration @{text "(acs, s')"} of a SINGLE run -- not independent points
  in time. That, together with the previous point, is what stops the theorem
  from over-reaching to forbid a thread legitimately relinquishing
  ownership: once a thread's own outline advances past its ownership-bearing
  node, that shows up as a DIFFERENT later configuration (a different @{text
  acs}, per @{term ann_par_step}'s one-slot rewrite), where its @{text
  "pre (acs ! i)"} no longer entails @{term Owns}, and the exclusion simply
  does not apply there. It only bites when two DISTINCT threads' CURRENT
  nodes are simultaneously ownership-contradictory in one shared state --
  and interference-freedom (@{thm [source] foreign_preserves_Owns}, @{thm
  [source] foreign_preserves_NotOwns}) is what makes that a sound reading:
  nothing but @{text t2}'s own steps can change whether @{text t2} owns
  @{text s}, so if @{term "Owns t2 s"} is @{text t2}'s current precondition
  at @{text s'}, it genuinely still holds there, not just at some earlier
  instant.\<close>

end  \<comment> \<open>@{locale ownership_system}\<close>

end