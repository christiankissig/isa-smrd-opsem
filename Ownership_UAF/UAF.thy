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
