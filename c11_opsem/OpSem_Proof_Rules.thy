theory OpSem_Proof_Rules
imports OpSem
begin

lemma allI_case: "\<lbrakk>
    \<And> y. x \<noteq> y
    \<Longrightarrow> P y\<rbrakk>
    \<Longrightarrow> \<lbrakk>P x\<rbrakk>
  \<Longrightarrow> \<forall> y. P y" by fastforce

lemma own_ModView:
  assumes "wfs \<sigma>"
      and "w \<in> writes \<sigma>"
    shows "modView \<sigma> w (var w) = w"
  using assms apply(unfold wfs_def)
  by blast

lemma ts_oride_same_var:
  assumes "wfs \<sigma>"
      and "x = var w"
      and "w \<in> visible_writes \<sigma> t (var w)"
    shows "ts_oride ((thrView \<sigma> t)(var w := w)) (modView \<sigma> w) x = w"
  apply(simp add: ts_oride_def) apply safe using assms
  apply (meson own_ModView subsetCE visible_writes_in_writes)
  using assms(2) apply blast
  using assms(2) by blast

lemma ts_oride_diff_var:
  assumes "wfs \<sigma>"
      and "x \<noteq> var w"
      and "w \<in> visible_writes \<sigma> t (var w)"
    shows "ts_oride ((thrView \<sigma> t)(var w := w')) (modView \<sigma> w) x = ts_oride (thrView \<sigma> t) (modView \<sigma> w) x"
  apply(simp add: ts_oride_def)
  using assms(2) by blast

lemma ts_oride_split:
  assumes "tst (m' x) \<le> tst (m x)\<Longrightarrow> P (m x)"
      and "tst (m x) \<le> tst (m' x) \<Longrightarrow> P (m' x)"
    shows "P (ts_oride m m' x)"
  apply(simp add: ts_oride_def)
  by (simp add: assms(1) assms(2))


lemma wfs_covered_preserved:
  assumes "covered \<sigma> \<subseteq> writes \<sigma>"
      and "step t a \<sigma> \<sigma>'"
    shows "covered \<sigma>' \<subseteq> writes \<sigma>'"
     apply (rule step_cases[OF assms(2)]) apply simp_all
  using assms(1) apply blast
  apply (simp add: assms(1) subset_insertI2)
  using assms(1) visible_writes_in_writes by fastforce

lemma wfs_preserved:
  assumes "wfs \<sigma>"
      and "step t a \<sigma> \<sigma>'"
    shows "wfs \<sigma>'"
  apply(unfold wfs_def)
  apply rule defer apply rule defer apply rule defer defer
    apply clarsimp defer
    apply clarsimp
     apply (rule step_cases[OF assms(2)]) apply simp_all
  using assms(1) wfs_def apply auto[1]
  apply(case_tac "var w = aa")
       apply(case_tac "(aa, b) = (x, ts')") apply simp
  apply simp
       apply(case_tac "b = ts'") apply simp using assms(1) wfs_def apply blast
   apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast  apply simp
  using assms(1) wfs_def apply blast
   apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast apply simp
  using assms(1) wfs_def apply blast
     apply(case_tac "var w = aa")
  apply(case_tac "releasing \<sigma> w")
      apply(case_tac "(aa, b) = (x, ts')")
        apply simp apply (metis assms(1) fun_upd_same ts_oride_def wfs_def)
       apply(case_tac "b = ts'") apply(case_tac "var w = x") apply simp
        apply simp apply(rule ts_oride_split) using assms(1) apply simp
          using assms(1) apply simp
          apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
               apply simp using assms(1) wfs_def apply blast
              apply(case_tac "(aa, b) = (x, ts')") apply simp
          apply simp apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
          apply(case_tac "b = ts'")apply simp using assms(1) wfs_def apply blast
         apply simp using assms(1) wfs_def apply blast
          apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
             apply simp using assms(1) wfs_def apply blast
          apply clarsimp apply (rule step_cases[OF assms(2)]) apply simp_all
          using assms(1) wfs_def apply blast
             apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
             apply simp using assms(1) wfs_def apply blast
             apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
            apply simp using assms(1) wfs_def apply blast
          apply (rule conjI)
           apply clarsimp  apply (rule step_cases[OF assms(2)]) apply simp_all
          using assms(1) assms(2) own_ModView step_def apply fastforce
            apply(case_tac "var w = x") apply(case_tac "(aa, b) = (x, ts')") apply(case_tac "var w = aa")
               apply simp  apply blast
          apply(case_tac "b = ts'")
              apply simp using own_ModView[OF assms(1)] apply auto[1]
             apply simp using own_ModView[OF assms(1)] apply auto[1]
          using visible_var apply fastforce
           apply(case_tac "var w = x") apply(case_tac "(aa, b) = (x, ts')") apply(case_tac "var w = aa")
              apply(case_tac "releasing \<sigma> w")
          using own_ModView[OF assms(1)] apply simp apply(rule ts_oride_split)
          apply simp apply simp
          using leD valid_fresh_ts_def visible_writes_in_writes apply fastforce
          apply simp apply(case_tac "releasing \<sigma> w") apply simp
          apply blast apply simp
          using own_ModView[OF assms(1)] apply auto[1]
          using visible_var apply force
          using wfs_covered_preserved assms(1) assms(2) wfs_def apply blast
          apply (rule step_cases[OF assms(2)])
            apply(case_tac "ta = t") apply(case_tac "syncing \<sigma> w b")
               apply simp apply(rule ts_oride_split)
          apply (metis assms(1) fun_upd_apply subsetCE visible_writes_in_writes wfs_def)
  using assms(1) wfs_def apply blast apply simp
     apply (metis assms(1) subsetCE visible_writes_in_writes wfs_def)
    apply simp using assms(1) wfs_def apply blast
            apply(case_tac "ta = t") apply simp
  using assms(1) wfs_def apply blast
  apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast
   apply simp using assms(1) wfs_def apply blast
  apply(case_tac "ta = t") apply simp apply(case_tac "releasing \<sigma> w") apply simp
  apply(case_tac "var w = x") apply simp
     apply (metis assms(1) fun_upd_same ts_oride_def wfs_def)
  apply simp apply(rule ts_oride_split)
  using assms(1) apply auto[1]
  using assms(1) wfs_def apply blast
  apply simp
  using assms(1) wfs_def apply blast
  apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast apply simp
  using assms(1) wfs_def by blast

lemma [simp]: "var(lastWr \<sigma> x) = x" by(simp add: lastWr_def)

lemma last_write_write_on [simp]: "wfs \<sigma>
\<Longrightarrow>  lastWr \<sigma> x \<in> writes_on \<sigma> x"
  apply(simp add: lastWr_def )
  apply(case_tac "Max (tst`(writes_on \<sigma> x)) \<in> tst`(writes_on \<sigma> x)")
  defer apply simp
  by (auto simp add: tst_def var_def writes_on_def)

lemma lastWr_visible:
    "wfs \<sigma>
    \<Longrightarrow> lastWr \<sigma> x \<in> visible_writes \<sigma> t x"
  by (metis (no_types, lifting) CollectI last_write_max last_write_write_on visible_writes_def wfs_def)

lemma lastWr_read_pres: "lastWr (read_trans t b w \<sigma>) x = lastWr \<sigma> x"
  by(simp add: lastWr_def)

lemma write_to_different_var [simp]: "wfs \<sigma>
\<Longrightarrow> var w \<noteq> x
\<Longrightarrow> lastWr (write_trans t b w v \<sigma> ts') x = lastWr \<sigma> x"
  by(simp add: lastWr_def)

lemma [simp]: "wfs \<sigma>
\<Longrightarrow> w = (lastWr \<sigma> x)
\<Longrightarrow> valid_fresh_ts \<sigma> w ts' \<Longrightarrow>
                    lastWr (write_trans t b w v \<sigma> ts') x = (x, ts')"
  apply (simp add: valid_fresh_ts_def)
  by (simp add: lastWr_def)

lemma [simp]: "wfs \<sigma>
\<Longrightarrow> w \<noteq> lastWr \<sigma> x
\<Longrightarrow> w \<in> writes_on \<sigma> x
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow> lastWr (write_trans t b w v \<sigma> ts') x = lastWr \<sigma> x"
  apply (subst lastWr_def) apply(case_tac "var w = x") apply simp_all defer
   apply (simp add: lastWr_def)
 apply (simp add: valid_fresh_ts_def)
  by (metis dual_order.order_iff_strict lastWr_def last_write_max last_write_write_on max.absorb2 prod.exhaust_sel sndI tst_def var_def writes_on_var)

lemma [simp]: " wfs \<sigma>
\<Longrightarrow> var w \<noteq> x
\<Longrightarrow> value (write_trans t b w v \<sigma> ts')(lastWr \<sigma> x) = value \<sigma> (lastWr \<sigma> x)"
 by(simp add: value_def)


lemma [simp]: "wfs \<sigma>
\<Longrightarrow> w = lastWr \<sigma> x
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow>lastWr (update_trans t w v' \<sigma> ts') x = (x, ts')"
  apply (subst lastWr_def) apply simp
  by (simp add: lastWr_def less_eq_rat_def max.absorb1 valid_fresh_ts_def)

lemma [simp]: "wfs \<sigma>
\<Longrightarrow> w \<noteq> lastWr \<sigma> x
\<Longrightarrow> w \<in> writes_on \<sigma> x
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow>
                    lastWr (update_trans t w v' \<sigma> ts') x = lastWr \<sigma> x"
  apply (subst lastWr_def) apply(case_tac "var w = x") apply simp_all
  by (metis lastWr_def last_write_max last_write_write_on less_eq_rat_def max_def prod.collapse snd_conv tst_def valid_fresh_ts_def var_def writes_on_var)

lemma modView_lte_last: "wfs \<sigma>
\<Longrightarrow> tst(modView \<sigma> w x) \<le> tst(lastWr \<sigma> x)"
  using last_write_max wfs_def by blast

lemma c_obs_intro:
  assumes "\<And> w. \<lbrakk>
    w \<in> writes \<sigma> ;
    var w = x ;
    tst(thrView \<sigma> t x) \<le> tst w;
    value \<sigma> w = u\<rbrakk>
  \<Longrightarrow> releasing \<sigma> w"
  and "\<And> w. \<lbrakk>
    w \<in> writes \<sigma> ;
    var w = x ; tst(thrView \<sigma> t x) \<le> tst w;
    value \<sigma> w = u\<rbrakk>
  \<Longrightarrow> modView \<sigma> w y = lastWr \<sigma> y"
  and "\<And> w. \<lbrakk>
    w \<in> writes \<sigma> ;
    var w = x ; tst(thrView \<sigma> t x) \<le> tst w;
    value \<sigma> w = u\<rbrakk>
  \<Longrightarrow> value \<sigma> (lastWr \<sigma> y) = v"
  shows "c_obs \<sigma> x u t y v"
  apply(simp add: c_obs_def d_obs_def)
  using assms apply(simp add: visible_writes_def)
  by (metis (mono_tags, lifting) CollectD prod.sel(2) tst_def writes_on_def)




lemma d_obs_lastWr_visible:
  "wfs \<sigma>
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> w \<in> visible_writes \<sigma> t x
  \<Longrightarrow> w = lastWr \<sigma> x"
  apply (simp add: tst_def d_obs_def d_obs_t_def lastWr_def var_def visible_writes_def, auto)
  by (metis dual_order.antisym lastWr_def last_write_max last_write_write_on prod.collapse tst_def var_def writes_on_var)



lemma d_obs_implies_p_obs:
  "wfs \<sigma>
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> [x \<approx>\<^sub>t u] \<sigma>"
  apply(simp add: d_obs_t_def d_obs_def p_obs_def) using lastWr_visible
  by (metis lastWr_def)


lemma d_obs_p_obs_agree: "wfs \<sigma>
\<Longrightarrow> [x =\<^sub>t u] \<sigma>
\<Longrightarrow> [x \<approx>\<^sub>t v] \<sigma>
\<Longrightarrow> u = v"
  apply(unfold p_obs_def d_obs_t_def d_obs_def visible_writes_def)apply clarsimp
  by (metis eq_snd_iff fst_conv lastWr_def last_write_max leD order.not_eq_order_implies_strict tst_def var_def writes_on_var)

lemma not_p_obs_implies_c_obs: "\<not> [x \<approx>\<^sub>t u] \<sigma>
\<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>"
  by(auto simp add: p_obs_def c_obs_def)



lemmas update_simps =
  valid_fresh_ts_def visible_writes_def
  update_trans_def update_thrView_def update_modView_def
  rev_app_def Let_def add_cv_def update_mods_def





(*********** Transition Inference Rules Follow ****************)

lemma d_obs_Wr_set :  \<comment> \<open>Rule: DV-set\<close>
  assumes "wfs \<sigma>"
      and "wr_val a = Some v"
      and "avar a = x"
      and "d_obs_t \<sigma> t x u"
      and "step t a \<sigma> \<sigma>'"
    shows "d_obs_t \<sigma>' t x v"
  apply(rule step_cases[OF assms(5)])
  using assms(2) apply simp
   apply(unfold d_obs_t_def d_obs_def) apply simp apply clarsimp
   apply(case_tac "xa = x")
    using assms(1) apply simp apply(drule d_obs_lastWr_visible[OF assms(1) assms(4)])
      apply simp using assms(2) apply simp apply(unfold value_def)
    using assms(3) visible_var apply(case_tac "x = aa") apply simp apply (simp add: lastWr_def)
    apply clarsimp apply(case_tac "xa = x")
    using assms(1) apply simp  using assms(3) apply auto[1]
    using assms(1) apply clarsimp apply(case_tac "xa = x") apply simp
      apply(drule d_obs_lastWr_visible[OF assms(1) assms(4)])
    using assms(2) apply simp apply(case_tac "releasing \<sigma> (lastWr \<sigma> x)")
      apply (simp add: ts_oride_def)using modView_lte_last[OF assms(1)]
      apply (simp add: valid_fresh_ts_def)
      apply (metis dual_order.antisym less_eq_rat_def less_irrefl order_trans)
    apply simp
    using assms(3) visible_var by force

corollary d_obs_WrX_set :
  "wfs \<sigma>
    \<Longrightarrow> [x =\<^sub>t u] \<sigma>
    \<Longrightarrow> \<sigma> [x := v]\<^sub>t \<sigma>'
    \<Longrightarrow> [x =\<^sub>t v] \<sigma>' "
  by (metis WrX_def avar.simps(2) d_obs_Wr_set wr_val.simps(1))

corollary d_obs_WrR_set :
  "wfs \<sigma>
    \<Longrightarrow> [x =\<^sub>t u] \<sigma>
    \<Longrightarrow> \<sigma> [x :=\<^sup>R v]\<^sub>t \<sigma>'
    \<Longrightarrow> [x =\<^sub>t v] \<sigma>' "
  by (metis WrR_def avar.simps(2) d_obs_Wr_set wr_val.simps(1))

corollary d_obs_RMW_set :
  "wfs \<sigma>
    \<Longrightarrow> [x =\<^sub>t u] \<sigma>
    \<Longrightarrow> \<sigma> RMW[x,w,v]\<^sub>t \<sigma>'
    \<Longrightarrow> [x =\<^sub>t v] \<sigma>' "
  using avar.simps(3) d_obs_Wr_set wr_val.simps(2) by blast

lemma d_obs_Rd_pres:
  assumes a1: "wfs \<sigma>"
      and a2: "isRd a"
      and a4: "d_obs_t \<sigma> t x u"
      and a5: "step t a \<sigma> \<sigma>'"
    shows "d_obs_t \<sigma>' t x u"
  apply(rule step_cases[OF a5])
    apply (case_tac "avar a = x") apply simp
   apply (unfold  d_obs_t_def d_obs_def)
     defer
  defer
  using a2 isRd.simps(2) apply blast
  using a2 isRd.simps(3) apply blast
  apply (unfold read_trans_def Let_def)
  apply (case_tac "b = False")
   apply (simp add: d_obs_def d_obs_lastWr_visible d_obs_t_def rev_app_def syncing_def update_thrView_def)
  using  a1 a4
   apply (smt d_obs_def d_obs_lastWr_visible d_obs_t_def fun_upd_triv lastWr_def prod.collapse prod.inject surrey_state.surjective surrey_state.update_convs(2) var_def)
  using a1 a4 apply (simp add: d_obs_def  d_obs_t_def  lastWr_def  rev_app_def ts_oride_def tst_def update_thrView_def value_def var_def wfs_def writes_on_def)
  apply clarsimp
  apply (metis a1 a4 d_obs_lastWr_visible fst_conv lastWr_def snd_conv tst_def var_def visible_var writes_on_def)
  using assms apply (simp add: d_obs_def  d_obs_t_def  lastWr_def  rev_app_def ts_oride_def tst_def update_thrView_def value_def var_def wfs_def writes_on_def)
  apply (intro conjI impI)
  apply (unfold visible_writes_def writes_on_def var_def, simp_all)
  apply (metis (no_types, lifting) a1 a4 d_obs_def d_obs_t_def dual_order.antisym modView_lte_last old.prod.inject prod.collapse tst_def)
  by auto

corollary d_obs_RdX_pres:
    "wfs \<sigma>
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow> x]\<^sub>t \<sigma>'
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>' "
  using RdX_def d_obs_Rd_pres by force

corollary d_obs_RdA_pres:
  "wfs \<sigma>
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>'
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>'"
  using RdA_def d_obs_Rd_pres by force

lemma [simp]: "var w \<noteq> x
\<Longrightarrow> lastWr (update_trans t w v' \<sigma> ts') x = lastWr \<sigma> x"
  by(simp add: lastWr_def)

lemma "d_obs_other": \<comment> \<open>Rule: DV-Other\<close>
  assumes "wfs \<sigma>"
      and "avar a \<noteq> x"
      and "d_obs_t \<sigma> t x u"
      and "step t a \<sigma> \<sigma>'"
    shows "d_obs_t \<sigma>' t x u"
  apply(rule step_cases[OF assms(4)])
  using assms(2, 3) apply simp
  apply (unfold  d_obs_t_def d_obs_def)
  apply (case_tac "b = False")
  apply (simp add: lastWr_def read_trans_def rev_app_def syncing_def update_thrView_def value_def)
     apply (unfold writes_on_def)
   apply (metis (no_types, lifting) Collect_cong assms(2) surrey_state.select_convs(1) surrey_state.surjective surrey_state.update_convs(2) visible_var)
   apply (unfold read_trans_def Let_def)
   apply (simp add: lastWr_def  rev_app_def ts_oride_def tst_def update_thrView_def value_def var_def  wfs_def writes_on_def)
   using assms(1,2,3)  apply (unfold tst_def d_obs_def d_obs_t_def wfs_def writes_on_def le_neq_trans modView_lte_last)
   apply clarsimp
   apply (metis (no_types, lifting) assms(1) dual_order.antisym fst_conv modView_lte_last prod.collapse snd_conv tst_def var_def visible_var)
   using assms (2, 3) apply simp
   apply (unfold d_obs_t_def d_obs_def)
    apply (intro conjI)
   using assms(2) apply (metis visible_var)
   using visible_var
    apply(case_tac "b = False")
     apply clarsimp
     apply(rule conjI)
   using assms(1)
      apply(unfold visible_writes_def)
      apply clarsimp
     apply simp
    apply simp
   using assms (2,3)
   apply simp
   apply (simp add: d_obs_t_def d_obs_def)
   apply clarsimp
   apply (rule conjI)
    apply (case_tac "aa = x")
     apply (simp add: var_def writes_on_def)
    apply simp
    apply (case_tac "releasing \<sigma> (aa, b)")
     apply(simp add: ts_oride_def tst_def var_def)
   apply (metis dual_order.antisym modView_lte_last prod.collapse tst_def)
     apply(simp add: ts_oride_def tst_def var_def)
    apply (case_tac "aa = x")
     apply (simp add: var_def writes_on_def)
   apply simp
   by(simp add: value_def tst_def)


corollary d_obs_RdX_other:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow> y]\<^sub>t \<sigma>'
  \<Longrightarrow>[x =\<^sub>t u] \<sigma>'"
  by (metis RdX_def avar.simps(1) d_obs_other)

corollary d_obs_RdA_other:
  "wfs \<sigma> \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>'
  \<Longrightarrow>[x =\<^sub>t u] \<sigma>'"
  by (metis RdA_def avar.simps(1) d_obs_other)

corollary d_obs_WrX_other:
  "wfs \<sigma> \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t \<sigma>'
  \<Longrightarrow>[x =\<^sub>t u] \<sigma>'"
  by (metis WrX_def avar.simps(2) d_obs_other)

corollary d_obs_WrR_other:
  "wfs \<sigma> \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>'
  \<Longrightarrow>[x =\<^sub>t u] \<sigma>'"
  by (metis WrR_def avar.simps(2) d_obs_other)

corollary d_obs_RMW_other:
  "wfs \<sigma> \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> RMW[y, v, v']\<^sub>t \<sigma>'
  \<Longrightarrow>[x =\<^sub>t u] \<sigma>'"
  using d_obs_other by force




lemma p_obs_Rd_intro: \<comment> \<open>Rule: OB-Intro\<close>
  assumes "wfs \<sigma>"
      and "isRd a"
  and "rd_val a = Some v"
  and "avar a = x"
  and "step t a \<sigma> \<sigma>'"
  shows "p_obs \<sigma>' t x v"
  using assms
  apply (simp add: p_obs_def step_def, auto)
  apply (cases a, auto)
   apply (simp add: read_trans_def rev_app_def)
  apply (unfold value_def rev_app_def valid_fresh_ts_def read_trans_def visible_writes_def wfs_def p_obs_def step_def, auto)
   apply (unfold writes_on_def tst_def update_thrView_def, safe)
  apply (case_tac "syncing \<sigma> (x, ba) x11", clarsimp)
  apply (metis (no_types, lifting) eq_refl fun_upd_same sndI ts_oride_def)
  apply clarsimp
  by auto[1]

corollary p_obs_RdX_intro:
  "wfs \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow> x]\<^sub>t \<sigma>'
  \<Longrightarrow> [x \<approx>\<^sub>t v] \<sigma>'"
  by (metis RdX_def avar.simps(1) isRd.simps(1) p_obs_Rd_intro rd_val.simps(1))

corollary p_obs_RdA_intro:
  "wfs \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>'
  \<Longrightarrow> [x \<approx>\<^sub>t v] \<sigma>'"
  by (metis RdA_def avar.simps(1) isRd.simps(1) p_obs_Rd_intro rd_val.simps(1))






lemma  [simp]: "var w \<noteq> y
\<Longrightarrow> lastWr (write_trans t b w u \<sigma> ts') y =  lastWr \<sigma> y"
  by(simp add: lastWr_def)

lemma [simp]:
  "var w' = var w
  \<Longrightarrow> tst w' = ts'
  \<Longrightarrow> releasing (update_trans t w v' \<sigma> ts') (var w', tst w')"
  by(simp add: releasing_def)

lemma [simp]:
  "var w' = var w
  \<Longrightarrow> tst w' = ts'
  \<Longrightarrow> releasing (write_trans t b w v' \<sigma> ts') (var w', tst w') = b"
  by(simp add: releasing_def)

lemma c_obs_Wr_intro:
  assumes "wfs \<sigma>"
  and "wr_val a = Some u"
  and "avar a = x"
  and "isRA a"
  and "isWr a"
  and "d_obs_t \<sigma> t y v"
  and "\<not> p_obs \<sigma> t' x u"
  and "x \<noteq> y"
  and "step t a \<sigma> \<sigma>'"
  and "t'\<noteq> t"
shows "c_obs \<sigma>' x u t' y v"
  apply(rule step_cases[OF assms(9)])
  using assms(2) apply auto[1] defer
  using assms(5) apply auto[1]
  using assms(2,3,4,5,6,7) apply clarsimp
  apply (case_tac "aa \<noteq> x")
  using visible_var apply fastforce
  apply clarsimp
  apply(simp add: d_obs_t_def d_obs_def p_obs_def c_obs_def)
  apply clarsimp
  apply (case_tac "aa \<noteq> x")
  using visible_var apply fastforce
  apply (case_tac "bb = ts'") defer
   apply(case_tac "value (write_trans t True (x, b) u \<sigma> ts')(x, bb) = value \<sigma> (x, bb)")
  apply (simp add: visible_writes_def)
  using assms(10) apply simp apply blast
   apply(simp add: value_def)
  apply simp
  apply(rule conjI)
   apply clarsimp
  using assms(8) apply clarsimp
  using assms apply (simp, auto)
  by(simp add: releasing_def)


corollary c_obs_WrR_intro:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> t' \<noteq> t
   \<Longrightarrow> [y =\<^sub>t v] \<sigma>
   \<Longrightarrow> \<not> [x \<approx>\<^sub>t' u] \<sigma>
   \<Longrightarrow> \<sigma> [x :=\<^sup>R u]\<^sub>t \<sigma>'
   \<Longrightarrow> [x = u]\<^sub>t'\<lparr>y = v\<rparr> \<sigma>'"
  by (metis WrR_def avar.simps(2) c_obs_Wr_intro isRA.simps(2) isWr.simps(2) wr_val.simps(1))



lemma c_obs_Up_intro:
  assumes as1: "wfs \<sigma>"
  and as2: "wr_val a = Some u"
  and as3: "avar a = x"
  and as4: "isUp a"
  and as5: "d_obs_t \<sigma> t y v"
  and as6: "\<not> p_obs \<sigma> t' x u"
  and as7: "x \<noteq> y"
  and as8: "step t a \<sigma> \<sigma>'"
  and as9: "t' \<noteq> t"
shows "c_obs \<sigma>' x u t' y v"
  apply(rule step_cases[OF assms(8)])
  using as2 apply auto[1]
  using as4 apply auto[1]
  using assms apply safe
proof -
  fix aa b xa va v' ts'
  assume a1: "wfs \<sigma>" and
         a2: "wr_val (Update xa (value \<sigma> (aa, b)) v') = Some u" and
         a3: "isUp (Update xa (value \<sigma> (aa, b)) v')" and
         a4: "[y =\<^sub>t v] \<sigma>" and
         a5: "\<not> [avar (Update xa (value \<sigma> (aa, b)) v') \<approx>\<^sub>t' u] \<sigma> " and
         a6: "avar (Update xa (value \<sigma> (aa, b)) v') \<noteq> y" and
         a7: "\<sigma> RMW[xa, value \<sigma> (aa, b), v']\<^sub>t (update_trans t (aa, b) v' \<sigma> ts')" and
         a8: "t' \<noteq> t" and
         a9: "x = avar (Update xa (value \<sigma> (aa, b)) v')" and
         a10: "\<sigma>' = update_trans t (aa, b) v' \<sigma> ts'"  and
         a11: "a = Update xa (value \<sigma> (aa, b)) v'" and
         a12: "(aa, b) \<in> visible_writes \<sigma> t (avar (Update xa (value \<sigma> (aa, b)) v'))" and
         a13: "(aa, b) \<notin> covered \<sigma>" and
         a14: "valid_fresh_ts \<sigma> (aa, b) ts'"
  show g: "[avar (Update xa (value \<sigma> (aa, b)) v') = u]\<^sub>t'\<lparr>y = v \<rparr> (update_trans t (aa, b) v' \<sigma> ts')"
    using a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 apply (simp add: update_simps step_def d_obs_def p_obs_def d_obs_t_def c_obs_def)
    apply (case_tac "releasing \<sigma> (aa, b)", safe)
    apply (simp add: tst_def releasing_def)
    apply ((metis fst_conv var_def writes_on_var)+) [9]
    using as8 dual_order.antisym fun_upd_other
    apply (smt as3 as5 d_obs_def d_obs_other d_obs_t_def fun_upd_eqD fun_upd_triv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5))
    apply auto[1]
    using as3 as5 as8 d_obs_def d_obs_other d_obs_t_def apply blast
    using as3 as5 as8 d_obs_def d_obs_other d_obs_t_def apply blast
    apply auto[1]
    apply(simp add: releasing_def)
    apply (smt Pair_inject fun_upd_other fun_upd_same surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) write_record.select_convs(2))
    apply (simp add:tst_def var_def wfs_def wfs_preserved writes_on_def)
    apply clarify
    using as8 fst_conv mem_Collect_eq fun_upd_same not_less_iff_gr_or_eq snd_conv
    apply (smt surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5))
    apply (metis fst_conv var_def writes_on_var)
    apply (metis fst_conv var_def writes_on_var)
    apply (metis fst_conv var_def writes_on_var)
                        apply (simp add: tst_def releasing_def) apply auto[1]
    apply (smt Pair_inject fun_upd_other insert_iff mem_Collect_eq surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(4) surrey_state.update_convs(5) value_def writes_on_def)
    using fst_conv insert_iff fun_upd_apply less_imp_not_less not_less_iff_gr_or_eq
    apply (smt fun_upd_same surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5))
    apply (case_tac "releasing \<sigma> (aa, b)", auto)[1]
    using as3 as5 as8 d_obs_def d_obs_other d_obs_t_def apply blast
    using as3 as5 as8 d_obs_def d_obs_other d_obs_t_def apply blast
    apply (case_tac "releasing \<sigma> (aa, b)", auto)[1]
    apply (simp add: tst_def releasing_def value_def) apply auto[1]
    apply (metis fst_conv var_def writes_on_var)
    apply (unfold writes_on_def var_def) [1]
    apply clarsimp apply auto[1]
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp apply blast
    apply ((metis fst_conv var_def writes_on_var)+)[9]
    apply (case_tac "releasing \<sigma> (aa, b)", auto)[1]
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    using not_less_iff_gr_or_eq apply blast
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    apply (smt as5 as8 assms(3) d_obs_def d_obs_other d_obs_t_def fun_upd_same fun_upd_triv fun_upd_twist surrey_state.select_convs(2) surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5))
    apply auto[1]
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    using not_less_iff_gr_or_eq apply blast
    using as3 as5 as8 d_obs_def d_obs_other d_obs_t_def apply blast
    apply auto[1]
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    apply blast
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    apply blast
    apply (metis fst_conv var_def writes_on_var)
    apply (metis fst_conv var_def writes_on_var)
    apply (metis fst_conv var_def writes_on_var)
    apply auto[1]
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
       apply safe[1]
    apply (simp add: tst_def a11 a12 a13)
        apply(simp add: lastWr_def )apply(unfold writes_on_def)apply simp
    apply (smt Collect_cong Pair_inject fst_conv fun_upd_other fun_upd_same surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) var_def)
    apply (simp add: tst_def a11 a12 a13)
        apply(simp add: lastWr_def )apply(unfold writes_on_def)apply simp
    apply (smt leD less_irrefl tst_def)
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    apply (smt Pair_inject fun_upd_same surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5))
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    apply blast
    apply (unfold writes_on_def var_def releasing_def value_def) [1]
    apply clarsimp
    by blast
qed


corollary c_obs_RMW_intro:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> t' \<noteq> t
   \<Longrightarrow> [y =\<^sub>t v] \<sigma>
   \<Longrightarrow> \<not> [x \<approx>\<^sub>t' u] \<sigma>
   \<Longrightarrow> \<sigma> RMW[x, w, u]\<^sub>t \<sigma>'
   \<Longrightarrow> [x = u]\<^sub>t'\<lparr>y = v\<rparr> \<sigma>'"
  using avar.simps(3) c_obs_Up_intro isUp.simps(3) wr_val.simps(2) by blast




lemma c_obs_Rd_d_obs:  \<comment> \<open>Transfer\<close>
  assumes "wfs \<sigma>"
  and "isRd a"
  and "isRA a"
  and "rd_val a = Some u"
  and "avar a = x"
  and "c_obs \<sigma> x u t y v"
  and "step t a \<sigma> \<sigma>'"
shows "d_obs_t \<sigma>' t y v"
  apply(rule step_cases[OF assms(7)])
    defer
  using assms(2) apply simp
  using assms(2) apply simp
  using assms(6) apply clarsimp
  using assms(6) apply clarsimp
  apply(case_tac "aa \<noteq> x")
  using assms(5) visible_var apply fastforce
  apply clarsimp
  apply (case_tac "\<not> syncing \<sigma> (x,b) True")
   apply (metis assms(4) c_obs_def option.sel prod.sel(1) rd_val.simps(1) syncing_def var_def visible_var)
  apply clarsimp
  using assms(3, 4, 5) apply clarsimp
  apply (simp add: c_obs_def d_obs_t_def d_obs_def)
  apply (rule conjI)
  using assms(1)
   apply(unfold  ts_oride_def visible_writes_def wfs_def)
  apply (simp add: lastWr_def var_def)
  apply(unfold lastWr_def read_trans_def rev_app_def update_thrView_def value_def writes_on_def)
  by auto

corollary c_obs_RdA_d_obs:
  "wfs \<sigma>
  \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>
  \<Longrightarrow> \<sigma> [u \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>'
  \<Longrightarrow> [y =\<^sub>t v] \<sigma>'"
  by (metis RdA_def avar.simps(1) c_obs_Rd_d_obs isRA.simps(1) isRd.simps(1) rd_val.simps(1))



lemma c_obs_Up_d_obs:
  assumes "wfs \<sigma>"
  and "isUp a"
  and "rd_val a = Some u"
  and "avar a = x"
  and "c_obs \<sigma> x u t y v"
  and "step t a \<sigma> \<sigma>'"
  and "x \<noteq> y"
shows "d_obs_t \<sigma>' t y v"
  apply(rule step_cases[OF assms(6)])
  using assms(2) isUp.simps(1) apply blast
  using assms(3) apply auto[1]
  using assms(2,3,4,5,7)
  apply clarsimp
  apply(case_tac "aa \<noteq> x")
   apply(simp add: visible_writes_def)
   apply(unfold writes_on_def)
   apply(elim conjE)
   apply simp
  apply clarsimp
  apply(simp add: c_obs_def d_obs_t_def d_obs_def)
  apply(intro conjI)
   apply(simp add: ts_oride_def)
   apply(intro conjI impI)
  using assms(1) last_write_max wfs_def apply blast
    apply (simp add: valid_fresh_ts_def)
  apply(simp add: lastWr_def)
  apply(unfold writes_on_def, simp, elim conjE)
  by(simp add: value_def)

corollary c_obs_UpRA_d_obs:
  "wfs \<sigma>
  \<Longrightarrow> x\<noteq>y
  \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>
  \<Longrightarrow> \<sigma> RMW[x, u, z]\<^sub>t \<sigma>'
  \<Longrightarrow> [y =\<^sub>t v] \<sigma>'"
  using avar.simps(3) c_obs_Up_d_obs isUp.simps(3) rd_val.simps(2) by blast






lemma [simp]: "z \<noteq> x
\<Longrightarrow>  visible_writes (write_trans t b (z, ts) v \<sigma> ts') t x = visible_writes \<sigma> t x"
  by(simp add: visible_writes_def)

lemma [simp]: "var w \<noteq> z
\<Longrightarrow>value (write_trans t ba (z, b) va \<sigma> ts') w =  value \<sigma> w"
  by(simp add: value_def)

lemma [simp]: "var w \<noteq> z
\<Longrightarrow> releasing (write_trans t ba (z, b) va \<sigma> ts') w = releasing \<sigma> w "
  by(simp add: releasing_def)

lemma [simp]: "var w \<noteq> z
\<Longrightarrow> z \<noteq> y
\<Longrightarrow> d_obs(write_trans t ba (z, b) va \<sigma> ts')(modView \<sigma> w) y v = d_obs \<sigma> (modView \<sigma> w) y v"
  by(simp add: d_obs_def)

lemma c_obs_Rd_pres:
  assumes "wfs \<sigma>"
  and "isRd a"
  and "c_obs \<sigma> x u t y v"
  and "step t' a \<sigma> \<sigma>'"
  and "x \<noteq> y"
  and "\<not>isRA a"
  and "t \<noteq> t'"
shows "c_obs \<sigma>' x u t y v"
  apply(rule step_cases[OF assms(4)])
  defer
  using assms(2) apply auto[2]
  using assms(1,2,3,5,6,7)
  apply(elim conjE)
  apply(simp add: c_obs_def d_obs_def visible_writes_def)
  apply(unfold writes_on_def, clarsimp)
  apply(intro conjI)
    apply(simp add: read_trans_def rev_app_def Let_def update_modView_def update_thrView_def)
  apply (smt action.simps(10) assms(4) lastWr_read_pres step_def)
   apply (simp add: lastWr_read_pres)
  by(simp add: releasing_def)


corollary c_obs_RdX_pres:
  "wfs \<sigma>
  \<Longrightarrow>  x \<noteq> y
  \<Longrightarrow> t \<noteq> t'
         \<Longrightarrow> [x=u]\<^sub>t\<lparr>y=v\<rparr> \<sigma>
         \<Longrightarrow> \<sigma> [k \<leftarrow> z]\<^sub>t' \<sigma>'
         \<Longrightarrow> [x=u]\<^sub>t\<lparr>y=v\<rparr> \<sigma>'"
  by (metis (full_types) RdX_def c_obs_Rd_pres isRA.simps(1) isRd.simps(1))




lemma c_obs_Wr_pres:
  assumes "wfs \<sigma>"
  and "avar a = z"
  and "isWr a"
  and "z \<noteq> y"
  and "z \<noteq>x"
  and "x \<noteq> y"
  and "c_obs \<sigma> x u t y v"
  and "step t a \<sigma> \<sigma>'"
shows "c_obs \<sigma>' x u t y v"
  apply(rule step_cases[OF assms(8)])
  using assms(3) apply clarsimp defer
  using assms(3) apply clarsimp
  using assms(2,3,4,5,6,7) apply clarsimp
  apply (case_tac "aa \<noteq> z")
  using visible_var apply force
  apply clarsimp
  by (simp add: c_obs_def)

corollary c_obs_WrX_pres:
  "wfs \<sigma>
  \<Longrightarrow> z \<noteq> y
  \<Longrightarrow> z \<noteq> x
  \<Longrightarrow> x \<noteq> y
         \<Longrightarrow> [x=u]\<^sub>t\<lparr>y=v\<rparr> \<sigma>
         \<Longrightarrow> \<sigma> [z:= w]\<^sub>t \<sigma>'
         \<Longrightarrow> [x=u]\<^sub>t\<lparr>y=v\<rparr> \<sigma>'"
  by (metis WrX_def avar.simps(2) c_obs_Wr_pres isWr.simps(2))

corollary c_obs_WrR_pres:
  "wfs \<sigma> \<Longrightarrow> z \<noteq> y
  \<Longrightarrow> z \<noteq> x \<Longrightarrow> x \<noteq> y
         \<Longrightarrow> [x=u]\<^sub>t\<lparr>y=v\<rparr> \<sigma>
         \<Longrightarrow> \<sigma> [z:=\<^sup>R w]\<^sub>t \<sigma>'
         \<Longrightarrow> [x=u]\<^sub>t\<lparr>y=v\<rparr> \<sigma>'"
  by (metis WrR_def avar.simps(2) c_obs_Wr_pres isWr.simps(2))

lemma d_obs_c_obs: "wfs \<sigma>
\<Longrightarrow> [x =\<^sub>t u] \<sigma>
\<Longrightarrow> x \<noteq> y
\<Longrightarrow> u \<noteq> m
\<Longrightarrow> [x = m]\<^sub>t\<lparr>y = v\<rparr> \<sigma>"
  apply(simp add: d_obs_t_def d_obs_def c_obs_def)
  using d_obs_def d_obs_p_obs_agree d_obs_t_def p_obs_def by blast


lemma [simp]: "tst (x,b) < ts'
\<Longrightarrow> writes_on (write_trans t ba (x, b) va \<sigma> ts') x = (writes_on \<sigma> x) \<union> {(x,ts')}"
 by(simp add: visible_writes_def)

lemma visible_writes_write_trans [simp]: "wfs \<sigma>
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow> t \<noteq> t'
\<Longrightarrow> var w \<noteq> x
\<Longrightarrow> visible_writes \<sigma> t x = visible_writes (write_trans t' b w v \<sigma> ts') t x"
  apply(unfold visible_writes_def) by simp

lemma value_not_change_write_to_different_var [simp]:  "wfs \<sigma>
\<Longrightarrow> t \<noteq> t'  \<Longrightarrow> w \<in> visible_writes \<sigma> t x
\<Longrightarrow> valid_fresh_ts \<sigma> w' ts'
\<Longrightarrow>var w \<noteq> var w'
\<Longrightarrow> u = value \<sigma> w
\<Longrightarrow> u = value (write_trans t' b w' v \<sigma> ts') w"
  apply (unfold  write_trans_def rev_app_def value_def add_cv_def update_mods_def) apply simp
  apply (rule conjI)
  using visible_var apply fastforce
  by (simp add: update_modView_def update_thrView_def)

lemma "wfs \<sigma>
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow> t \<noteq> t' \<Longrightarrow> var w \<noteq> x \<Longrightarrow> p_obs \<sigma> t x u =  p_obs (write_trans t' b w v \<sigma> ts') t x u"
  apply (unfold  p_obs_def)
  apply (case_tac " visible_writes \<sigma> t x \<noteq> visible_writes (write_trans t' b w v \<sigma> ts') t x")
  apply simp
  using  value_not_change_write_to_different_var
  by (metis (full_types) visible_var)


lemma not_p_obs_Wr_pres :
  assumes a1: "wfs \<sigma>"
      and a2: "isWr a"
      and a3: "avar a \<noteq> x"
      and a4: "t \<noteq> t'"
      and a5: "\<not> p_obs \<sigma> t x u"
      and a6: "step t' a \<sigma> \<sigma>'"
    shows a7: "\<not> p_obs \<sigma>' t x u"
  apply(rule step_cases[OF a6])
  using a2 apply auto[1]
   defer
  using a2 apply auto[1]
  using assms
  apply simp
  apply(unfold p_obs_def)
  apply(case_tac "var w = x")
   apply simp
  using visible_var apply fastforce
  apply clarsimp
  apply (case_tac "var (aa, b) = x")
  using var_def apply auto[1]
  using visible_writes_write_trans apply simp
  using visible_var by fastforce

corollary not_p_obs_WrX_pres:
  "wfs \<sigma>
  \<Longrightarrow> y \<noteq> x
  \<Longrightarrow> t \<noteq> t'
    \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
    \<Longrightarrow> \<sigma> [y := v]\<^sub>t' \<sigma>'
    \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis WrX_def avar.simps(2) isWr.simps(2) not_p_obs_Wr_pres)

corollary not_p_obs_WrR_pres:
  "wfs \<sigma> \<Longrightarrow> y \<noteq> x
  \<Longrightarrow> t \<noteq> t'
    \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
    \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t' \<sigma>'
    \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis WrR_def avar.simps(2) isWr.simps(2) not_p_obs_Wr_pres)

lemma not_p_obs_Up_pres :
  assumes a1: "wfs \<sigma>"
      and a2: "isUp a"
      and a3: "avar a \<noteq> x"
      and a4: "t \<noteq> t'"
      and a5: "\<not> p_obs \<sigma> t x u"
      and a6: "step t' a \<sigma> \<sigma>'"
    shows "\<not> p_obs \<sigma>' t x u"
  apply(rule step_cases[OF a6])
  using a2 apply auto[2]
  apply (elim conjE)
proof -
  fix w xa v v' ts'
  assume p1: "\<sigma>' = update_trans t' w v' \<sigma> ts'" and
         p2: "a = Update xa v v'" and
         p3: "w \<in> visible_writes \<sigma> t' (avar a)" and
         p4: "v = value \<sigma> w" and
         p5: "w \<notin> covered \<sigma>" and
         p6: "valid_fresh_ts \<sigma> w ts'"
  show "\<not> (p_obs (update_trans t' w v' \<sigma> ts') t x u) "
    using p3 p4 p5 p6
  apply(simp add: p_obs_def)
    apply (simp add: Let_def update_trans_def step_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
    apply (case_tac "releasing \<sigma> w", auto)
     apply (simp add:visible_writes_def  valid_fresh_ts_def ts_oride_def, auto)
     apply(unfold writes_on_def  tst_def tst_def value_def var_def visible_var visible_writes_def writes_on_def)
     apply clarsimp
    apply (smt a3 a4 a5 fst_conv fun_upd_other fun_upd_other insert_iff mem_Collect_eq old.prod.inject p3 p_obs_def snd_conv surrey_state.select_convs(1) surrey_state.select_convs(2) surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) tst_def value_def var_def visible_var visible_writes_def writes_on_def)
    using a1 a2 a3 a4 a5 a6 apply auto
     apply (simp add: tst_def value_def var_def p_obs_def is_releasing_def visible_writes_def  valid_fresh_ts_def ts_oride_def, auto)
     apply(unfold wfs_def writes_on_def tst_def tst_def value_def var_def visible_var visible_writes_def writes_on_def)
     apply clarsimp
    by (smt Pair_inject fun_upd_other insert_iff surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5))
qed

corollary not_p_obs_RMW_pres:
  "wfs \<sigma>
  \<Longrightarrow> y \<noteq> x
  \<Longrightarrow> t \<noteq> t'
    \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
    \<Longrightarrow> \<sigma> RMW[y, v, w]\<^sub>t' \<sigma>'
    \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  using not_p_obs_Up_pres by force

lemma neg_pobs_val:
  assumes "isRd a"
     and "\<not> p_obs \<sigma> t x u"
     and "step t a \<sigma> \<sigma>''"
     and "avar a = x"
   shows "rd_val a \<noteq> Some u"
  using assms
  apply (simp add: step_def)
  apply (elim exE conjE)
  apply (cases rule: action.exhaust[where y = a], auto)
  using p_obs_def by blast

lemma visible_writes_subset:
  assumes "wfs \<sigma>"
     and "isRd a"
     and "step t a \<sigma> \<sigma>'"
     and "avar a = x"
   shows "visible_writes \<sigma>' t x \<subseteq> visible_writes \<sigma> t x"
  using assms
  apply (simp add: step_def)
  apply (elim exE conjE)
  apply (cases rule: action.exhaust[where y = a], auto)
  apply (simp add: visible_writes_def)
  apply (elim conjE)
  apply (cases "isRA a", auto)
  apply (unfold writes_on_def wfs_def read_trans_def ts_oride_def tst_def update_thrView_def rev_app_def, auto)
  by (smt fun_upd_same order_trans snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2))

lemma not_pobs_Rd_pres:
  assumes "isRd a"
     and "\<not> p_obs \<sigma> t x u "
     and "step t' a \<sigma> \<sigma>'"
   shows "\<not> p_obs \<sigma>' t x u"
  using assms
  apply (cases "t = t'", auto)
  apply(rule step_cases[OF assms(3)])
  apply simp
  apply (unfold p_obs_def read_trans_def update_thrView_def value_def visible_writes_def writes_on_def)
  apply auto
  apply (smt action.simps(10) dual_order.trans fun_upd_same fun_upd_triv fun_upd_twist mem_Collect_eq read_trans_def rev_app_def step_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) ts_oride_def update_thrView_def visible_writes_def writes_on_var)
  by (smt action.simps(10) fun_upd_other isRd.elims(2) read_trans_def rev_app_def step_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def)

corollary not_pobs_RdX_pres:
  "\<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow> y]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis RdX_def not_pobs_Rd_pres isRd.simps(1))

corollary not_pobs_RdA_pres:
  "\<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A y]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis RdA_def isRd.simps(1) not_pobs_Rd_pres)



lemma not_p_obs_Wr_val_pres:
  assumes "isWr a"
     and "\<not> p_obs \<sigma> t x u"
     and "step t' a \<sigma> \<sigma>'"
     and "wr_val a = Some v"
     and "u \<noteq> v"
   shows "\<not> p_obs \<sigma>' t x u"
  using assms
  apply (cases "t = t'", auto)
  apply(rule step_cases[OF assms(3)])
  apply (simp, auto)
  apply (unfold p_obs_def write_trans_def update_thrView_def step_def update_modView_def)
  apply auto
  apply (unfold rev_app_def tst_def update_mods_def add_cv_def valid_fresh_ts_def value_def writes_on_def visible_writes_def)
  apply safe
  apply (cases "avar a = x", safe, clarsimp)
  apply (smt dual_order.strict_implies_order dual_order.trans write_record.select_convs(1))
  apply clarsimp
  apply blast
  apply (cases "a", auto)
  by (smt write_record.select_convs(1))

corollary not_p_obs_WrX_val_pres:
  "u \<noteq> v
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis WrX_def isWr.simps(2) not_p_obs_Wr_val_pres wr_val.simps(1))

corollary not_p_obs_WrR_val_pres:
  "u \<noteq> v
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis WrR_def isWr.simps(2) not_p_obs_Wr_val_pres wr_val.simps(1))


lemma not_p_obs_Wr_diff_var_pres:
  assumes "isWr a"
     and "\<not> p_obs \<sigma> t x u"
     and "step t' a \<sigma> \<sigma>'"
     and "avar a = y"
     and "x \<noteq> y"
   shows "\<not> p_obs \<sigma>' t x u"
  using assms
  apply (cases "t = t'", auto)
  apply(rule step_cases[OF assms(3)])
  apply (simp, auto)
  apply (unfold p_obs_def write_trans_def update_thrView_def step_def update_modView_def)
  apply auto
  apply (unfold rev_app_def tst_def update_mods_def add_cv_def valid_fresh_ts_def value_def writes_on_def visible_writes_def)
  apply safe
  apply clarsimp
  apply blast
  by (cases "a", auto)

corollary not_p_obs_WrX_diff_var_pres:
  "x \<noteq> y
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis WrX_def avar.simps(2) isWr.simps(2) not_p_obs_Wr_diff_var_pres)

corollary not_p_obs_WrA_diff_var_pres:
  "x \<noteq> y
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
  by (metis WrR_def avar.simps(2) isWr.simps(2) not_p_obs_Wr_diff_var_pres)


lemma not_p_obs_Up_val_pres:
  assumes "isUp a"
     and "\<not> p_obs \<sigma> t x u"
     and "step t' a \<sigma> \<sigma>'"
     and "wr_val a = Some v"
     and "u \<noteq> v"
   shows "\<not> p_obs \<sigma>' t x u"
  using assms
  apply (cases "t = t'", auto)
  apply(rule step_cases[OF assms(3)])
  apply (simp, auto)
  apply (unfold p_obs_def update_trans_def update_thrView_def step_def update_modView_def)
  apply auto
  apply (unfold ts_oride_def Let_def tst_def rev_app_def tst_def update_mods_def add_cv_def valid_fresh_ts_def value_def writes_on_def visible_writes_def)
  apply safe
  apply (cases "avar a = x", safe, clarsimp)
  apply (smt Pair_inject dual_order.trans  fun_upd_same fun_upd_triv fun_upd_twist insert_iff leD less_eq_rat_def not_le prod.collapse surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5)  write_record.select_convs(1))
   apply clarsimp
   apply (case_tac "releasing \<sigma> (aa, ba)", clarsimp)
  apply (smt fun_upd_other order_trans)
  apply auto[1]
  apply(rule step_cases[OF assms(3)])
  apply (simp, auto)
  apply (unfold p_obs_def update_trans_def update_thrView_def step_def update_modView_def)
  apply auto
  apply (unfold ts_oride_def Let_def tst_def rev_app_def tst_def update_mods_def add_cv_def valid_fresh_ts_def value_def writes_on_def visible_writes_def)
  apply safe
  apply (cases "avar a = x", safe, clarsimp)
  apply (smt Pair_inject dual_order.trans  fun_upd_same fun_upd_triv fun_upd_twist insert_iff leD less_eq_rat_def not_le prod.collapse surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5)  write_record.select_convs(1))
   apply clarsimp
  by (smt write_record.select_convs(1))


corollary not_p_obs_RMW_val_pres:
  "u \<noteq> v
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> \<sigma> RMW[y, w, v]\<^sub>t' \<sigma>'
  \<Longrightarrow> \<not> [x \<approx>\<^sub>t u] \<sigma>'"
    using isUp.simps(3) not_p_obs_Up_val_pres wr_val.simps(2) by blast


lemma dobs_Rd_pres:
  assumes "isRd a"
     and "d_obs_t \<sigma> t x v"
     and "step t' a \<sigma> \<sigma>'"
     and "t \<noteq> t'"
     shows "d_obs_t \<sigma>' t x v"
  apply(rule step_cases[OF assms(3)])
  apply (simp add: step_def d_obs_t_def d_obs_def)
  apply (elim exE conjE)
  apply (smt Collect_cong assms(2) assms(4) d_obs_def d_obs_t_def fun_upd_other lastWr_def read_trans_def rev_app_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def writes_on_def)
  using assms by auto

lemma dobs_RdX_pres:
  "t \<noteq> t'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>
  \<Longrightarrow> \<sigma> [u \<leftarrow> y]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>'"
  by (metis RdX_def dobs_Rd_pres isRd.simps(1))

lemma dobs_RdA_pres:
  "t \<noteq> t'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>
  \<Longrightarrow> \<sigma> [u \<leftarrow>\<^sup>A y]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>'"
  by (metis RdA_def dobs_Rd_pres isRd.simps(1))

lemma dobs_Wr_pres:
  assumes "isWr a"
     and "d_obs_t \<sigma> t x v"
     and "avar a \<noteq> x"
     and "step t' a \<sigma> \<sigma>'"
     and "t \<noteq> t'"
     shows "d_obs_t \<sigma>' t x v"
  apply(rule step_cases[OF assms(4)])
  using assms(1) apply auto[1]
  defer
  using assms(1) apply auto[1]
  apply(unfold d_obs_t_def d_obs_def)
  using assms
  apply simp
   apply(case_tac "var w = x")
  using visible_var apply fastforce
  apply (rule conjI)
   apply(unfold d_obs_def d_obs_t_def) apply simp
  by clarsimp

lemma dobs_WrX_pres:
  "t \<noteq> t'
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>
  \<Longrightarrow> \<sigma> [y:= u]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>'"
  by (metis WrX_def avar.simps(2) dobs_Wr_pres isWr.simps(2))

lemma dobs_WrR_pres:
  "t \<noteq> t'
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>
  \<Longrightarrow> \<sigma> [y:=\<^sup>R u]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>'"
  by (metis WrR_def avar.simps(2) dobs_Wr_pres isWr.simps(2))


lemma dobs_Up_pres:
  assumes "isUp a"
     and "d_obs_t \<sigma> t x v"
     and "avar a \<noteq> x"
     and "step t' a \<sigma> \<sigma>'"
     and "t \<noteq> t'"
     shows "d_obs_t \<sigma>' t x v"
  apply(rule step_cases[OF assms(4)])
  using assms(1) apply auto[2]
  apply(unfold d_obs_t_def d_obs_def)
  using assms
  apply simp
   apply(case_tac "var w = x")
  using visible_var apply fastforce
  apply (rule conjI)
   apply(unfold d_obs_def d_obs_t_def) apply simp
   apply(unfold Let_def step_def update_mods_def valid_fresh_ts_def tst_def lastWr_def add_cv_def update_trans_def update_thrView_def update_modView_def rev_app_def)
   apply(case_tac "releasing \<sigma> w") apply clarsimp
   apply (case_tac "releasing \<sigma> (aaa, ba)") apply auto
     apply (simp_all add: value_def var_def  writes_on_def)
  by (smt Collect_cong fst_conv var_def visible_var)+


lemma dobs_RMW_pres:
  "t \<noteq> t'
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>
  \<Longrightarrow> \<sigma> RMW[y, w, u]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x =\<^sub>t v] \<sigma>'"
  using dobs_Up_pres by force


lemma cobs_pres:
  assumes "c_obs \<sigma> x u t y v"
      and "x \<noteq> y"
      and "wfs \<sigma>"
      and "v' \<noteq> u"
      and "step t (Read m x v') \<sigma> \<sigma>'"
    shows "c_obs \<sigma>' x u t y v"
  using assms apply (simp add: c_obs_def)
  apply (cases "m")
  apply (simp add: d_obs_def) apply safe[1]
  apply (smt Collect_cong action.simps(10) avar.simps(1) in_mono isRd.simps(1) lastWr_def read_trans_def rev_app_def step_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def visible_writes_subset writes_on_def)
  apply (smt Collect_cong action.simps(10) avar.simps(1) in_mono isRd.simps(1) lastWr_def read_trans_def rev_app_def step_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def visible_writes_subset writes_on_def)
  apply (simp add:visible_writes_def releasing_def step_def, clarify)
  apply (smt assms(5) avar.simps(1) in_mono isRd.simps(1) mem_Collect_eq read_trans_def rev_app_def snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) tst_def update_thrView_def value_def visible_writes_def visible_writes_subset)
  apply auto
  apply (simp add:visible_writes_def releasing_def step_def d_obs_def lastWr_def, auto)
  apply (smt dual_order.trans read_trans_def rev_app_def snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) tst_def update_thrView_def value_def)
  apply (smt dual_order.trans read_trans_def rev_app_def snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) tst_def update_thrView_def value_def)
  by (smt action.simps(10) avar.simps(1) in_mono isRd.simps(1) read_trans_def releasing_def rev_app_def step_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def visible_writes_subset)


lemma cobs_Rd_pres:
  assumes "c_obs \<sigma> x u t y v"
      and "isRd a"
      and "rd_val a = Some w"
      and "x \<noteq> y"
      and "wfs \<sigma>"
      and "w \<noteq> u"
      and "step t a \<sigma> \<sigma>'"
    shows "c_obs \<sigma>' x u t y v"
  using assms apply (simp add: c_obs_def step_def)
  apply (cases "a", auto)
  apply (simp_all add: Let_def lastWr_def rev_app_def d_obs_def step_def read_trans_def) apply auto
  apply (unfold writes_on_def tst_def value_def visible_writes_def update_thrView_def)
  apply auto
  apply (smt dual_order.trans fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply (smt dual_order.trans fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  using dual_order.trans apply fastforce
  using dual_order.trans apply fastforce
  apply (smt dual_order.trans fun_upd_other fun_upd_same releasing_def snd_conv surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) ts_oride_def tst_def)
  by (smt dual_order.trans releasing_def snd_conv surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2))


lemma cobs_RdX_pres:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> w \<noteq> u
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>
    \<Longrightarrow> \<sigma> [w \<leftarrow> z]\<^sub>t \<sigma>'
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>'"
  by (metis RdX_def cobs_Rd_pres isRd.simps(1) rd_val.simps(1))

lemma cobs_RdA_pres:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> w \<noteq> u
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>
    \<Longrightarrow> \<sigma> [w \<leftarrow>\<^sup>A z]\<^sub>t \<sigma>'
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>'"
  by (metis RdA_def cobs_Rd_pres isRd.simps(1) rd_val.simps(1))

lemma cobs_Rd_diff_var_pres:
  assumes "c_obs \<sigma> x u t y v"
      and "isRd a"
      and "avar a \<noteq> x"
      and "x \<noteq> y"
      and "wfs \<sigma>"
      and "step t' a \<sigma> \<sigma>'"
    shows "c_obs \<sigma>' x u t y v"
  apply(rule step_cases[OF assms(6)])
  defer
  using assms(2) apply auto[2]
  using assms(1,2,3,4,5)
  apply (simp add: c_obs_def)
  apply (simp_all add: Let_def lastWr_def rev_app_def d_obs_def step_def read_trans_def)
       apply (unfold writes_on_def tst_def value_def visible_writes_def update_thrView_def)
  apply simp
  by (smt fun_upd_other order.trans releasing_def surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) ts_oride_def tst_def)

lemma cobs_RdX_diff_var_pres:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> x \<noteq> z
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>
    \<Longrightarrow> \<sigma> [w \<leftarrow> z]\<^sub>t' \<sigma>'
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>'"
  by (metis RdX_def avar.simps(1) cobs_Rd_diff_var_pres isRd.simps(1))

lemma cobs_RdA_diff_var_pres:
  "wfs \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> x \<noteq> z
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>
    \<Longrightarrow> \<sigma> [w \<leftarrow>\<^sup>A z]\<^sub>t' \<sigma>'
    \<Longrightarrow> [x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma>'"
  by (metis RdA_def avar.simps(1) cobs_Rd_diff_var_pres isRd.simps(1))

lemma p_obs_Rd_intro2:
  assumes "step t (Read m x v) \<sigma> \<sigma>'"
    shows "p_obs \<sigma> t x v"
  apply(rule step_cases[OF assms(1)])
  defer
  apply simp
  apply blast
  using p_obs_def by fastforce

lemma init_d_obs:  "wfs \<sigma>
\<Longrightarrow> initial_state \<sigma> I
\<Longrightarrow> I x = u
\<Longrightarrow> [x =\<^sub>t u] \<sigma>"
  apply(simp add: initial_state_def d_obs_def d_obs_t_def)
    apply(elim exE conjE, intro conjI)
  defer
  apply(simp add: value_def)
  apply (simp add: lastWr_def)
  using last_write_write_on
proof -
  fix F :: "nat \<Rightarrow> rat"
  assume a1: "wfs \<sigma>"
  assume a3: "\<forall>t x. thrView \<sigma> t x = (x, F x)"
  assume a4: "\<forall>a b x. modView \<sigma> (a, b) x = (x, F x)"
  have f5: "\<And>n. var (lastWr \<sigma> n) = n \<and> lastWr \<sigma> n \<in> surrey_state.writes \<sigma>"
    using a1 writes_on_def by fastforce
  then have "\<And>n. \<exists>na. lastWr \<sigma> n = (na, F na)"
    by (metis a1 a4 old.prod.exhaust own_ModView)
    then show "thrView \<sigma> t x = lastWr \<sigma> x"
    using f5 a4 a3 a1 by (metis (no_types) own_ModView)
qed

lemma init_covered_v: "initial_state \<sigma> I
\<Longrightarrow> covered_v \<sigma> x (I x)"
  apply(simp add:  covered_v_def)
  apply clarsimp
  using initially_write_unique
  apply(intro conjI)
   apply (simp add: initial_wfs initially_write_unique)
  apply(unfold writes_on_def)
  proof -
  fix a :: nat and b :: rat
  assume a1: "initial_state \<sigma> I"
    assume a2: "(a, b) \<in> {w. var w = x \<and> w \<in> surrey_state.writes \<sigma>}"
    have "\<forall>p. I (var p) = value \<sigma> p"
      using a1 by (metis (no_types) initial_state_def value_def write_record.select_convs(1))
    then show "value \<sigma> (a, b) = I x"
      using a2 by auto
  qed

lemma covered_update_v_pres:
  assumes "covered_v \<sigma> x u"
  and "wfs \<sigma>"
  and "step t a \<sigma> \<sigma>'"
  and "isUp a"
  and "avar a = x"
  and "wr_val a = Some v"
shows "covered_v \<sigma>' x v"
  apply(rule step_cases[OF assms(3)])
  using assms(4) apply auto[1]
    using assms(4) isUp.simps(2) apply blast
    using assms(1,2,4,5)
       apply(simp add: covered_v_def)
    apply(intro allI impI, elim conjE)
    apply(unfold writes_on_def)
    apply simp
    apply clarsimp
    apply(simp add: visible_writes_def)
    apply(unfold writes_on_def)
    apply clarsimp
    apply(simp add: valid_fresh_ts_def)
     apply(unfold writes_on_def)
    apply(elim  conjE)
    apply(case_tac "ba = b", simp)
    apply(case_tac "ba < b", simp)
     apply (metis dual_order.irrefl prod.inject)
    apply clarsimp
    apply(simp add: update_trans_def rev_app_def Let_def update_mods_def add_cv_def update_modView_def update_thrView_def)
    apply (auto simp add: value_def)
    using assms(6) apply auto[1]
    apply (metis Pair_inject)
    by (metis Pair_inject)


corollary cvd_RMW_new_cvd:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow>  \<sigma> RMW[x, z, v]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,v] \<sigma>' "
  by (simp add: covered_update_v_pres)

lemma covered_read_v_pres:
  assumes "covered_v \<sigma> x u"
  and "wfs \<sigma>"
  and "step t a \<sigma> \<sigma>'"
  and "isRd a"
shows "covered_v \<sigma>' x u"
  apply(rule step_cases[OF assms(3)])
  defer
  using assms(4) apply auto[1]
  using assms(4) apply auto[1]
  using assms(1,2,4)
       apply(simp add: covered_v_def)
    apply(intro allI impI conjI, elim conjE)
   apply(unfold writes_on_def, simp)
    apply(simp add: read_trans_def rev_app_def Let_def  add_cv_def update_mods_def update_modView_def update_thrView_def)
   apply(intro conjI impI)
    apply(unfold wfs_def)
    apply(case_tac "syncing \<sigma> w b", clarsimp)
  apply(simp add: visible_writes_def)
    apply(unfold lastWr_def writes_on_def, clarsimp)
  apply blast
   apply auto[1]
  apply(simp add: value_def)
  done

lemma covered_v_RMW_d_obs:
  assumes "covered_v \<sigma> x v"
  and "wfs \<sigma>"
  and "step t a \<sigma> \<sigma>'"
  and "isUp a"
  and "avar a = x"
  and "wr_val a = Some u"
shows "d_obs_t \<sigma>' t x u"
  apply(rule step_cases[OF assms(3)])
  using assms(4) isUp.simps(1) apply blast
  using assms(4) isUp.simps(2) apply blast
  using assms(1,2, 4, 5, 6)
  apply(simp add: covered_v_def d_obs_t_def d_obs_def)
  apply(intro conjI)
   defer
  apply(elim conjE)
   apply(simp add: value_def)
  apply(simp add: visible_writes_def)
   apply(unfold  writes_on_def, clarsimp)
  apply(unfold  visible_writes_def writes_on_def, clarsimp)
  apply(simp add: update_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)
  apply(simp add: add_cv_def update_modView_def update_mods_def)
  apply(case_tac "releasing \<sigma> (x, b)", clarsimp)
   defer
   apply blast
  apply(simp add: ts_oride_def valid_fresh_ts_def)
  apply(intro impI)
  apply(unfold  wfs_def lastWr_def writes_on_def, clarsimp)
  done

corollary cvd_RMW_d_obs:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,v] \<sigma>
  \<Longrightarrow>  \<sigma> RMW[x, w, u]\<^sub>t \<sigma>'
  \<Longrightarrow> [x =\<^sub>t u] \<sigma>' "
  by (simp add: covered_v_RMW_d_obs)

lemma covered_diff_var_pres:
  assumes "covered_v \<sigma> x v"
  and "wfs \<sigma>"
  and "step t a \<sigma> \<sigma>'"
  and "avar a \<noteq> x"
shows "covered_v \<sigma>' x v"
  apply(rule step_cases[OF assms(3)])
   using assms(1,2,4)
    apply(simp add: covered_v_def)
    apply(unfold  writes_on_def, clarsimp)
     apply (intro conjI)
      apply(case_tac "xa \<noteq> aa")
       apply(simp add: visible_writes_def)
       apply clarsimp
       apply(unfold  wfs_def writes_on_def, simp)
   apply clarsimp
         apply(simp add: read_trans_def rev_app_def Let_def update_thrView_def)
   apply(intro conjI impI)
   apply(simp add: lastWr_def ts_oride_def)
       apply(unfold   writes_on_def, simp)
   apply(simp add: lastWr_def ts_oride_def)
       apply(unfold   writes_on_def, simp)
  apply (smt read_trans_def rev_app_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def)
   using assms(1,2,4)
    apply(simp add: covered_v_def)
    apply(unfold  writes_on_def, clarsimp)
    apply (intro conjI)
      apply(case_tac "xa \<noteq> aa")
       apply(simp add: visible_writes_def)
       apply clarsimp
       apply(unfold  wfs_def writes_on_def, simp)
   apply clarsimp
    apply(simp add: write_trans_def rev_app_def update_thrView_def value_def)
    apply(simp add: update_mods_def update_thrView_def update_modView_def add_cv_def)
   apply(intro conjI impI)
     apply (metis assms(2) last_write_write_on subset_iff visible_var visible_writes_in_writes writes_on_var)
    apply auto[1]
   using assms(1,2,4)
    apply(simp add: covered_v_def)
   apply(intro allI impI conjI)
    apply clarsimp
    apply(unfold  writes_on_def, clarsimp)
   apply(simp add: visible_writes_def)
    apply(unfold  writes_on_def, clarsimp)
    apply clarsimp
   apply(simp add: visible_writes_def)
   apply(unfold  writes_on_def value_def, clarsimp)
   done

corollary cvd_WrX_other_var_pres:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow> x\<noteq>y
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,u] \<sigma>' "
  using WrX_def avar.simps(2) covered_diff_var_pres by auto


corollary cvd_WrR_other_var_pres:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow> x\<noteq>y
  \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,u] \<sigma>' "
  using WrR_def avar.simps(2) covered_diff_var_pres by auto


corollary cvd_RMW_other_val_pres:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow> x\<noteq>y
  \<Longrightarrow>  \<sigma> RMW[y, u, v]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,u] \<sigma>' "
  using avar.simps(3) covered_diff_var_pres by blast


corollary cvd_RMW_pres:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow> \<sigma> RMW[x, z, v]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,v] \<sigma>' "
  using avar.simps(3) covered_update_v_pres isUp.simps(3) wr_val.simps(2) by blast


corollary cvd_Rdx_pres:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow> \<sigma> [a \<leftarrow> y]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,u] \<sigma>' "
  by (simp add: RdX_def covered_read_v_pres)

corollary cvd_RdA_pres:
  "wfs \<sigma>
  \<Longrightarrow> cvd[x,u] \<sigma>
  \<Longrightarrow> \<sigma> [a \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>'
  \<Longrightarrow> cvd[x,u] \<sigma>' "
  by (simp add: RdA_def covered_read_v_pres)

lemma backward_cvd:
  assumes "cvd[x, u] \<sigma>'"
  and "wfs \<sigma>"
  and "avar a \<noteq> x"
  and "step t a \<sigma> \<sigma>'"
  and "\<not>isUp a"
shows "cvd[x, u] \<sigma>"
  apply(rule step_cases[OF assms(4)])
  using assms (1,2,3)
    apply(simp add: covered_v_def read_trans_def visible_writes_def rev_app_def Let_def update_thrView_def)
    apply(unfold writes_on_def)
    apply clarsimp
    apply(intro conjI)
     apply(unfold lastWr_def writes_on_def)
     apply simp
    apply(simp add: value_def)
  using assms(1,2,3)
  apply(simp add: covered_v_def)
  apply(case_tac "lastWr (write_trans t b w v \<sigma> ts') x \<noteq> lastWr \<sigma> x")
  apply (metis assms(3) visible_var write_to_different_var)
   apply simp
    apply(case_tac "value (write_trans t b w v \<sigma> ts') (lastWr \<sigma> x) \<noteq> value \<sigma> (lastWr \<sigma> x)")
  apply (metis avar.simps(2) lastWr_visible value_not_change_write_to_different_var visible_var)
   apply simp
   apply(intro allI impI conjI)
  apply (unfold writes_on_def)
  apply(elim conjE)
    apply clarsimp
  apply(simp add: visible_writes_def)
  apply (unfold writes_on_def)
   apply(elim conjE)
   apply clarsimp
  using assms(5) by auto

corollary cvd_backwards_WrX:
  "wfs \<sigma>
    \<Longrightarrow> cvd[x, u] \<sigma>'
    \<Longrightarrow> y \<noteq> x
    \<Longrightarrow> \<sigma> [y := v]\<^sub>t \<sigma>'
    \<Longrightarrow> cvd[x, u] \<sigma> "
  by (metis WrX_def avar.simps(2) backward_cvd isUp.simps(2))

corollary cvd_backwards_WrR:
  "wfs \<sigma> \<Longrightarrow> cvd[x, u] \<sigma>' \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>' \<Longrightarrow> cvd[x, u] \<sigma> "
  by (metis WrR_def avar.simps(2) backward_cvd isUp.simps(2))

corollary cvd_backwards_RdX:
  "wfs \<sigma> \<Longrightarrow> cvd[x, u] \<sigma>' \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<sigma> [v \<leftarrow> y]\<^sub>t \<sigma>' \<Longrightarrow> cvd[x, u] \<sigma> "
  by (metis RdX_def avar.simps(1) backward_cvd isUp.simps(1))

corollary cvd_backwards_RdA:
  "wfs \<sigma> \<Longrightarrow> cvd[x, u] \<sigma>' \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>' \<Longrightarrow> cvd[x, u] \<sigma> "
  by (metis RdA_def avar.simps(1) backward_cvd isUp.simps(1))

lemma not_cvd_pres:
  assumes "\<not>cvd[x, u] \<sigma>"
  and "wfs \<sigma>"
  and "step t a \<sigma> \<sigma>'"
  and "\<not>isUp a"
shows "\<not>cvd[x, u] \<sigma>'"
  apply(rule step_cases[OF assms(3)])
  using assms(1,2)
    apply(simp add: covered_v_def visible_writes_def read_trans_def Let_def rev_app_def)
    apply(simp add: add_cv_def update_mods_def update_modView_def update_thrView_def lastWr_def value_def)
    apply(unfold wfs_def  writes_on_def)
    apply simp
  using assms(1,2)
  apply(case_tac "xa \<noteq> x")
  using assms(3) backward_cvd apply force
    apply(simp add: covered_v_def visible_writes_def write_trans_def Let_def rev_app_def valid_fresh_ts_def)
    apply(simp add: add_cv_def update_mods_def update_modView_def update_thrView_def lastWr_def value_def)
   apply(unfold wfs_def  writes_on_def, clarsimp)
  apply(intro conjI)
  using neq_iff apply blast
  apply (metis less_irrefl subsetCE)
  using assms(4) isUp.simps(3) by blast

corollary not_cvd_RdX_pres:
  "wfs \<sigma> \<Longrightarrow> \<not>cvd[x, u] \<sigma>  \<Longrightarrow> \<sigma> [v \<leftarrow> y]\<^sub>t \<sigma>' \<Longrightarrow> \<not>cvd[x, u] \<sigma>' "
  using RdX_def not_cvd_pres by auto

corollary not_cvd_RdA_pres:
  "wfs \<sigma> \<Longrightarrow> \<not>cvd[x, u] \<sigma>  \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>' \<Longrightarrow> \<not>cvd[x, u] \<sigma>' "
  using RdA_def not_cvd_pres by auto

corollary not_cvd_WrX_pres:
  "wfs \<sigma> \<Longrightarrow> \<not>cvd[x, u] \<sigma>  \<Longrightarrow> \<sigma> [y := v]\<^sub>t \<sigma>' \<Longrightarrow> \<not>cvd[x, u] \<sigma>' "
  using WrX_def not_cvd_pres by auto

corollary not_cvd_WrR_pres:
  "wfs \<sigma> \<Longrightarrow> \<not>cvd[x, u] \<sigma>  \<Longrightarrow>  \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>' \<Longrightarrow> \<not>cvd[x, u] \<sigma>' "
  using WrR_def not_cvd_pres by auto

lemma cvd_u_not_cvd_v: "w \<in> writes_on \<sigma> x \<Longrightarrow> w \<notin> covered \<sigma> \<Longrightarrow> value \<sigma> w = u  \<Longrightarrow> cvd[x, u] \<sigma> \<Longrightarrow> u \<noteq> v \<Longrightarrow> \<not>cvd[x, v]\<sigma>"
  apply(simp add: covered_v_def)
  by (metis surj_pair)

lemma new_update_not_covered:
  assumes "wfs \<sigma>"
     and "w \<in> visible_writes \<sigma> t x"
     and "v = value \<sigma> w"
     and "w \<notin> covered \<sigma>"
     and "valid_fresh_ts \<sigma> w ts'"
   shows "(var w, ts') \<notin> covered (update_trans t w v' \<sigma> ts')"
  apply(subgoal_tac "(var w, ts') \<notin> writes \<sigma>")
  apply(subgoal_tac "w \<in> writes \<sigma>")
  apply simp using assms(1)
  using wfs_def apply fastforce
  apply (meson assms(2) subsetCE visible_writes_in_writes)
  by (metis assms(1) assms(5) fst_conv less_irrefl prod.sel(2) tst_def valid_fresh_ts_def var_def wfs_def)

lemma RMW_exist_w_in_post: "wfs \<sigma> \<Longrightarrow> \<sigma> RMW[x, u, v]\<^sub>t \<sigma>' \<Longrightarrow> \<exists> w . w \<in> writes_on \<sigma>' x \<and> value \<sigma>' w = v  \<and> w \<notin> covered \<sigma>'"
  apply(simp add:  step_def visible_writes_def valid_fresh_ts_def update_trans_def Let_def rev_app_def)
  apply(simp add: add_cv_def update_mods_def update_thrView_def update_modView_def value_def)
  apply(unfold writes_on_def)
  apply clarsimp
  by (metis less_irrefl subsetCE wfs_def)


lemma update_reads_cvd_v:
  assumes "cvd[x, u] \<sigma>"
  and "isUp a"
  and "avar a = x"
  and "rd_val a = Some v"
  and "wr_val a = Some z"
  and "step t a \<sigma> \<sigma>'"
shows "u = v"
  apply(rule step_cases[OF assms(6)])
  using assms(2) isUp.simps(1) apply blast
  using assms(2) isUp.simps(2) apply blast
  using assms(1,2,3,4)
  by (smt covered_v_def mem_Collect_eq option.inject rd_val.simps(2) visible_writes_def)


corollary Up_reads_cvd_v:
  "cvd[x, u] \<sigma>  \<Longrightarrow>  \<sigma> RMW[x, v, z]\<^sub>t \<sigma>' \<Longrightarrow> v = u "
  using avar.simps(3) isUp.simps(3) rd_val.simps(2) update_reads_cvd_v wr_val.simps(2) by blast

(*****************************************************)

lemmas  opsem_def  =
  amo_def
  mo_def
  d_vorder_def
  p_vorder_def
  enc_def
  enc_t_def
  no_val_def

lemma pvord_to_dvord:
  assumes "p_vorder \<sigma> u x v"
  and "amo \<sigma> x u"
  and "amo \<sigma> x v"
  shows "d_vorder \<sigma> u x v"
  using assms
  apply(simp add: opsem_def)
  by (metis fst_conv linorder_neqE_linordered_idom var_def writes_on_var)

lemma enc_read_intro:
  assumes "isRd a"
  and "avar a = x"
  and "rd_val a = Some v"
  and "step t a \<sigma> \<sigma>'"
shows "enc_t \<sigma>' t x v"
  apply(rule step_cases[OF assms(4)])
  defer
  using assms(1) apply auto[1]
  using assms(1) isRd.simps(3) apply blast  apply(simp add: enc_t_def enc_def)
  defer
  using assms(3) apply auto[1]
  apply(unfold read_trans_def Let_def rev_app_def)
  apply simp
  apply(case_tac "syncing \<sigma> (aa, b) ba")
   defer apply simp
   apply(simp add: update_thrView_def)
   apply (rule conjI)
  apply (smt assms(2) avar.simps(1) mem_Collect_eq order_refl surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) value_def visible_writes_def)
   apply (rule impI)
   apply(unfold value_def writes_on_def visible_writes_def)
  apply simp
  using assms(2) avar.simps(1) apply blast
apply simp
   apply(simp add: update_thrView_def ts_oride_def)
   apply (rule conjI)
  apply blast
  using assms(2) avar.simps(1) by blast

corollary enc_RdX_intro:
  "\<sigma> [v \<leftarrow> x]\<^sub>t \<sigma>' \<Longrightarrow> [en x v]\<^sub>t \<sigma>'"
  by (metis RdX_def avar.simps(1) enc_read_intro isRd.simps(1) rd_val.simps(1))

corollary enc_RdA_intro:
  "\<sigma> [v \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>' \<Longrightarrow> [en x v]\<^sub>t \<sigma>'"
  by (metis RdA_def avar.simps(1) enc_read_intro isRd.simps(1) rd_val.simps(1))

lemma enc_write_intro:
  assumes "isWr a"
  and "avar a = x"
  and "wr_val a = Some v"
  and "step t a \<sigma> \<sigma>'"
shows "enc_t \<sigma>' t x v"
  apply(rule step_cases[OF assms(4)])
  using assms(1) isWr.simps(1) apply blast
   defer
  using assms(1) apply auto[1]
  apply(simp add: enc_t_def enc_def)
  apply (elim conjE impE)
  apply (rule conjI)
   defer
  using assms(2) apply auto[1]
  apply (rule impI)
  apply simp
  apply(simp add:  valid_fresh_ts_def)
  apply (elim conjE)
  apply clarsimp
  apply(case_tac "aa \<noteq> x")
   apply(simp add: visible_writes_def)
   apply(unfold writes_on_def)
   apply simp
  apply clarsimp
  apply(simp add: write_trans_def rev_app_def value_def)
  apply(unfold update_thrView_def  add_cv_def update_modView_def update_mods_def)
  apply clarsimp
  using assms(3) by auto

corollary enc_WrX_intro:
  "\<sigma> [x := v]\<^sub>t \<sigma>' \<Longrightarrow> [en x v]\<^sub>t \<sigma>'"
  by (metis WrX_def avar.simps(2) enc_write_intro isWr.simps(2) wr_val.simps(1))

corollary enc_WrR_intro:
  "\<sigma> [x :=\<^sup>R v]\<^sub>t \<sigma>' \<Longrightarrow> [en x v]\<^sub>t \<sigma>'"
  by (metis WrR_def avar.simps(2) enc_write_intro isWr.simps(2) wr_val.simps(1))

lemma enc_update_intro:
  assumes "isUp a"
  and "avar a = x"
  and "wr_val a = Some v"
  and "step t a \<sigma> \<sigma>'"
shows "enc_t \<sigma>' t x v"
  using assms apply (simp add: enc_t_def step_def enc_def)
  apply (case_tac "a", auto)
  apply (simp add: update_simps)
  apply (unfold writes_on_def)
  apply (simp add: value_def ts_oride_def tst_def)
  by blast

lemma not_p_vorder_Write__pres:
  assumes "\<not> p_vorder \<sigma> v x v"
and "isWr a"
and "avar a  = x"
and "wr_val a \<noteq> Some v"
and "step t a \<sigma> \<sigma>'"
shows "\<not> p_vorder \<sigma>' v x v"
  apply(rule step_cases[OF assms(5)])
  using assms(2) isWr.simps(1) apply blast
  defer
  using assms(2) isWr.simps(3) apply blast
  apply (elim conjE)
  apply(case_tac "xa = x")
   defer
  using assms(3) apply auto[1]
  using assms
  apply(simp add:  valid_fresh_ts_def visible_writes_def opsem_def)
  apply(unfold writes_on_def)
  apply simp
  apply(simp add: write_trans_def rev_app_def)
  apply(unfold update_thrView_def  add_cv_def update_modView_def update_mods_def value_def)
  by simp

lemma amo_intro:
assumes "init_val \<sigma> x u"
and "\<not> p_vorder \<sigma> u x v"
shows "amo \<sigma> x v"
  using assms
  apply (simp add: opsem_def)
  by (metis assms(2) init_val_def p_vorder_def)

lemma init_val_pres:
assumes "[init x u] \<sigma>"
and "step t action \<sigma> \<sigma>'"
shows "init_val \<sigma>' x u"
  using assms
  apply (auto simp add: step_def)
  apply (cases action, auto)
  apply (auto simp add: init_val_def)[1]
  apply (metis read_trans_def rev_app_def surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def)
  apply (auto simp add: init_val_def)[1]
  apply (simp add: valid_fresh_ts_def update_thrView_def write_trans_def rev_app_def add_cv_def update_mods_def update_modView_def)
  apply (simp add: visible_writes_def tst_def value_def var_def writes_on_def)
  apply (metis (no_types, lifting) fst_conv less_trans mo_def not_less_iff_gr_or_eq snd_conv tst_def var_def)
  proof -
  fix a b y v ts'
  assume a1: "init_val \<sigma> x u"  and
         a2: "(a, b) \<in> visible_writes \<sigma> t y" and
         a5: "valid_fresh_ts \<sigma> (a, b) ts'"
  show "init_val (update_trans t (a, b) v \<sigma> ts') x u"
    using a1 a2 a5
  apply (simp add: update_trans_def)
    apply (auto simp add: init_val_def value_def valid_fresh_ts_def  rev_app_def add_cv_def update_mods_def update_thrView_def update_modView_def)
    by (smt fst_conv fun_upd_other insert_iff less_trans mem_Collect_eq mo_def not_less_iff_gr_or_eq snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) tst_def var_def visible_writes_def writes_on_def)
qed

lemma amo_intro_step:
  assumes "init_val \<sigma> x u"
  and "u \<noteq> v"
  and "\<not> p_vorder \<sigma> u x v"
  and "step t action \<sigma> \<sigma>'"
  shows "amo \<sigma>' x v"
  using assms
  apply (simp add: opsem_def step_def)
  apply (intro impI allI conjI)
  apply (elim conjE exE)
  apply (cases action, auto)
    apply (auto simp add: update_thrView_def value_def read_trans_def init_val_def rev_app_def)
    apply (metis (no_types, lifting) fst_conv mo_def snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) tst_def var_def)
    apply (auto simp add:  write_trans_def rev_app_def add_cv_def update_mods_def)
  apply (smt dual_order.irrefl fst_conv insert_compr mem_Collect_eq mo_def snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) tst_def update_modView_def update_thrView_def var_def writes_on_def)
    apply (auto simp add:  update_trans_def rev_app_def add_cv_def update_mods_def)
    apply (auto simp add: valid_fresh_ts_def init_val_def write_trans_def rev_app_def update_thrView_def update_modView_def add_cv_def update_mods_def)
  by (smt dual_order.irrefl fst_conv fun_upd_other insert_compr mem_Collect_eq mo_def snd_conv surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(4) surrey_state.update_convs(5) tst_def var_def writes_on_def)

lemma not_pvorder_pres_step_wr:
assumes "init_val \<sigma> x u"
and "\<not> p_vorder \<sigma> u x v"
and "isWr action"
and "wr_val action \<noteq> Some v"
and "wr_val action \<noteq> Some u"
and "step t action \<sigma> \<sigma>'"
shows "\<not> p_vorder \<sigma>' u x v"
  using assms
  apply (simp add: step_def opsem_def)
  apply (intro allI impI)
  apply (elim exE)
  apply (cases "action", auto)
  apply (auto simp add: update_thrView_def value_def fun_upd_other write_trans_def rev_app_def add_cv_def valid_fresh_ts_def init_val_def update_modView_def update_mods_def)
  by (smt Pair_inject insert_iff mem_Collect_eq surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(4) surrey_state.update_convs(5) write_record.ext_inject write_record.surjective writes_on_def)

lemma amo_pres_step_wr:
assumes "amo \<sigma> x v"
and "isWr action"
and "wr_val action \<noteq> Some v"
and "step t action \<sigma> \<sigma>'"
shows "amo \<sigma>' x v"
  apply(rule step_cases[OF assms(4)])
  using assms(2) apply auto[1]
  using assms
  apply(simp add: valid_fresh_ts_def visible_writes_def write_trans_def rev_app_def)
   apply(simp add: add_cv_def update_mods_def update_thrView_def update_modView_def)
   apply(elim conjE)
   apply(simp add: opsem_def init_val_def value_def)
   apply(unfold writes_on_def, simp)
  using assms(2) isWr.simps(3) by blast

corollary amo_Wr_diff_val_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> u \<noteq> v \<Longrightarrow>  \<sigma> [y := v]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  by (metis WrX_def amo_pres_step_wr isWr.simps(2) option.inject wr_val.simps(1))

corollary amo_WrR_diff_val_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> u \<noteq> v \<Longrightarrow>  \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  by (metis WrR_def amo_pres_step_wr isWr.simps(2) option.inject wr_val.simps(1))

lemma amo_write_pres:
assumes "amo \<sigma> x v"
and "isWr action"
and "avar action \<noteq> x"
and "step t action \<sigma> \<sigma>'"
shows "amo \<sigma>' x v"
  apply(rule step_cases[OF assms(4)])
  using assms(2) apply auto[1] defer
  using assms(2) apply auto[1]
  using assms(1,2,3)
  apply(simp add: valid_fresh_ts_def visible_writes_def write_trans_def rev_app_def)
   apply(simp add: add_cv_def update_mods_def update_thrView_def update_modView_def)
   apply(elim conjE)
   apply(simp add: opsem_def init_val_def value_def)
   by(unfold writes_on_def, simp)

corollary amo_WrX_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> x \<noteq> y \<Longrightarrow>  \<sigma> [y := v]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  by (metis WrX_def amo_write_pres avar.simps(2) isWr.simps(2))

corollary amo_WrR_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> x \<noteq> y \<Longrightarrow>  \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  by (metis WrR_def amo_write_pres avar.simps(2) isWr.simps(2))

lemma amo_update_pres:
assumes "amo \<sigma> x v"
and "isUp action"
and "avar action \<noteq> x"
and "step t action \<sigma> \<sigma>'"
shows "amo \<sigma>' x v"
  apply(rule step_cases[OF assms(4)])
  using assms(2) apply auto[2]
  using assms(2) apply auto[1]
  using assms(1,2,3)
  apply(simp add: valid_fresh_ts_def visible_writes_def update_trans_def rev_app_def)
   apply(elim conjE)
   apply(simp add: Let_def opsem_def init_val_def value_def)
   apply (case_tac "releasing \<sigma> (a, b)", auto)
  apply (simp add: tst_def var_def ts_oride_def add_cv_def update_mods_def update_modView_def update_thrView_def)
    apply (unfold writes_on_def, simp)
  apply (simp add: tst_def var_def ts_oride_def add_cv_def update_mods_def update_modView_def update_thrView_def)
  done

corollary amo_Up_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> x \<noteq> y \<Longrightarrow>  \<sigma> RMW[y, v, w]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  using amo_update_pres by force

lemma amo_read_pres:
assumes "amo \<sigma> x v"
and "isRd action"
and "step t action \<sigma> \<sigma>'"
shows "amo \<sigma>' x v"
  apply(rule step_cases[OF assms(3)])
  defer
  using assms(2) apply auto[1]
  using assms(2) apply auto[1]
  using assms
  apply(unfold opsem_def read_trans_def Let_def rev_app_def writes_on_def update_thrView_def visible_writes_def value_def)
  by clarsimp

corollary amo_RdX_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> \<sigma> [v \<leftarrow> y]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  by (metis RdX_def amo_read_pres isRd.simps(1))

corollary amo_RdA_pres:
  "[\<one>\<^sub>x u] \<sigma>  \<Longrightarrow> \<sigma> [v \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>' \<Longrightarrow> [\<one>\<^sub>x u] \<sigma>'"
  by (metis RdA_def amo_read_pres isRd.simps(1))

lemma d_vorder_intro:
  assumes "step t action \<sigma> \<sigma>'"
 and "p_vorder \<sigma> u x v"
 and "[init x v'] \<sigma>"
 and np: "\<not> p_vorder \<sigma> v' x v"
shows "d_vorder \<sigma>' u x v"
  using assms
  apply (simp add: opsem_def)
  apply (intro conjI allI impI)
  apply (metis fst_conv var_def writes_on_var)
  apply (metis np init_val_def less_imp_not_less mo_def p_vorder_def snd_conv tst_def)
  by (metis np init_val_def less_imp_not_less mo_def p_vorder_def snd_conv tst_def)

lemma d_vorder_intro_w:
  assumes "enc_t \<sigma> t xv u"
and "init_val  \<sigma> xv z"
and "amo \<sigma> xv u"
and "\<not> p_vorder  \<sigma> z xv v"
and "amo \<sigma> xv v"
and "v \<noteq> u"
and "v \<noteq> z"
and "u  \<noteq> z"
and "avar action = xv"
and "wr_val action = Some v"
and "step t action  \<sigma> \<sigma>'"
and "isWr action"
shows "d_vorder  \<sigma>' u xv v"
  apply(rule step_cases[OF assms(11)])
  using assms(10) apply auto[1]
   defer
  using assms(12) apply auto[1]
  using assms(1, 2, 3,4,5,6,7,8,9,10,12)
  apply clarsimp
  apply(simp add: opsem_def write_trans_def rev_app_def init_val_def valid_fresh_ts_def visible_writes_def)
  apply(simp add: add_cv_def update_modView_def update_thrView_def update_mods_def value_def)
  apply(unfold writes_on_def)
  apply clarsimp
  apply(intro conjI)
   apply clarsimp
   apply(intro conjI impI)
  apply clarsimp
  apply(case_tac "bb = bd")
  apply linarith
  apply(case_tac "bb = bc")
     apply blast
    apply (metis linorder_cases)
    apply metis
    by (metis dual_order.strict_trans2)

corollary WrX_d_vorder:
  "[\<zero>\<^sub>x v]\<^sub>z \<sigma> \<Longrightarrow> [\<one>\<^sub>x u] \<sigma> \<Longrightarrow> [\<one>\<^sub>x v] \<sigma> \<Longrightarrow> [en x u]\<^sub>t \<sigma> \<Longrightarrow> u \<noteq> z \<Longrightarrow> v \<noteq> u \<Longrightarrow> v \<noteq> z  \<Longrightarrow> \<sigma> [x := v]\<^sub>t \<sigma>' \<Longrightarrow>  [u \<hookrightarrow>\<^sub>x v] \<sigma>'"
  by (metis WrX_def avar.simps(2) d_vorder_intro_w isWr.simps(2) no_val_def wr_val.simps(1))

corollary WrR_d_vorder:
  "[\<zero>\<^sub>x v]\<^sub>z \<sigma> \<Longrightarrow> [\<one>\<^sub>x u] \<sigma> \<Longrightarrow> [\<one>\<^sub>x v] \<sigma> \<Longrightarrow> [en x u]\<^sub>t \<sigma> \<Longrightarrow> u \<noteq> z \<Longrightarrow> v \<noteq> u \<Longrightarrow> v \<noteq> z  \<Longrightarrow> \<sigma> [x :=\<^sup>R v]\<^sub>t \<sigma>' \<Longrightarrow>  [u \<hookrightarrow>\<^sub>x v] \<sigma>'"
  by (metis WrR_def avar.simps(2) d_vorder_intro_w isWr.simps(2) no_val_def wr_val.simps(1))

lemma d_vorder_one_way:
  assumes "d_vorder \<sigma> u x v"
shows "\<not> d_vorder \<sigma> v x u"
  using assms
  apply (unfold opsem_def, safe)
  using not_less_iff_gr_or_eq by blast

lemma enc_read_p_vorder1:
  assumes "enc_t \<sigma> t xv v"
and "isRd action"
and "avar action = xv"
and "rd_val action = Some u"
and "step t action \<sigma> \<sigma>'"
shows "v \<noteq> u \<longrightarrow> p_vorder \<sigma> v xv u"
  apply(rule step_cases[OF assms(5)])
  using assms
  apply(unfold opsem_def read_trans_def Let_def rev_app_def writes_on_def update_thrView_def visible_writes_def)
    apply simp
    apply(case_tac "syncing \<sigma> w b")
     apply simp
     apply (elim conjE)
  apply(intro impI)
     apply simp
  apply(case_tac "v = u")
      apply linarith
     apply clarsimp
  using le_neq_trans apply fastforce
  apply (metis dual_order.trans order.not_eq_order_implies_strict prod.collapse tst_def var_def)
  using isRd.simps(2) apply blast
  using isRd.simps(3) by blast

lemma enc_read_p_vorder:
  assumes "enc_t \<sigma> t xv v"
and "isRd action"
and "avar action = xv"
and "rd_val action = Some u"
and "step t action \<sigma> \<sigma>'"
shows "v \<noteq> u \<longrightarrow> p_vorder \<sigma>' v xv u"
  apply(rule step_cases[OF assms(5)])
    defer
  using assms(2) apply auto[2]
  using assms(1,2,3,4)
  apply(unfold opsem_def read_trans_def Let_def rev_app_def writes_on_def update_thrView_def visible_writes_def)
  apply simp
    apply(case_tac "syncing \<sigma> w b")
     apply simp
     apply (elim conjE)
  apply(intro impI)
     apply (simp_all add: value_def)
  apply(case_tac "v = u")
      apply linarith
     apply clarsimp
  using less_eq_rat_def apply fastforce
  by (metis dual_order.trans order.not_eq_order_implies_strict prod.collapse tst_def var_def)

corollary enc_RdA_p_vorder:
  "[en x v]\<^sub>t \<sigma> \<Longrightarrow> \<sigma> [u \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>' \<Longrightarrow> v \<noteq> u \<longrightarrow> [v \<leadsto>\<^sub>x u] \<sigma>'"
  by (metis RdA_def avar.simps(1) enc_read_p_vorder isRd.simps(1) rd_val.simps(1))

corollary enc_Rdx_p_vorder:
  "[en x v]\<^sub>t \<sigma> \<Longrightarrow> \<sigma> [u \<leftarrow> x]\<^sub>t \<sigma>' \<Longrightarrow> v \<noteq> u \<longrightarrow> [v \<leadsto>\<^sub>x u] \<sigma>'"
  by (metis RdX_def avar.simps(1) enc_read_p_vorder isRd.simps(1) rd_val.simps(1))

lemma p_vorder_write_pres:
  assumes "p_vorder \<sigma> v xv u"
    and "isWr action"
    and "step t action \<sigma> \<sigma>'"
  shows "p_vorder \<sigma>' v xv u"
  apply(rule step_cases[OF assms(3)])
  using assms(2) isWr.simps(1) apply blast
  using assms
   apply(simp add: opsem_def value_def write_trans_def rev_app_def visible_writes_def update_thrView_def)
   apply(simp add: update_modView_def update_mods_def add_cv_def)
   apply(unfold writes_on_def valid_fresh_ts_def)
   apply(elim conjE)
   apply clarsimp
  apply (metis (full_types) dual_order.irrefl)
  using assms(2) isWr.simps(3) by blast

corollary p_vorder_WrX_p_vorder:
  " [v \<leadsto>\<^sub>x u] \<sigma> \<Longrightarrow> \<sigma> [y := z]\<^sub>t \<sigma>' \<Longrightarrow> [v \<leadsto>\<^sub>x u] \<sigma>'"
  by (metis WrX_def isWr.simps(2) p_vorder_write_pres)

corollary p_vorder_WrR_p_vorder:
  " [v \<leadsto>\<^sub>x u] \<sigma> \<Longrightarrow> \<sigma> [y :=\<^sup>R z]\<^sub>t \<sigma>' \<Longrightarrow> [v \<leadsto>\<^sub>x u] \<sigma>'"
  by (metis WrR_def isWr.simps(2) p_vorder_write_pres)

lemma read_pres_not_p_vorder:
  assumes "\<not> p_vorder \<sigma> v xv u"
  and "isRd action"
  and "step t action \<sigma> \<sigma>'"
  shows "\<not> p_vorder \<sigma>' v xv u"
  apply(rule step_cases[OF assms(3)])
    defer
  using assms(2) apply auto[2]
  using assms
  by(simp add: opsem_def value_def)

lemma read_pres_p_vorder:
  assumes "p_vorder \<sigma> v xv u"
  and "isRd action"
  and "step t action \<sigma> \<sigma>'"
  shows "p_vorder \<sigma>' v xv u"
  apply(rule step_cases[OF assms(3)])
    defer
  using assms(2) apply auto[1]
  using assms(2) apply auto[1]
  using assms
  by(simp add: opsem_def value_def)

corollary p_vorder_RdX_p_vorder:
  " [v \<leadsto>\<^sub>x u] \<sigma> \<Longrightarrow> \<sigma> [z \<leftarrow> y]\<^sub>t \<sigma>' \<Longrightarrow> [v \<leadsto>\<^sub>x u] \<sigma>'"
  by (metis (full_types) RdX_def isRd.simps(1) read_pres_p_vorder)

corollary p_vorder_RdA_p_vorder:
  " [v \<leadsto>\<^sub>x u] \<sigma> \<Longrightarrow> \<sigma> [z \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>' \<Longrightarrow> [v \<leadsto>\<^sub>x u] \<sigma>'"
  by (metis (full_types) RdA_def isRd.simps(1) read_pres_p_vorder)

lemma d_vorder_Read_pres:
  assumes "d_vorder \<sigma> v x u"
  and "isRd action"
  and "step t action \<sigma> \<sigma>'"
  shows "d_vorder \<sigma>' v x u"
  apply(rule step_cases[OF assms(3)])
    defer
  using assms(2) apply auto[1]
  using assms(2) apply auto[1]
  using assms
  apply(simp add: d_vorder_def)
  apply(simp add: value_def)
  apply(unfold opsem_def read_trans_def writes_on_def rev_app_def Let_def, simp)
  apply(elim conjE)
  apply(case_tac "syncing \<sigma> w b", simp)
  apply (simp add: update_thrView_def value_def)
  by (simp add: update_thrView_def value_def)

corollary d_vorder_RdX_pres:
  " [v \<hookrightarrow>\<^sub>x u] \<sigma>
  \<Longrightarrow> \<sigma> [z \<leftarrow> y]\<^sub>t \<sigma>'
  \<Longrightarrow> [v \<hookrightarrow>\<^sub>x u] \<sigma>'"
  by (metis RdX_def isRd.simps(1) d_vorder_Read_pres)

corollary d_vorder_RdA_pres:
  " [v \<hookrightarrow>\<^sub>x u] \<sigma>
  \<Longrightarrow> \<sigma> [z \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>'
  \<Longrightarrow> [v \<hookrightarrow>\<^sub>x u] \<sigma>'"
  by (metis RdA_def isRd.simps(1) d_vorder_Read_pres)

lemma d_vorder_Write_pres:
  assumes "d_vorder \<sigma> v x u"
    and "step t a \<sigma> \<sigma>'"
    and "isWr a"
    and "wr_val a \<noteq> Some v"
    and "wr_val a \<noteq> Some u"
    and "avar a = x"
 shows "d_vorder \<sigma>' v x u"
  apply(rule step_cases[OF assms(2)])
  using assms(3) apply auto[1] defer
  using assms(3) isWr.simps(3) apply blast
  using assms(1,3,4,5,6)
  apply simp
  apply(elim conjE)
  apply clarsimp
  apply(simp add: d_vorder_def)
  apply(intro conjI)
   apply clarsimp apply auto
   apply (smt UnE fun_upd_def mem_Collect_eq rev_app_def singletonD surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) update_modView_def update_mods_def update_thrView_def add_cv_def value_def write_record.ext_inject write_record.surjective write_trans_def writes_on_def)
  using assms(2) assms(3) p_vorder_write_pres by blast

corollary d_vorder_WrX_pres:
  " [v \<hookrightarrow>\<^sub>x u] \<sigma>
  \<Longrightarrow> \<sigma> [x := w]\<^sub>t \<sigma>'
  \<Longrightarrow> w \<noteq> u
  \<Longrightarrow> w \<noteq> v
  \<Longrightarrow> [v \<hookrightarrow>\<^sub>x u] \<sigma>'"
  by (simp add: WrX_def d_vorder_Write_pres)

corollary d_vorder_WrR_pres:
  " [v \<hookrightarrow>\<^sub>x u] \<sigma>
  \<Longrightarrow> \<sigma> [x :=\<^sup>R w]\<^sub>t \<sigma>'
  \<Longrightarrow> w \<noteq> u
  \<Longrightarrow> w \<noteq> v
  \<Longrightarrow> [v
  \<hookrightarrow>\<^sub>x u] \<sigma>'"
  by (simp add: WrR_def d_vorder_Write_pres)

lemma enc_pres:
  assumes "enc_t \<sigma> t xv u"
  and "step t' action \<sigma> \<sigma>'"
  shows "enc_t \<sigma>' t xv u"
  apply(rule step_cases[OF assms(2)])
  using assms
  apply simp
  apply(simp add: enc_t_def enc_def visible_writes_def read_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)
  apply(case_tac "syncing \<sigma> w b")
  apply (unfold writes_on_def)
  apply clarsimp
  apply(auto simp add: tst_def value_def enc_t_def enc_def visible_writes_def read_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)
  using assms
  apply(simp add: enc_t_def enc_def visible_writes_def write_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)
  apply (unfold writes_on_def)
   apply clarsimp
  apply(auto simp add: tst_def value_def enc_t_def enc_def visible_writes_def read_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)[1]
  apply(auto simp add: add_cv_def update_mods_def update_modView_def)
  apply (metis dual_order.strict_implies_order dual_order.trans not_le snd_conv tst_def valid_fresh_ts_def)
  apply (smt fst_conv mem_Collect_eq not_less_iff_gr_or_eq snd_conv tst_def valid_fresh_ts_def var_def writes_on_def)
  using assms
  apply(simp add: enc_t_def enc_def visible_writes_def update_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)
  apply(auto simp add: add_cv_def valid_fresh_ts_def update_mods_def  tst_def value_def enc_t_def enc_def visible_writes_def read_trans_def Let_def rev_app_def update_thrView_def ts_oride_def)
  apply (unfold writes_on_def)
  apply auto
  apply (unfold update_modView_def, clarsimp)
  apply (smt dual_order.irrefl dual_order.strict_implies_order dual_order.trans fun_upd_same fun_upd_triv fun_upd_twist snd_conv ts_oride_def tst_def)
  apply auto
  apply (metis leD less_imp_le order_trans)
  by (metis leD order_refl)

lemma enc_pvord_step:
  "enc_t \<sigma> t xv u
   \<Longrightarrow> isRd action
   \<Longrightarrow> avar action = xv
   \<Longrightarrow> rd_val action = Some v
   \<Longrightarrow> step t action \<sigma> \<sigma>'
   \<Longrightarrow> u \<noteq> v
   \<Longrightarrow> p_vorder \<sigma>' u xv v"
  apply (frule enc_read_p_vorder[where action = action])
  by blast+

lemma no_val_read_pres:
  assumes "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "isRd a"
  and "step t a \<sigma> \<sigma>'"
  shows "[\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  by (meson assms(1) assms(2) assms(3) init_val_pres no_val_def read_pres_not_p_vorder)

corollary no_val_RdA_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> \<sigma> [r \<leftarrow>\<^sup>A y]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  using  no_val_read_pres
  by (metis RdA_def isRd.simps(1))

corollary no_val_Rdx_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> \<sigma> [r \<leftarrow> y]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  using  no_val_read_pres
  by (metis RdX_def isRd.simps(1))

lemma write_no_val:
  assumes "wr_val a = Some u"
   and "[init x i] \<sigma>"
  and "avar a = x"
  and "isWr a"
  and "step t a \<sigma> \<sigma>'"
shows "\<not>[\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  apply(rule step_cases[OF assms(5)])
  using assms(4) apply auto[1]
  using assms(1,2,3,4)
   apply(simp add:  opsem_def init_val_def visible_writes_def valid_fresh_ts_def value_def)
   apply(simp add: write_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
   apply(unfold writes_on_def)
   apply(elim conjE)
   apply clarsimp
  using order.asym apply blast
    using assms(4) by auto

corollary WrX_no_val:
  "[init x i] \<sigma>
  \<Longrightarrow> \<sigma> [x := u]\<^sub>t \<sigma>'
  \<Longrightarrow> \<not>[\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  using  write_no_val
  by (metis WrX_def avar.simps(2) isWr.simps(2) wr_val.simps(1))

lemma no_val_write_diff_value_pres:
  assumes "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "isWr a"
  and "wr_val a \<noteq> Some u"
  and "step t a \<sigma> \<sigma>'"
shows "[\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  apply(rule step_cases[OF assms(4)])
  using assms(2) apply auto[1]
  using assms(1)
   apply(elim conjE)
   apply(simp add:  opsem_def init_val_def visible_writes_def valid_fresh_ts_def value_def)
   apply(simp add: write_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
   apply(unfold writes_on_def)
  apply(elim conjE, intro conjI)
    apply simp
    apply clarsimp
    apply (smt less_trans order.asym)
    apply clarsimp
  using assms(3) apply auto[1]
  using assms(2) by auto


corollary no_val_WrX_diff_val_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> v \<noteq> u
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  by (metis WrX_def isWr.simps(2) no_val_write_diff_value_pres option.sel wr_val.simps(1))

corollary no_val_WrR_diff_val_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> v \<noteq> u
  \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  by (metis WrR_def isWr.simps(2) no_val_write_diff_value_pres option.sel wr_val.simps(1))

lemma no_val_write_diff_var_pres:
  assumes "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "isWr a"
  and "avar a \<noteq> x"
  and "step t a \<sigma> \<sigma>'"
shows "[\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  apply(rule step_cases[OF assms(4)])
  using assms(2) apply auto[1]
  using assms(1)
   apply(elim conjE)
   apply(simp add:  opsem_def init_val_def visible_writes_def valid_fresh_ts_def value_def)
   apply(simp add: write_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
   apply(unfold writes_on_def)
  apply(elim conjE, intro conjI)
    apply simp
    apply clarsimp
    apply (smt less_trans order.asym)
    apply clarsimp
  using assms(3) apply auto[1]
  using assms(2) by auto

corollary no_val_Wr_diff_var_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  by (metis WrX_def avar.simps(2) isWr.simps(2) no_val_write_diff_var_pres)

corollary no_val_WrR_diff_var_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> \<sigma> [y :=\<^sup>R v]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  by (metis WrR_def avar.simps(2) isWr.simps(2) no_val_write_diff_var_pres)

lemma d_obs_enc: "wfs \<sigma>
\<Longrightarrow> d_obs_t \<sigma> t x v
\<Longrightarrow> enc_t \<sigma> t x v"
    apply(simp add: opsem_def d_obs_t_def d_obs_def lastWr_def value_def)
  apply(unfold wfs_def writes_on_def) apply simp
  apply(elim conjE)
  by (metis (no_types, lifting) less_eq_rat_def)

lemma no_val_Update_diff_var_pres:
  assumes "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "isUp a"
  and "avar a \<noteq> x"
  and "step t a \<sigma> \<sigma>'"
shows "[\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  apply(rule step_cases[OF assms(4)])
  using assms(2) apply auto[1]
  using assms(2) apply auto[1]
  using assms(1)
   apply(elim conjE)
   apply(simp add: update_simps opsem_def)
  apply(unfold writes_on_def)
  apply clarsimp
  apply (intro conjI impI)
   apply(simp add: releasing_def tst_def )
  using assms(4) init_val_pres apply blast
  apply clarsimp
  apply (intro conjI impI)
   apply(simp add: releasing_def tst_def )
  using assms(3) avar.simps(3) apply blast
  apply clarsimp
  apply (intro conjI impI)
   apply(simp add: releasing_def tst_def )
  using assms(3) avar.simps(3) apply blast
    apply(simp add: releasing_def ts_oride_def tst_def value_def)
  apply auto
  using assms(3) apply auto[1]
  using assms(4) init_val_pres apply blast
  using assms(3) avar.simps(3) apply blast
  using assms(3) avar.simps(3) apply blast
    apply(simp add: releasing_def ts_oride_def tst_def value_def)
  using assms(3) by auto

corollary no_val_RMW_diff_var_pres:
  " [\<zero>\<^sub>x u]\<^sub>i \<sigma>
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> \<sigma> RMW[y, v, w]\<^sub>t \<sigma>'
  \<Longrightarrow> [\<zero>\<^sub>x u]\<^sub>i \<sigma>'"
  using no_val_Update_diff_var_pres by force

lemma d_obs_read_value:
  assumes "wfs cs"
and "[x =\<^sub>t u] cs"
and "cs [v \<leftarrow> x]\<^sub>t cs'"
shows "v = u"
  using assms
  apply(simp add: d_obs_t_def d_obs_def lastWr_def tst_def step_def RdX_def visible_writes_def read_trans_def rev_app_def)
  apply(simp add: update_thrView_def)
  apply(unfold  writes_on_def)[1]
  apply(elim exE conjE)
  by (metis assms(2) assms(3) d_obs_RdX_pres d_obs_p_obs_agree p_obs_RdX_intro wfs_preserved)

lemma p_obs_Wr_pres :  \<comment> \<open>Rule: DV-set\<close>
  assumes "True"
      and "wr_val a = Some u"
      and "avar a = y"
      and "p_obs \<sigma> t x v"
      and "step t' a \<sigma> \<sigma>'"
      and "t \<noteq> t'"
    shows "p_obs \<sigma>' t x v"
  apply(rule step_cases[OF assms(5)])
  using assms apply simp
   using assms(4)
   apply(simp add: p_obs_def)
  apply(simp add: write_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
    apply(elim exE conjE)
   apply(rule_tac x = aa in exI)
    apply(rule_tac x = ba in exI)
   apply(simp add: visible_writes_def value_def)
   apply(intro conjI impI)
   using assms(6) apply presburger
   using assms(6) apply fastforce
   using assms(6) apply fastforce
   using assms(6) apply fastforce
              apply (metis less_le snd_conv tst_def valid_fresh_ts_def writes_on_var)
   apply (metis dual_order.irrefl snd_conv tst_def valid_fresh_ts_def writes_on_var)
     apply(unfold wfs_def writes_on_def value_def tst_def var_def valid_fresh_ts_def, simp)[1]
   using assms(6) apply fastforce
   apply fastforce
   using assms(6) apply linarith
   using assms(6) apply fastforce
       apply force
   apply (metis fst_conv var_def writes_on_var)
   apply (metis fst_conv var_def writes_on_var)
     apply(unfold Let_def wfs_def writes_on_def value_def tst_def var_def valid_fresh_ts_def, simp)[1]
   using assms(4)
   apply(simp add: p_obs_def)
  apply(simp add: update_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
    apply(elim exE conjE)
   apply(rule_tac x = aa in exI)
    apply(rule_tac x = b in exI)
   apply(simp add: visible_writes_def value_def)
   apply(intro conjI impI)
     apply(unfold Let_def wfs_def writes_on_def value_def tst_def var_def valid_fresh_ts_def, simp)[1]
     apply(unfold Let_def wfs_def writes_on_def value_def tst_def var_def valid_fresh_ts_def, simp)[1]
  using assms(6) apply presburger
     apply(unfold Let_def wfs_def writes_on_def value_def tst_def var_def valid_fresh_ts_def, simp)[1]
      by blast

corollary p_obs_Wr_pres_write:
  " [x \<approx>\<^sub>t u] \<sigma>
  \<Longrightarrow> t \<noteq> t'
  \<Longrightarrow> \<sigma> [y := v]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x \<approx>\<^sub>t u] \<sigma>'"
  using p_obs_Wr_pres
  by (metis WrX_def wr_val.simps(1))


lemma d_obs_Wr_p_obs_intro :  \<comment> \<open>Rule: DV-set\<close>
  assumes "wfs \<sigma>"
      and "wr_val a = Some u"
      and "avar a = x"
      and "d_obs_t \<sigma> t' x m"
      and "step t' a \<sigma> \<sigma>'"
      and "t \<noteq> t'"
    shows "p_obs \<sigma>' t x u"
  apply(rule step_cases[OF assms(5)])
  using assms apply simp
   using assms(4)
   apply(simp add: p_obs_def d_obs_t_def d_obs_def)
  apply(simp add: write_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
    apply(elim exE conjE)

   apply(simp add: visible_writes_def value_def)
   apply(intro conjI impI)
   using assms(6) apply presburger
      apply(unfold wfs_def writes_on_def value_def tst_def var_def valid_fresh_ts_def, simp)[1]
   apply(rule_tac x = x in exI)
      apply(rule_tac x = ts' in exI)
   apply(intro conjI impI)
   apply (metis assms(1) last_write_max less_le_trans linear sup.strict_order_iff tst_def wfs_def)
   apply (metis assms(2) option.inject wr_val.simps(1))

   using assms(6) apply fastforce
   using assms(6) apply fastforce
   using assms(6) apply fastforce
      apply (metis)
   using assms(6) apply linarith
   using assms(3) avar.simps(2) apply blast


  apply(simp add: update_trans_def rev_app_def add_cv_def update_mods_def update_modView_def update_thrView_def)
    apply(elim exE conjE)
    apply(simp add: p_obs_def d_obs_t_def d_obs_def)
  apply(rule_tac x = x in exI)
    apply(rule_tac x = ts' in exI)
   apply(simp add: visible_writes_def value_def Let_def)
   apply(unfold writes_on_def, simp)[1]
   apply(intro conjI impI)
   using assms(6) apply linarith
   using assms(6) apply blast
   using assms(6) apply linarith
   using assms(6) apply linarith
   using assms(6) apply linarith
   apply (metis assms(1) assms(4) d_obs_def d_obs_t_def last_write_max linorder_not_le order_antisym order_less_trans valid_fresh_ts_def wfs_def)
   apply (metis assms(2) option.inject wr_val.simps(2))
   using assms(3) avar.simps(3) apply blast
   using assms(3) avar.simps(3) apply blast
   using assms(3) avar.simps(3) apply blast
   using assms(6) apply linarith
   using assms(6) apply linarith
   using assms(6) apply force
   using assms(6) apply fastforce
   apply (metis assms(1) assms(4) d_obs_def d_obs_t_def last_write_max linorder_not_le order_antisym order_less_trans valid_fresh_ts_def wfs_def)
   apply (metis assms(2) option.inject wr_val.simps(2))
   using assms(3) avar.simps(3) apply blast
   using assms(3) avar.simps(3) apply blast
   by (metis assms(3) avar.simps(3))

corollary d_obs_Wr_p_obs_intro_write:
  "wfs \<sigma>
  \<Longrightarrow> [x =\<^sub>t' m] \<sigma>
  \<Longrightarrow> t \<noteq> t'
  \<Longrightarrow> \<sigma> [x := u]\<^sub>t' \<sigma>'
  \<Longrightarrow> [x \<approx>\<^sub>t u] \<sigma>'"
  using d_obs_Wr_p_obs_intro
  by (metis WrX_def avar.simps(2) wr_val.simps(1))

lemma d_obs_pre_p_obs_post:
  assumes "wfs \<sigma>"
  and "[m \<approx>\<^sub>t u] \<sigma>"
  and "\<sigma> [v \<leftarrow> n]\<^sub>t \<sigma>'"
  and "m \<noteq> n"
shows "[m \<approx>\<^sub>t u] \<sigma>'"
  apply(rule step_cases[OF assms(3)])
    apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  apply(case_tac "syncing \<sigma> w b"; simp)
     apply (metis RdX_def isRA.simps(1) syncing_def)
    apply(simp add: p_obs_def visible_writes_def var_def)
    apply(intro conjI impI)
  apply(unfold writes_on_def value_def var_def tst_def)
  using RdX_def assms(4) apply auto[1]
  using assms    apply(simp add: syncing_def)
  apply safe
  apply (smt (z3) CollectD p_obs_def prod.collapse tst_def value_def var_def visible_writes_def writes_on_def)
  apply (smt (z3) CollectD p_obs_def prod.collapse subsetD tst_def value_def var_def visible_writes_def visible_writes_in_writes writes_on_var)
  apply (simp add: RdX_def)
  apply (simp add: RdX_def)
  done

lemma d_obs_pre_write_p_obs_post:
  assumes "wfs \<sigma>"
  and "[m \<approx>\<^sub>t u] \<sigma>"
  and "\<sigma> [n := v]\<^sub>t \<sigma>'"
  and "m \<noteq> n"
shows "[m \<approx>\<^sub>t u] \<sigma>'"
  apply(rule step_cases[OF assms(3)])
  apply (simp add: WrX_def)
  using assms
  apply(simp add: write_trans_def rev_app_def update_thrView_def )
    apply(simp add: p_obs_def visible_writes_def var_def update_mods_def update_modView_def)
   apply(unfold writes_on_def value_def var_def tst_def; simp)
  apply(intro conjI impI)
  using WrX_def apply auto[1]
  by (simp add: WrX_def)

end
