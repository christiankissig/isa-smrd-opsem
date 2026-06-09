theory SimpleLBDataAddCtrl
  imports  OpSem_Proof_Rules HOL.Transitive_Closure 
begin
datatype PC =
  L1
| L2
| L3
| L4
| END

consts t1 :: T 
consts t2 :: T
consts x :: L
consts y :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and> x \<noteq> y"

type_synonym C = "PC \<times> V option"

record prog_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r1 :: V
  r2 :: V
  f ::  "((C \<times> C) set) set "
  g ::  "((C \<times> C) set) set "

consts F  :: "((C \<times> C) set) set "
consts F\<^sub>1 :: "((C \<times> C) set) set "
consts F\<^sub>e :: "((C \<times> C) set) set "
consts G  :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>0 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>1 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>2 :: "((C \<times> C) set) set "
consts G\<^sub>e :: "((C \<times> C) set) set "




definition "futures \<equiv>   F  = {{((L1, None), (L2, None))}}
                      \<and> F\<^sub>1 = {{((L2, None), (L2, None))}}
                      \<and> F\<^sub>e = {{}}
                      \<and> G = {{((L3, Some 0), (L3, Some 0))},
                             {((L3, Some 1), (L3, Some 1))},
                             {((L3, Some 2), (L4, None))}}
                      \<and> G\<^sub>3\<^sub>2 = {{((L4, None), (L4, None))}}
                      \<and> G\<^sub>3\<^sub>1 = {{}}
                      \<and> G\<^sub>3\<^sub>0 = {{}}
                      \<and> G\<^sub>e = {{}}"

lemmas [simp] = futures_def thrdsvars_def
definition "members rel \<equiv> {a . a\<in>Domain rel \<or>  a\<in>Range rel} "

definition "relID S \<equiv> { e . fst e = snd e \<and> fst e \<in>members S}"

definition "minimal (p) (s) \<equiv> p\<in>Domain s \<and> p\<notin>Range (s - relID s)"



definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


definition prog :: "T \<Rightarrow> PC \<Rightarrow> nat option \<Rightarrow> prog_state \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog t p rv s s' \<equiv> 
(
  if t = t1
    then
      if p = L1
      then
        (state s) [r1 s' \<leftarrow> x]\<^sub>t (state s') \<and>
        r2 s = r2 s' \<and>
        f s' = F\<^sub>1 \<and> g s' = g s \<and> rv = Some (r1 s')
  else
      if p = L2
      then
        (state s) [y := ((r1 s) + 1)]\<^sub>t (state s') 
         \<and> r1 s = r1 s' \<and> r2 s = r2 s'   
         \<and> f s' = F\<^sub>e \<and> g s' = g s   \<and> rv = None          
      else
        False
else
  if t = t2
    then
      if p = L3
        then
          (state s) [r2 s' \<leftarrow> y]\<^sub>t (state s')                 
          \<and> r1 s = r1 s' \<and> f s' = f s \<and> rv = Some (r2 s')
          \<and> (r2 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>0)
          \<and> (r2 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1)
          \<and> (r2 s' = 2 \<longrightarrow> g s' = G\<^sub>3\<^sub>2) 

      else
        if p = L4
          then
            (state s) [x := 1]\<^sub>t (state s') 
            \<and> r1 s = r1 s'  \<and> r2 s = r2 s'  
            \<and> f s' = f s  \<and> rv = None    
            \<and>  g s' = G\<^sub>e
               
          else
            False
  else
    False
)"




definition prog_future_inv :: "((C \<times> C) set) set \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_future_inv p s \<equiv> 
  if p = F  then 

      [y =\<^sub>t2 0] (state s) \<and> r2 s = 0 \<and> (\<forall> i . i\<noteq>0 \<longrightarrow> \<not>[x \<approx>\<^sub>t1 i] (state s))

  else  if p = F\<^sub>1 then

      [y =\<^sub>t2 0] (state s) \<and> r2 s = 0 \<and> r1 s = 0

  else if p = F\<^sub>e  then

     r1 s \<noteq> 1 \<or> r2 s \<noteq> 2

  else if p = G then

     (\<forall> i . i \<notin> {0,1} \<longrightarrow> \<not>[y \<approx>\<^sub>t2 i] (state s))

  else if p = G\<^sub>3\<^sub>2 then

     False

  else if p = G\<^sub>e \<or>  p = G\<^sub>3\<^sub>0 \<or>  p = G\<^sub>3\<^sub>1 then
  
     True
 
  else  False
  "



lemma noteq[simp]: "futures \<Longrightarrow> F\<noteq>F\<^sub>1 \<and> F\<noteq>F\<^sub>e \<and> F\<^sub>1\<noteq>F\<^sub>e \<and>
 F\<^sub>1 \<noteq> G \<and> F\<^sub>e \<noteq> G \<and> G \<noteq> F \<and> G\<^sub>e \<noteq> G\<^sub>3\<^sub>2  \<and> G\<^sub>3\<^sub>2 \<noteq> G \<and>
  G\<^sub>3\<^sub>2 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>2 \<noteq> F\<^sub>1  \<and> G \<noteq> F\<^sub>e \<and> F\<^sub>e \<noteq> F\<^sub>1 \<and> F\<^sub>1 \<noteq> F 
 \<and> G\<^sub>e\<noteq> G \<and> G \<noteq> F\<^sub>1 \<and> G\<^sub>3\<^sub>2 \<noteq> F \<and> F\<^sub>e \<noteq> F \<and> G\<^sub>e \<noteq> F\<^sub>1 \<and> G\<^sub>e \<noteq> F \<and> G \<noteq> G\<^sub>e"
  using  futures_def
  by (smt (verit) PC.distinct(1) PC.distinct(11) PC.distinct(15) PC.distinct(9) insertCI prod.inject singletonD)


  lemma po_local_t1:
    assumes "wfs (state s)"
      and "thrdsvars"
      and "futures"
      and "f s \<in> {F, F\<^sub>1}"
      and "c \<in> f s"
      and "minimal p c"
      and "prog_future_inv (f s) s"
      and "prog t1 (fst p) (snd p) s s'"
    shows "prog_future_inv (f s') s'"
    using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L1")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI impI)
    apply (metis  dobs_RdX_pres)
      apply (metis neqE not_less0 not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis Domain.simps Pair_inject insertI1 minimal_def prod.collapse singletonD)
    apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
    apply (metis Domain.simps Pair_inject insertI1 minimal_def prod.collapse singletonD)
    done



  lemma po_local_t2:
  assumes "wfs (state s)"
      and "futures"
      and "thrdsvars"
      and "g s \<in> {G, G\<^sub>3\<^sub>2}"
      and "c \<in> g s"
      and "minimal p c"
      and "prog_future_inv (g s) s"
      and "prog t2 (fst p) (snd p) s s'"
    shows "prog_future_inv (g s') s'"
    using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p  = L3")
    apply clarsimp
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI impI)
                 apply simp_all
               apply (metis insert_not_empty singleton_inject)
              apply(case_tac " G = G\<^sub>e"; simp_all)
               apply (metis (no_types, lifting) insertI1 insert_not_empty singletonD)
              apply (metis neq0_conv not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres)    
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis not_pobs_RdX_pres p_obs_RdX_intro)
    apply (smt (z3) Domain.simps fst_conv insertE insertI1 minimal_def option.distinct(1) singletonD snd_conv)
    apply(subgoal_tac " fst p  = L4")
    apply simp_all
      apply(simp add: prog_future_inv_def prog_def)
    apply (smt (z3) One_nat_def insertI1 option.distinct(1) singleton_iff snd_conv)
    apply (smt (z3) Domain.simps fst_conv insertE insertI1 minimal_def option.distinct(1) singletonD snd_conv)
    done



lemma po_global_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>e}"
    and "g s \<in> {G, G\<^sub>3\<^sub>2}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv (f s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp 
  apply(simp add: prog_future_inv_def prog_def)
        apply (metis d_obs_RdX_pres d_obs_read_value not_pobs_RdX_pres)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L4")
       apply(simp add: prog_future_inv_def prog_def)
  apply (smt (z3) empty_not_insert insertI1 option.distinct(1) singleton_iff snd_conv)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp 
  apply(simp add: prog_future_inv_def prog_def)
      apply (metis d_obs_RdX_pres d_obs_read_value)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp 
     apply(simp add: prog_future_inv_def prog_def)
     apply (metis n_not_Suc_n not_pobs_RdX_pres numeral_2_eq_2 p_obs_RdX_intro zero_less_Suc)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L4")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis d_obs_WrX_other)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L4")
  apply(simp add: prog_future_inv_def prog_def)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  done

lemma G3130e: "futures \<Longrightarrow> G\<^sub>3\<^sub>1 = G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>0 = G\<^sub>e \<and> G\<^sub>3\<^sub>1 = G\<^sub>e"
  by (metis futures_def)

lemma po_global_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1}"
    and "g s \<in> {G, G\<^sub>3\<^sub>2, G\<^sub>3\<^sub>1, G\<^sub>3\<^sub>0, G\<^sub>e}"
    and "c \<in> f s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t1 (fst p) (snd p) s s'"
  shows "prog_future_inv (g s') s'"
  apply(subgoal_tac "{G, G\<^sub>3\<^sub>2, G\<^sub>3\<^sub>1, G\<^sub>3\<^sub>0, G\<^sub>e} = {G, G\<^sub>3\<^sub>2, G\<^sub>e}")
   defer 
  using assms
  using G3130e apply fastforce
  using assms
  apply simp
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L1")
  apply(simp add: prog_future_inv_def prog_def)
        apply (metis Suc_neq_Zero d_obs_p_obs_agree gr0_implies_Suc not_pobs_RdX_pres)
  apply (metis Domain.simps Pair_inject insertI1 minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L1")
       apply(simp add: prog_future_inv_def prog_def)
       apply (smt (z3) PC.distinct(15) fst_conv insertI1 singleton_iff)
  apply (smt (verit, del_insts) PC.distinct(11) PC.distinct(15) Pair_inject empty_not_insert insertI1 prog_future_inv_def singletonD)
  apply(subgoal_tac "fst p = L1")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis Domain.simps Pair_inject insertI1 minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L2")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis d_obs_p_obs_agree gr0_implies_Suc not_p_obs_WrX_val_pres old.nat.distinct(1))
  apply (metis Domain.simps Pair_inject insertI1 minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
  apply (smt (z3) PC.distinct(15) fst_conv insertI1 singleton_iff)
  apply (metis Domain.simps Pair_inject insertI1 minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L2")
  apply(simp add: prog_future_inv_def prog_def)
  by (metis Domain.simps fst_conv insertI1 minimal_def singletonD)



end
