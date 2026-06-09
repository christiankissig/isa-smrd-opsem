theory MessagePassing
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
consts G\<^sub>e :: "((C \<times> C) set) set "




definition "futures \<equiv>   F  = {{((L1, None), (L2, None))}}
                      \<and> F\<^sub>1 = {{((L2, None), (L2, None))}}
                      \<and> F\<^sub>e = {{}}
                      \<and> G = {{((L3, Some 0),( L3, Some 0))},
                             {((L3, Some 1), (L4, Some 1))}}
                      \<and> G\<^sub>3\<^sub>1 = {{((L4, Some 1), (L4, Some 1))}}
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
        (state s) [x := 1]\<^sub>t (state s') \<and>
         r1 s = r1 s' \<and> r2 s = r2 s'  \<and> 
        f s' = F\<^sub>1 \<and> g s' = g s \<and> rv = None
  else
      if p = L2
      then
        (state s) [y :=\<^sup>R 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s' \<and> r2 s = r2 s'   
         \<and> f s' = F\<^sub>e \<and> g s' = g s   \<and> rv = None          
      else
        False
else
  if t = t2
    then
      if p = L3
        then
          (state s) [r1 s' \<leftarrow>\<^sup>A y]\<^sub>t (state s')                 
          \<and> r2 s = r2 s' \<and> f s' = f s \<and> rv = Some (r1 s')
          \<and> (r1 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>0)
          \<and> (r1 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1)

      else
        if p = L4
          then
            (state s) [r2 s' \<leftarrow> x]\<^sub>t (state s') 
            \<and> r1 s = r1 s'   
            \<and> f s' = f s  \<and> rv = Some (r2 s')    
            \<and>  g s' = G\<^sub>e
               
          else
            False
  else
    False
)"




definition prog_future_inv :: " T \<Rightarrow> ((C \<times> C) set) set \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_future_inv t p  s \<equiv> 
  if t = t1 \<and> p = F   then 

      [x =\<^sub>t1 0] (state s) \<and> \<not>[y \<approx>\<^sub>t2 1] (state s)

  else  if t = t1 \<and> p = F\<^sub>1 then

      [x =\<^sub>t1 1] (state s) \<and> \<not>[y \<approx>\<^sub>t2 1] (state s)

  else if t = t1 \<and> p = F\<^sub>e  then

       True

  else if t = t2 \<and> p = G then

      [y = 1]\<^sub>t2\<lparr>x = 1\<rparr> (state s)

  else if t = t2 \<and> p = G\<^sub>3\<^sub>1 then

     [x =\<^sub>t2 1] (state s)

  else if t = t2 \<and> (p = G\<^sub>e \<or>  p = G\<^sub>3\<^sub>0) then
  
     r1 s = 1 \<longrightarrow> r2 s = 1
 
  else  False
  "



lemma noteq[simp]: "futures \<Longrightarrow> F\<noteq>F\<^sub>1 \<and> F\<noteq>F\<^sub>e \<and> F\<^sub>1\<noteq>F\<^sub>e \<and>
 F\<^sub>1 \<noteq> G \<and> F\<^sub>e \<noteq> G \<and> G \<noteq> F \<and>
   G \<noteq> F\<^sub>e \<and> F\<^sub>e \<noteq> F\<^sub>1 \<and> F\<^sub>1 \<noteq> F 
 \<and> G\<^sub>e\<noteq> G \<and> G \<noteq> F\<^sub>1  \<and> F\<^sub>e \<noteq> F \<and> G\<^sub>e \<noteq> F\<^sub>1 \<and> G\<^sub>e \<noteq> F \<and> G \<noteq> G\<^sub>e"
  using  futures_def
  by (smt (z3) PC.distinct(1) PC.distinct(11) PC.distinct(15) insertCI insert_absorb old.prod.inject singleton_iff)


  lemma po_local_t1:
    assumes "wfs (state s)"
      and "thrdsvars"
      and "futures"
      and "f s \<in> {F, F\<^sub>1}"
      and "c \<in> f s"
      and "minimal p c"
      and "prog_future_inv t1 (f s) s"
      and "prog t1 (fst p) (snd p) s s'"
    shows "prog_future_inv t1 (f s') s'"
    using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L1")
    apply(simp add: prog_future_inv_def prog_def)
      apply(intro conjI impI)
       apply (metis d_obs_WrX_set)
    apply (metis not_p_obs_WrX_pres)
    apply (metis Domain.simps Pair_inject  minimal_def prod.collapse singletonD)
    apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
    apply (metis Domain.simps Pair_inject minimal_def prod.collapse singletonD)
    done



  lemma po_local_t2:
  assumes "wfs (state s)"
      and "futures"
      and "thrdsvars"
      and "g s \<in> {G, G\<^sub>3\<^sub>1}"
      and "c \<in> g s"
      and "minimal p c"
      and "prog_future_inv t2 (g s) s"
      and "prog t2 (fst p) (snd p) s s'"
    shows "prog_future_inv t2 (g s') s'"
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
         apply (smt (z3) PC.distinct(15) Pair_inject insertI1 singletonD)
    
    apply (smt (z3) Domain.simps Pair_inject assms(8) c_obs_RdA_d_obs insert_iff minimal_def option.inject prog_def singletonD snd_conv)
    apply (metis cobs_RdA_pres)
    apply (smt (z3) Domain.simps Pair_inject assms(8) insert_iff minimal_def option.inject prog_def singletonD snd_conv)

    apply (smt (z3) Domain.simps fst_conv insertE insertI1 minimal_def option.distinct(1) singletonD snd_conv)
    apply(subgoal_tac " fst p  = L4")
    apply simp_all
     apply(simp add: prog_future_inv_def prog_def)
    apply (smt (z3) Domain_empty Domain_insert One_nat_def PC.distinct(15) d_obs_read_value empty_iff fst_conv insertE minimal_def)
    by (metis DomainE  fstI minimal_def singletonD)



lemma po_global_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>e}"
    and "g s \<in> {G, G\<^sub>3\<^sub>1}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv t1 (f s) s"
    and "prog_future_inv t2 (g s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv t1 (f s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp 
        apply(simp add: prog_future_inv_def prog_def)
  apply (metis dobs_RdA_pres not_pobs_RdA_pres)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L4")
       apply(simp add: prog_future_inv_def prog_def)
  
       apply (metis dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis DomainE fstI minimal_def singletonD)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp 
      apply(simp add: prog_future_inv_def prog_def)
  
  apply (metis dobs_RdA_pres not_pobs_RdA_pres)

  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp 
     apply(simp add: prog_future_inv_def prog_def)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L4")
    apply(simp add: prog_future_inv_def prog_def)
 
  apply (metis dobs_RdX_pres not_pobs_RdX_pres)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  apply(subgoal_tac "fst p = L4")
  apply(simp add: prog_future_inv_def prog_def)
  apply (smt (verit, ccfv_SIG) Domain.simps fst_conv insert_iff minimal_def singleton_iff)
  done

lemma G3130e: "futures \<Longrightarrow> G\<^sub>3\<^sub>1 = G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>0 = G\<^sub>e \<and> G\<^sub>3\<^sub>1 = G\<^sub>e"
  oops
lemma d_obs_diff_vals_contradiction:
   "[x =\<^sub>t u] \<sigma> \<Longrightarrow> [x =\<^sub>t' v] \<sigma> \<Longrightarrow> v \<noteq> u \<Longrightarrow> False"
  by (simp add: d_obs_def d_obs_t_def)

lemma po_global_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1}"
    and "g s \<in> {G, G\<^sub>3\<^sub>1, G\<^sub>e}"
    and "c \<in> f s"
    and "minimal p c"
    and "prog_future_inv t1 (f s) s"
    and "prog_future_inv t2 (g s) s"
    and "prog t1 (fst p) (snd p) s s'"
  shows "prog_future_inv t2 (g s') s'"
  using assms
  apply simp
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L1")
        apply(simp add: prog_future_inv_def prog_def)
  apply (metis not_p_obs_WrX_pres not_p_obs_implies_c_obs)
  apply (metis Domain.simps Pair_inject  minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L1")
       apply(simp add: prog_future_inv_def prog_def)
  apply(intro impI conjI)
        apply (smt (z3) PC.distinct(15) fst_conv insertI1 singleton_iff)
       apply(case_tac "G\<^sub>3\<^sub>1 = G"; simp)
  apply(elim conjE)
  apply (metis One_nat_def d_obs_diff_vals_contradiction zero_neq_one)
  apply (metis Domain_iff Pair_inject minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L1")
      apply(simp add: prog_future_inv_def prog_def)
       apply(case_tac "G\<^sub>e = G\<^sub>3\<^sub>1"; simp)

       apply (metis One_nat_def d_obs_diff_vals_contradiction zero_neq_one)
  apply (metis Domain.simps Pair_inject  minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L2")
     apply(simp add: prog_future_inv_def prog_def)
  apply (metis c_obs_WrR_intro)
  apply (metis Domain.simps Pair_inject minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
  apply (metis One_nat_def c_obs_WrR_intro dobs_WrR_pres)
  apply (metis Domain.simps Pair_inject  minimal_def prod.collapse singletonD)
  apply(subgoal_tac "fst p = L2")
   apply(simp add: prog_future_inv_def prog_def)
  apply (metis One_nat_def dobs_WrR_pres)
  by (metis Domain.simps fst_conv  minimal_def singletonD)



end
