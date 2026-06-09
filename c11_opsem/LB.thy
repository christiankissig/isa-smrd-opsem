theory LB
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

type_synonym C = "PC \<times> L \<times> V option"

record prog_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r1 :: V
  r2 :: V
  f ::  "(PC \<times> PC) set "
  g ::  "(PC \<times> PC) set "

consts F  :: "(PC \<times> PC) set "
consts F\<^sub>1 :: "(PC \<times> PC) set "
consts F\<^sub>e :: "(PC \<times> PC) set "
consts G  :: "(PC \<times> PC) set "
consts G\<^sub>3 :: "(PC \<times> PC) set "
consts G\<^sub>4 :: "(PC \<times> PC) set "
consts G\<^sub>e :: "(PC \<times> PC) set "




definition "futures    \<equiv>   F  = {(L1, L2)}
                         \<and> F\<^sub>1 = {(L2, L2)}
                         \<and> F\<^sub>e = {}
                         \<and> G = {(L3, L3), (L4, L4)}
                         \<and> G\<^sub>3 = {(L4, L4)}
                         \<and> G\<^sub>4 = {(L3, L3)}
                         \<and> G\<^sub>e = {}"

lemmas [simp] = futures_def thrdsvars_def

definition "members rel \<equiv> {a . a\<in>Domain rel \<or>  a\<in>Range rel} "

definition "rel_id S \<equiv> { e . fst e = snd e \<and> fst e \<in>members S}"

definition "minimal (p::PC) (s::(PC\<times>PC) set) \<equiv> \<forall> e . e \<in> s \<longrightarrow> p\<in>Domain s \<and> p\<notin>Range (s - rel_id s)"


lemma "futures \<Longrightarrow> minimal p G \<Longrightarrow> p \<in> {L3, L4}"
  apply simp
  apply(simp add: minimal_def rel_id_def)
  by (metis Domain_empty Domain_insert insertE insertI1 singleton_iff) 
  

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


definition prog :: "T \<Rightarrow> PC \<Rightarrow> prog_state \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog t p s s' \<equiv> 
(
  if t = t1
    then
      if p = L1
      then
        (state s) [r1 s' \<leftarrow> x]\<^sub>t (state s') \<and>
        r2 s = r2 s' \<and>
        f s' = F\<^sub>1 \<and> g s' = g s
  else
      if p = L2
      then
        (state s) [y := ((r1 s) + 1)]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s'   \<and>
         f s' = F\<^sub>e \<and> g s' = g s            
      else
        False
else
  if t = t2
    then
      if p = L3
        then
          (state s) [r2 s' \<leftarrow> y]\<^sub>t (state s')                 
          \<and> r1 s = r1 s' \<and> f s' = f s
          \<and> (g s = G \<longrightarrow> g s' = G\<^sub>3) \<and>  (g s = G\<^sub>4 \<longrightarrow> g s' = G\<^sub>e)

         
      else
        if p = L4
          then
            (state s) [x := 1]\<^sub>t (state s') \<and> r1 s = r1 s'  \<and> r2 s = r2 s'  \<and> f s' = f s 
            \<and> (g s = G \<longrightarrow> g s' = G\<^sub>4) \<and>  (g s = G\<^sub>3 \<longrightarrow> g s' = G\<^sub>e)
               
          else
            False
  else
    False
)"




definition prog_future_inv :: "(PC\<times>PC) set \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_future_inv p s \<equiv> 
  if p = F  then 

      [y =\<^sub>t2 0] (state s) \<and> r2 s = 0 \<and> (\<forall> i . i \<notin>{0,1} \<longrightarrow> \<not>[x \<approx>\<^sub>t1 i] (state s))

  else  if p = F\<^sub>1 then

      [y =\<^sub>t2 0] (state s) \<and> r2 s = 0 \<and> r1 s \<in> {0,1}

  else if p = F\<^sub>e  then

     r1 s \<noteq> 1 \<or> r2 s \<noteq> 1

  else if p = G then

     [x =\<^sub>t1 0] (state s) \<and> r1 s = 0

  else if p = G\<^sub>3 then

     [x =\<^sub>t1 0] (state s) \<and> r1 s = 0

  else if p = G\<^sub>4 then

     r1 s = 0 \<or> (r1 s = 1 \<and> (\<forall> i . i \<notin> {0,2} \<longrightarrow> \<not>[y \<approx>\<^sub>t2 i] (state s)))

  else if p = G\<^sub>e then
  
     r1 s \<noteq> 1 \<or> r2 s \<noteq> 1
 
  else  False
  "


lemma po_local_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1}"
    and "minimal p (f s)"
    and "prog_future_inv (f s) s"
    and "prog t1 p s s'"
  shows "prog_future_inv (f s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
    apply(subgoal_tac "p = L1")
     apply(simp add: prog_future_inv_def prog_def)
     apply(intro conjI impI)
  apply (metis PC.distinct(1) fst_conv singleton_iff)
  apply (meson not_pobs_RdX_pres)
  apply (metis  dobs_RdX_pres)
  apply (metis neqE not_less0 not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
  apply(subgoal_tac "p = L2")
     apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI impI)
  apply (metis insert_not_empty)
  apply presburger
  apply (metis insert_not_empty)
  apply (metis insert_not_empty)
  apply presburger
  apply (metis insert_not_empty)
       apply (metis insert_not_empty)
  apply presburger
  apply (metis insert_not_empty)
  apply (metis One_nat_def zero_neq_one)
   apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
  done

lemma po_global_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1}"
    and "g s \<in> {G, G\<^sub>3, G\<^sub>4}"
    and "minimal p (g s)"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t2 p s s'"
  shows "prog_future_inv (f s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
       apply(subgoal_tac "p\<in> {L3, L4}")
  apply clarsimp apply(elim disjE)
        apply(simp add: prog_future_inv_def prog_def)
         apply(case_tac "F = G"; simp)
  apply (metis d_obs_RdX_pres d_obs_read_value not_pobs_RdX_pres)
         apply(case_tac "F\<^sub>1 = G"; simp)
          apply (metis d_obs_RdX_pres d_obs_read_value not_pobs_RdX_pres)
  apply (metis d_obs_RdX_pres d_obs_read_value not_pobs_RdX_pres)
        apply(simp add: prog_future_inv_def prog_def)
        apply(case_tac "F = G"; simp)
  apply (metis d_obs_WrX_other not_p_obs_WrX_val_pres)
         apply(case_tac "F\<^sub>1 = G"; simp)
  apply (metis d_obs_WrX_other not_p_obs_WrX_val_pres)
  apply (metis d_obs_WrX_other not_p_obs_WrX_val_pres)
  using prog_def apply fastforce
       apply(subgoal_tac "p = L4", simp)
        apply(simp add: prog_future_inv_def prog_def)
  apply (metis d_obs_WrX_other not_p_obs_WrX_val_pres)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
       apply(subgoal_tac "p = L3", simp)
        apply(simp add: prog_future_inv_def prog_def)
  apply (metis d_obs_RdX_pres d_obs_read_value not_pobs_RdX_pres)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
         apply(subgoal_tac "p\<in> {L3, L4}")
  apply clarsimp apply(elim disjE)
        apply(simp add: prog_future_inv_def prog_def)
         apply(case_tac "F = F\<^sub>1"; simp)
  apply (metis d_obs_RdX_pres d_obs_read_value not_pobs_RdX_pres)
         apply(case_tac "F = G"; simp)
          apply (metis d_obs_RdX_pres d_obs_read_value)
  apply (metis d_obs_RdX_pres d_obs_read_value)
        apply(simp add: prog_future_inv_def prog_def)
         apply(case_tac "F = F\<^sub>1"; simp)
  apply (metis d_obs_WrX_other not_p_obs_WrX_val_pres)
         apply(case_tac "F = G"; simp)
  apply (metis d_obs_WrX_other)
  apply (metis d_obs_WrX_other)
  using prog_def apply fastforce
       apply(subgoal_tac "p = L4", simp)
        apply(simp add: prog_future_inv_def prog_def)
         apply(case_tac "F = F\<^sub>1"; case_tac " G\<^sub>3 = F\<^sub>1"; simp)
  apply (metis d_obs_WrX_other not_p_obs_WrX_val_pres)
  apply (metis PC.distinct(1) fst_conv the_elem_eq)
  apply (metis d_obs_WrX_other)
  apply (metis d_obs_WrX_other)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
  by (smt (verit) Domain_empty Domain_insert PC.distinct(1) d_obs_RdX_pres d_obs_read_value minimal_def prog_def prog_future_inv_def singleton_iff)



lemma po_local_t2:
  assumes "wfs (state s)"
    and "futures"
    and "thrdsvars"
    and "g s \<in> {G, G\<^sub>3, G\<^sub>4}"
    and "minimal p (g s)"
    and "prog_future_inv (g s) s"
    and "prog t2 p s s'"
  shows "prog_future_inv (g s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac " p \<in> {L3, L4}")
  apply clarsimp
  apply(elim disjE)
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI)
  apply (metis(mono_tags) insert_not_empty)+
  apply (metis(mono_tags) PC.distinct(11) fst_conv singleton_iff)+
  apply (metis(mono_tags) PC.distinct(5) fst_conv singleton_iff)+
  apply (metis  insertI1  singleton_iff)
  apply (metis(mono_tags))+
  apply simp_all
  apply (metis (mono_tags) insert_not_empty)+
  apply (metis(mono_tags) PC.distinct(11) fst_conv the_elem_eq)+
  apply (metis (mono_tags) PC.distinct(5) fst_conv the_elem_eq)+
  apply (metis dobs_RdX_pres insertI1 insert_not_empty singleton_iff)
  apply (metis (mono_tags) insertI1 insert_not_empty singleton_iff)+
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI)
  apply simp_all
  apply (metis(mono_tags) insert_not_empty)
  apply (metis(mono_tags) insert_not_empty)
  apply (metis(mono_tags) insert_not_empty)
  apply (metis(mono_tags) insert_not_empty)
  apply (metis(mono_tags) insert_not_empty)
  apply (metis(mono_tags))
  apply (metis(mono_tags))
  apply (metis(mono_tags))
  apply (metis(mono_tags))
  apply (metis(mono_tags))
  apply (metis(mono_tags))
  apply (metis(mono_tags) PC.distinct(11) fst_conv singleton_iff)+
  apply (metis(mono_tags) PC.distinct(5) fst_conv singleton_iff)+
  apply (metis insert_absorb2)
  apply (metis insert_absorb2)
  apply (metis(mono_tags) insert_not_empty)+
  apply (metis d_obs_WrX_other)
  apply blast
  apply blast
  apply (metis d_obs_WrX_other)
  apply (metis not_p_obs_WrX_val_pres)
  apply (metis Diff_insert_absorb insert_absorb insert_not_empty)
  apply (metis(mono_tags) insert_not_empty)+
  apply (metis (mono_tags) PC.distinct(9) fst_conv the_elem_eq)+
  apply (metis (mono_tags) PC.distinct(3) fst_conv the_elem_eq)+
  apply (metis insertI1 insert_not_empty singleton_iff)
  using prog_def apply fastforce
  apply(subgoal_tac "p = L4", simp)
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI)
  apply simp_all
  apply (metis (mono_tags) insert_not_empty)+
  apply clarsimp
  apply (metis One_nat_def zero_neq_one)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
  apply(subgoal_tac "p = L3", simp)
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI)
  apply simp_all
  apply (metis (mono_tags) insert_not_empty)+
  apply clarsimp
  apply(case_tac "G\<^sub>4 = F"; simp)
  apply (metis d_obs_read_value old.nat.distinct(2))
  apply (metis PC.distinct(9) Suc_1 empty_iff fst_conv insert_iff n_not_Suc_n not_pobs_RdX_pres p_obs_RdX_intro)
  by (metis Domain_empty Domain_insert minimal_def singleton_iff)

lemma po_global_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1}"
    and "g s \<in> {G, G\<^sub>3, G\<^sub>4}"
    and "minimal p (f s)"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t1 p s s'"
  shows "prog_future_inv (g s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
       apply(subgoal_tac "p = L1")
      apply(simp add: prog_future_inv_def prog_def)
        apply(case_tac "F = G"; case_tac "F\<^sub>1 = G"; simp)
           apply blast
  apply (metis dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis dobs_RdX_pres less_linear not_less_zero not_pobs_RdX_pres p_obs_RdX_intro)
  apply (metis d_obs_RdX_pres d_obs_read_value)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
  apply (smt (verit, del_insts) PC.distinct(11) PC.distinct(5) d_obs_RdX_pres d_obs_WrX_other d_obs_read_value fst_conv insert_not_empty prog_def prog_future_inv_def the_elem_eq)
      apply(simp add: prog_future_inv_def prog_def)
         apply(case_tac "F = G\<^sub>4"; case_tac "F\<^sub>1 = G"; simp)
  apply (metis PC.distinct(3) fst_conv the_elem_eq)
  apply (smt (z3) PC.distinct(3) old.prod.inject singleton_inject)
  apply(case_tac "G\<^sub>4 = G"; case_tac "p = L1"; simp)
  apply (metis PC.distinct(9) fst_conv the_elem_eq)
  apply (metis PC.distinct(9) fst_conv the_elem_eq)
  apply (metis insertE insertI1 insert_absorb)
      apply (smt (z3) insert_iff singleton_iff)
  apply(case_tac "G\<^sub>4 = F\<^sub>1"; case_tac "p = L1"; case_tac "p = L2"; simp)
  apply (metis PC.distinct(9) fst_conv the_elem_eq)
       apply (metis PC.distinct(9) fst_conv the_elem_eq)
  apply(case_tac "G\<^sub>4 = {}";case_tac "G\<^sub>4 = G"; case_tac "G\<^sub>4 = G\<^sub>3"; simp)
  apply (metis d_obs_RdX_pres d_obs_read_value)
  apply (metis Diff_insert_absorb insert_absorb insert_not_empty)
  apply (metis insert_absorb2)
  apply (metis d_obs_p_obs_agree neq0_conv not_pobs_RdX_pres p_obs_RdX_intro)
     apply(case_tac "G\<^sub>4 = {}";case_tac "G\<^sub>4 = G"; case_tac "G\<^sub>4 = G\<^sub>3"; simp)
        apply (meson d_obs_WrX_other)
  apply (meson d_obs_WrX_other)
  apply (meson d_obs_WrX_other)
  apply (metis not_p_obs_WrX_val_pres numeral_2_eq_2)
       apply(subgoal_tac "p = L2")
      apply(simp add: prog_future_inv_def prog_def)
     apply(case_tac "F = G"; case_tac "F\<^sub>1 = G"; simp)
  apply blast
  apply (metis Domain_empty Domain_insert Range_empty Range_insert the_elem_eq)
  apply (metis PC.distinct(9) Pair_inject insertE insertI1 insert_absorb insert_not_empty)
  apply (metis d_obs_WrX_other insert_not_empty)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
       apply(subgoal_tac "p = L2")
      apply(simp add: prog_future_inv_def prog_def)
     apply(case_tac "F = F\<^sub>1"; case_tac "F\<^sub>1 = F\<^sub>e"; case_tac "G\<^sub>3 = F\<^sub>1"; case_tac "G\<^sub>3 = {}"; simp)
       apply blast
  apply (metis d_obs_WrX_other)
  apply (metis PC.distinct(11) fst_conv the_elem_eq)
  apply (metis Pair_inject d_obs_WrX_other singleton_inject)
  apply (metis Domain_empty Domain_insert minimal_def singleton_iff)
         apply(subgoal_tac "p = L2")
      apply(simp add: prog_future_inv_def prog_def)
     apply(case_tac "F = F\<^sub>1"; case_tac "F\<^sub>1 = F\<^sub>e"; case_tac "G\<^sub>3 = F\<^sub>1"; case_tac "G\<^sub>3 = {}"; simp)
       apply blast
  apply (metis PC.distinct(1) fst_conv the_elem_eq)
  apply (metis PC.distinct(11) fst_conv the_elem_eq)
  apply (metis PC.distinct(15) PC.distinct(9) Pair_inject d_obs_p_obs_agree doubleton_eq_iff insert_absorb2 neq0_conv not_p_obs_WrX_val_pres numeral_2_eq_2)
  by (metis Domain_empty Domain_insert minimal_def singleton_iff)

end
