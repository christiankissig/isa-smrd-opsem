theory RNG
  imports  OpSem_Proof_Rules HOL.Transitive_Closure
begin
datatype PC =
  L1
| L2
| L3
| L4
| L5
| L6
| END1
| END2
| END3

consts t1 :: T 
consts t2 :: T
consts t3 :: T
consts x :: L
consts y :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and> t1 \<noteq> t3 \<and> t3 \<noteq> t2 \<and> x \<noteq> y"

type_synonym C = "PC \<times> V option"


record prog_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r1 :: V
  r2 :: V
  r3 :: V
  f ::  "((C \<times> C) set) set "
  g ::  "((C \<times> C) set) set "
  h ::  "((C \<times> C) set) set "

consts F  :: "((C \<times> C) set) set "
consts F\<^sub>1 :: "((C \<times> C) set) set "
consts F\<^sub>e :: "((C \<times> C) set) set "
consts G  :: "((C \<times> C) set) set "
consts G\<^sub>3 :: "((C \<times> C) set) set "
consts G\<^sub>e :: "((C \<times> C) set) set "
consts H  :: "((C \<times> C) set) set "
consts H\<^sub>5\<^sub>1\<^sub>0\<^sub>0  :: "((C \<times> C) set) set "
consts H\<^sub>5\<^sub>0  :: "((C \<times> C) set) set "
consts H\<^sub>5\<^sub>1  :: "((C \<times> C) set) set "
consts H\<^sub>e  :: "((C \<times> C) set) set "




definition "futures    \<equiv>   F  = {{((L1, None), (L2, None))}}
                         \<and> F\<^sub>1 = {{((L2, None), (L2, None))}}
                         \<and> F\<^sub>e = {{}}
                         \<and> G = {{((L3, None), (L4, None))}}
                         \<and> G\<^sub>3 = {{((L4, None), (L4, None))}}
                         \<and> G\<^sub>e = {{}}
                         \<and> H = {
                                {((L5, Some 0),(L5, Some 0))},
                                {((L5, Some 1),(L5, Some 1))}}
                         \<and> H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 = {{((L6, None), (L6, None))}}
                         \<and> H\<^sub>e = {{}} \<and> H\<^sub>5\<^sub>0 = H\<^sub>e \<and>  H\<^sub>5\<^sub>1 = H\<^sub>e"

lemmas [simp] = futures_def thrdsvars_def

definition "members s \<equiv> {a . a \<in> Domain s \<or> a \<in> Range s}"

definition "rel_id rel \<equiv> {(a1, a2) . a1 \<in> members rel \<and> a2 \<in> members rel \<and> a1 = a2} "

(*definition "relID S \<equiv> { e . fst e = snd e \<and> fst e \<in>members S}"

lemma "relID S = rel_id S"
  apply(simp add: relID_def rel_id_def)  by force*)

definition "minimal (p) (s) \<equiv> p\<in>Domain s \<and> p\<notin>Range (s - rel_id s)"


lemma Glp34: "futures \<Longrightarrow> c\<in>G \<Longrightarrow>  minimal p c \<Longrightarrow> fst p \<in> {L3, L4}"
  apply simp
  apply(simp add: minimal_def rel_id_def)
  by (metis (no_types, lifting) Domain_empty Domain_insert fst_conv singletonD)
  

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
        r2 s = r2 s' \<and> r3 s = r3 s'  \<and>
        f s' = F\<^sub>1 \<and> g s' = g s \<and> h s' = h s \<and> rv = Some (r1 s')
  else
      if p = L2
      then
        (state s) [y := ((r1 s) + 1)]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s' \<and> r3 s = r3 s'  
         \<and> f s' = F\<^sub>e \<and> g s' = g s \<and> h s' = h s \<and> rv = None
      else
        False
else
  if t = t2
    then
      if p = L3
        then
          (state s) [r2 s' \<leftarrow> y]\<^sub>t (state s')                 
          \<and> r1 s = r1 s' \<and> r3 s = r3 s'
          \<and> f s' = f s  \<and> h s' = h s \<and>  g s' = G\<^sub>3 \<and> rv = Some (r2 s')
      else
        if p = L4
          then
            (state s) [x := (r2 s)]\<^sub>t (state s')
            \<and> r1 s = r1 s'  \<and> r2 s = r2 s' \<and> r3 s = r3 s' 
            \<and> f s' = f s \<and> h s' = h s \<and> g s' = G\<^sub>e \<and> rv = Some (r2 s')
          else
            False
  else
      if t = t3
    then
      if p = L5
        then
            (state s) [r3 s' \<leftarrow> x]\<^sub>t (state s')                 
          \<and> r1 s = r1 s' \<and> r2 s = r2 s' 
          \<and> f s' = f s \<and>  g s' = g s \<and> rv = Some (r3 s')
          \<and> (r3 s' = 100 \<longrightarrow> h s' = H\<^sub>5\<^sub>1\<^sub>0\<^sub>0)
          \<and> (r3 s' = 0 \<longrightarrow> h s' = H\<^sub>5\<^sub>0) 
          \<and> (r3 s' = 1 \<longrightarrow> h s' = H\<^sub>5\<^sub>1) 
      else
        if p = L6
          then
            (state s) [x := 99]\<^sub>t (state s')
            \<and> r1 s = r1 s'  \<and> r2 s = r2 s'  \<and> r3 s = r3 s'  
            \<and> f s' = f s \<and> g s' = g s \<and> h s' = H\<^sub>e \<and> rv = None
          else
            False
else
False
)"



definition prog_future_inv :: "T \<Rightarrow> ((C \<times> C) set) set \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_future_inv t p s \<equiv> 
  if t = t1 \<and> p = F  then 

      [y =\<^sub>t2 0] (state s) \<and> [y =\<^sub>t3 0] (state s) \<and> r2 s = 0 \<and>
      (\<forall> i . i \<noteq> 0 \<longrightarrow> \<not>[x \<approx>\<^sub>t1 i] (state s))

  else  if t = t1 \<and> p = F\<^sub>1 then

      [y =\<^sub>t3 0] (state s) \<and> r1 s = 0

  else if t = t1 \<and> p = F\<^sub>e  then

      True

  else if t = t2 \<and> p = G then

     [x =\<^sub>t1 0] (state s) \<and> [x =\<^sub>t2 0] (state s) \<and> [x =\<^sub>t3 0] (state s) \<and>
     (\<forall> i . i \<notin>{0,1} \<longrightarrow> \<not>[y \<approx>\<^sub>t2 i] (state s))

  else if t = t2 \<and> p = G\<^sub>3 then

     [x =\<^sub>t1 0] (state s) \<and> [x =\<^sub>t2 0] (state s) \<and> [x =\<^sub>t3 0] (state s) \<and>
     r2 s \<in> {0, 1}

  else if t = t2 \<and> p = G\<^sub>e then
  
     True
 
  else if t = t3 \<and> p = H then

    \<not>[x \<approx>\<^sub>t1 99] (state s) \<and>
    \<not>[x \<approx>\<^sub>t2 99] (state s) \<and>
    \<not>[x \<approx>\<^sub>t3 99] (state s) \<and>
     (\<forall> i . i \<notin>{0,1} \<longrightarrow> \<not>[x \<approx>\<^sub>t3 i] (state s))

  else if t = t3 \<and> p = H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 then

        False

  else if t = t3 \<and> (p = H\<^sub>e \<or> p = H\<^sub>5\<^sub>1 \<or> p = H\<^sub>5\<^sub>0) then
  
      \<not>[x \<approx>\<^sub>t1 99] (state s) \<and>
      \<not>[x \<approx>\<^sub>t2 99] (state s) \<and>
      \<not>[x \<approx>\<^sub>t3 99] (state s)

else False"

lemma noteq[simp]: "futures \<Longrightarrow> F\<noteq>F\<^sub>1 \<and> F\<noteq>F\<^sub>e \<and> F\<^sub>1\<noteq>F\<^sub>e \<and>
  F\<^sub>1 \<noteq> G \<and> F\<^sub>e \<noteq> G \<and> H \<noteq> F\<^sub>e \<and> H \<noteq> G\<^sub>3 \<and>  H \<noteq> G\<^sub>e \<and>
  H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<noteq> H \<and> G \<noteq> F \<and> H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<noteq> G\<^sub>e  \<and> G\<^sub>e \<noteq> G\<^sub>3  \<and> G\<^sub>3 \<noteq> G \<and>
  H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<noteq> G\<^sub>3 \<and>  G\<^sub>3 \<noteq> F\<^sub>e \<and> G\<^sub>3 \<noteq> F\<^sub>1 \<and> H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<noteq> G \<and> H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<noteq> F\<^sub>1 \<and>
  H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<noteq> F \<and> H\<^sub>e \<noteq> H\<^sub>5\<^sub>1\<^sub>0\<^sub>0 \<and> H\<^sub>e \<noteq> H \<and> H \<noteq> G \<and> G \<noteq> F\<^sub>e \<and> F\<^sub>e \<noteq> F\<^sub>1 \<and>
  F\<^sub>1 \<noteq> F \<and> G\<^sub>e\<noteq> G \<and> G \<noteq> F\<^sub>1 \<and> H\<^sub>e \<noteq> G\<^sub>3 \<and> G\<^sub>3 \<noteq> F \<and>
  H\<^sub>e \<noteq> G \<and>  F\<^sub>e \<noteq> F \<and> H\<^sub>e \<noteq> F\<^sub>1 \<and> H\<^sub>e \<noteq> F \<and> H \<noteq> F \<and>
  F \<noteq> G \<and> F \<noteq> G\<^sub>3 \<and> F \<noteq> G\<^sub>e \<and> H \<noteq> F\<^sub>1"
  apply(simp)  
  apply clarify
  apply safe
  apply (metis PC.distinct(1) fst_conv the_elem_eq)
  apply (metis insert_not_empty singleton_inject)
  apply (metis insert_not_empty the_elem_eq PC.distinct(31) fst_conv pair_in_Id_conv the_elem_eq )+
                      apply auto[1] 
  apply (metis (no_types, lifting) PC.distinct(43) fst_conv insertCI singletonD)
  apply (metis empty_iff insert_iff)
  apply (metis (no_types, lifting) PC.distinct(53) fst_conv insertCI singletonD)
  apply (metis PC.distinct(3) fst_conv the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis empty_iff insert_iff)
  apply (metis PC.distinct(31) fst_conv the_elem_eq)
  apply (metis PC.distinct(45) fst_conv the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  apply (metis PC.distinct(19) fst_conv the_elem_eq)
  apply (metis PC.distinct(31) fst_conv pair_in_Id_conv the_elem_eq)
  apply (metis PC.distinct(23) fst_conv the_elem_eq)
  apply (metis PC.distinct(9) fst_conv the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  apply (metis empty_not_insert insertI1 singletonD)
  apply (metis PC.distinct(33) Pair_inject insertI1 singletonD)
  apply (metis empty_not_insert singleton_inject)
  apply (metis insert_not_empty singleton_inject)
  apply (metis PC.distinct(1) fst_conv the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  apply (metis PC.distinct(17) fst_conv the_elem_eq)
  apply (metis insert_not_empty singleton_inject)
  apply (metis PC.distinct(5) fst_conv the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  apply (metis insert_not_empty singleton_inject)
  apply (metis empty_not_insert the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  apply (metis PC.distinct(7) Pair_inject insertI1 singletonD)
  apply (metis (no_types, lifting) PC.distinct(3) Pair_inject singleton_inject)
  apply (metis PC.distinct(1) fst_conv pair_in_Id_conv the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  by (metis PC.distinct(21) Pair_inject insertI1 singletonD)


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
  apply simp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L1")
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI)
        apply (metis dobs_RdX_pres)
  apply (metis dobs_RdX_pres)
      apply (metis  not_pobs_RdX_pres)
  apply (metis dobs_RdX_pres)
  apply (metis less_linear not_less0 not_pobs_RdX_pres p_obs_RdX_intro)
  apply (metis DomainE fstI minimal_def singletonD)
  apply(subgoal_tac "fst p = L2", simp)
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis empty_not_insert singleton_inject)
  by (metis DomainE  fstI minimal_def singletonD)


lemma po_local_t2:
  assumes "wfs (state s)"
    and "futures"
    and "thrdsvars"
    and "g s \<in> {G, G\<^sub>3}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv t2 (g s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv t2 (g s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L3")
  apply clarsimp
  apply(simp add: prog_future_inv_def prog_def)
  apply(case_tac "G = F"; simp)
  apply (metis PC.distinct(3) fst_conv the_elem_eq)
  apply(case_tac "G = F\<^sub>1"; simp)
  using assms(2) noteq apply presburger
  apply(case_tac "G = F\<^sub>e"; simp)
  using assms(2) noteq apply presburger
    apply (metis  d_obs_RdX_other dobs_RdX_pres neq0_conv not_pobs_RdX_pres p_obs_RdX_intro)
  apply (metis Domain_iff fst_conv minimal_def singletonD)
  apply(subgoal_tac "fst p = L4")
  apply clarsimp
  apply(simp add: prog_future_inv_def prog_def) 
  apply(case_tac "G\<^sub>3 = F"; simp)
  apply (metis PC.distinct(5) fst_conv the_elem_eq)
  apply(case_tac "G\<^sub>3 = F\<^sub>1"; simp)
  apply (metis PC.distinct(19) fst_conv the_elem_eq)
  apply(case_tac "G\<^sub>3 = F\<^sub>e"; simp)
  apply (metis empty_iff insert_iff)
  by (metis Domain_iff fst_conv minimal_def singletonD)


lemma po_local_t3:
  assumes "wfs (state s)"
    and "futures"
    and "thrdsvars"
    and "h s \<in> {H, H\<^sub>5\<^sub>1\<^sub>0\<^sub>0}"
    and "c \<in> h s"
    and "minimal p c"
    and "prog_future_inv t3 (h s) s"
    and "prog t3 (fst p) (snd p) s s'"
  shows "prog_future_inv t3 (h s') s'"
  using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
  apply (metis less_nat_zero_code not_less_iff_gr_or_eq not_pobs_RdX_pres p_obs_RdX_intro)
   apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    apply(simp add: prog_future_inv_def prog_def)
  done


lemma po_global_t1_against_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>e}"
    and "g s \<in> {G, G\<^sub>3}"
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
    apply(intro conjI)
    apply (metis d_obs_RdX_pres)
    apply (metis dobs_RdX_pres)  
    apply(elim conjE)
    apply (metis d_obs_read_value)
        apply (metis not_pobs_RdX_pres)
       apply (metis DomainE  fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L4")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis d_obs_WrX_other)
    apply (metis dobs_WrX_pres)
    apply(elim conjE disjE)
    apply (metis less_numeral_extra(3) not_p_obs_WrX_val_pres)
       apply (metis DomainE  fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L3")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply (metis dobs_RdX_pres)
       apply (metis DomainE  fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L3")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
       apply (metis DomainE  fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L4")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply (metis dobs_WrX_pres)
       apply (metis DomainE  fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L4")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
       apply (metis DomainE  fstI minimal_def singletonD)
  done


lemma po_global_t1_against_t3:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>e}"
    and "h s \<in> {H, H\<^sub>5\<^sub>1\<^sub>0\<^sub>0}"
    and "c \<in> h s"
    and "minimal p c"
    and "prog_future_inv t1 (f s) s"
    and "prog_future_inv t3 (h s) s"
    and "prog t3 (fst p) (snd p) s s'"
  shows "prog_future_inv t1 (f s') s'"
  using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
        apply (metis d_obs_RdX_other dobs_RdX_pres not_pobs_RdX_pres)
       apply (smt (z3) Domain_iff Pair_inject insertE minimal_def prod.collapse singleton_iff) 
    apply(subgoal_tac "fst p = L6")
       apply(simp add: prog_future_inv_def prog_def)
  apply (metis DomainE fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
    apply (metis d_obs_RdX_other)
  apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
     apply(subgoal_tac "fst p = L5")
     apply(simp add: prog_future_inv_def prog_def)
    apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)  
   apply(subgoal_tac "fst p = L6")
    apply(simp add: prog_future_inv_def prog_def)  
  apply (metis DomainE fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L6")
    apply(simp add: prog_future_inv_def prog_def)
   apply (metis DomainE fstI minimal_def singletonD)
    done


lemma po_global_t2_against_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1}"
    and "g s \<in> {G, G\<^sub>3, G\<^sub>e}"
    and "c \<in> f s"
    and "minimal p c"
    and "prog_future_inv t1 (f s) s"
    and "prog_future_inv t2 (g s) s"
    and "prog t1 (fst p) (snd p) s s'"
  shows "prog_future_inv t2 (g s') s'"
    using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L1")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis d_obs_RdX_pres)
    apply (metis dobs_RdX_pres)  
    apply(elim conjE)
    apply (metis dobs_RdX_pres)
          apply (metis not_pobs_RdX_pres)
    apply (metis Domain_empty Domain_insert empty_iff fst_conv insert_iff minimal_def)
    apply(subgoal_tac "fst p = L1")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis d_obs_RdX_pres)
    apply (metis dobs_RdX_pres)
    apply (metis dobs_RdX_pres)
    apply (metis DomainE fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L1")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
       apply (metis DomainE fstI minimal_def singletonD)   
    apply(subgoal_tac "fst p = L2")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def) 
       apply (metis d_obs_WrX_other dobs_WrX_pres not_p_obs_WrX_val_pres)
    apply (metis DomainE  fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L2")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def) 
      apply (metis d_obs_WrX_other dobs_WrX_pres)
    apply (metis DomainE  fstI minimal_def singletonD)
    apply(simp add: prog_future_inv_def prog_def) 
    by (metis (no_types, lifting))




lemma po_global_t2_against_t3:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "h s \<in> {H, H\<^sub>5\<^sub>1\<^sub>0\<^sub>0}"
    and "g s \<in> {G, G\<^sub>3, G\<^sub>e}"
    and "c \<in> h s"
    and "minimal p c"
    and "prog_future_inv t2 (g s) s"
    and "prog_future_inv t3 (h s) s"
    and "prog t3 (fst p) (snd p) s s'"
  shows "prog_future_inv t2 (g s') s'"
  using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis dobs_RdX_pres)
    apply (metis dobs_RdX_pres)
    apply (metis d_obs_RdX_pres)
        apply (metis not_pobs_RdX_pres)
  apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis dobs_RdX_pres)
    apply (metis dobs_RdX_pres)
    apply (metis d_obs_RdX_pres)
  apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
  apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    apply(subgoal_tac "fst p = L6")
    apply(simp add: prog_future_inv_def prog_def)
   apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    apply(subgoal_tac "fst p = L6")
    apply(simp add: prog_future_inv_def prog_def)
   apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    apply(subgoal_tac "fst p = L6")
    apply(simp add: prog_future_inv_def prog_def)
  apply (smt (z3) Domain_iff fst_conv insertE minimal_def singleton_iff)
    done
    
    
    lemma po_global_t3_against_t1:
    assumes "wfs (state s)"
        and "thrdsvars"
        and "futures"
        and "f s \<in> {F, F\<^sub>1}"
        and "h s \<in> {H, H\<^sub>5\<^sub>1\<^sub>0\<^sub>0, H\<^sub>e}"
        and "c \<in> f s"
        and "minimal p c"
        and "prog_future_inv t1 (f s) s"
        and "prog_future_inv t3 (h s) s"
        and "prog t1 (fst p) (snd p) s s'"
      shows "prog_future_inv t3 (h s') s'"
  using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L1")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis not_pobs_RdX_pres zero_less_numeral)
    apply (metis not_pobs_RdX_pres)
    apply (metis not_pobs_RdX_pres)
        apply (metis not_pobs_RdX_pres)
  apply (metis DomainE fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L1")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
      apply (metis DomainE fstI minimal_def singletonD)  
     apply(subgoal_tac "fst p = L1")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
      apply (metis not_pobs_RdX_pres zero_less_numeral)
  apply (metis DomainE fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
     apply (metis not_p_obs_WrX_diff_var_pres)
  apply (metis Domain_empty Domain_insert empty_iff fst_conv insertE minimal_def)
    apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
  apply (metis DomainE fstI minimal_def singletonD)
    apply(subgoal_tac "fst p = L2")
    apply(simp add: prog_future_inv_def prog_def)
   apply (metis not_p_obs_WrX_diff_var_pres)
  by (metis Domain_iff fst_conv minimal_def singletonD)




lemma po_global_t3_against_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "h s \<in> {H, H\<^sub>5\<^sub>1\<^sub>0\<^sub>0, H\<^sub>e}"
    and "g s \<in> {G, G\<^sub>3}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv t2 (g s) s"
    and "prog_future_inv t3 (h s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv t3 (h s') s'"
  using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L3")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis not_pobs_RdX_pres)
    apply (metis not_pobs_RdX_pres)
    apply (metis not_pobs_RdX_pres)
        apply (metis not_pobs_RdX_pres)
       apply (metis Domain_iff fst_conv minimal_def singletonD)  
      apply(subgoal_tac "fst p = L4")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis not_p_obs_WrX_val_pres numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(84) zero_neq_numeral)
    apply (metis not_p_obs_WrX_val_pres numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(84) zero_neq_numeral)
    apply (metis not_p_obs_WrX_val_pres numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(84) zero_neq_numeral)
    apply (metis less_le not_p_obs_WrX_val_pres)
       apply (metis Domain_iff fst_conv minimal_def singletonD)  
    apply(subgoal_tac "fst p = L3")
    apply(simp add: prog_future_inv_def prog_def)
       apply (metis Domain_iff fst_conv minimal_def singletonD)  
    apply(subgoal_tac "fst p = L3")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI)
    apply (metis not_pobs_RdX_pres)
    apply (metis not_pobs_RdX_pres)
    apply (metis not_pobs_RdX_pres)
       apply (metis Domain_iff fst_conv minimal_def singletonD)  
    apply(subgoal_tac "fst p = L4")
    apply(simp add: prog_future_inv_def prog_def)
  apply (metis DomainE fstI minimal_def singletonD)
    apply(simp add: prog_future_inv_def prog_def)
    by (metis (no_types, lifting) not_p_obs_WrX_val_pres not_pobs_RdX_pres numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(84) zero_neq_numeral)

end
