theory LBDataAddCtrl
  imports  OpSem_Proof_Rules HOL.Transitive_Closure
begin
datatype PC =
  L1
| L2
| L3
| L4
| L5
| L6
| L7
| END1
| END2

consts t1 :: T 
consts t2 :: T
consts x :: L
consts y :: L
consts z :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and> x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z"

type_synonym C = "PC \<times> V option"

record prog_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r1 :: V
  r2 :: V
  r3 :: V
  r4 :: V
  f ::  "((C \<times> C) set) set "
  g ::  "((C \<times> C) set) set "

consts F  :: "((C \<times> C) set) set "
consts F\<^sub>1 :: "((C \<times> C) set) set "
consts F\<^sub>2 :: "((C \<times> C) set) set "
consts F\<^sub>3 :: "((C \<times> C) set) set "
consts F\<^sub>4 :: "((C \<times> C) set) set "
consts F\<^sub>e :: "((C \<times> C) set) set "
consts G  :: "((C \<times> C) set) set "
consts G\<^sub>6\<^sub>2 :: "((C \<times> C) set) set "
consts G\<^sub>6\<^sub>1 :: "((C \<times> C) set) set "
consts G\<^sub>6\<^sub>0 :: "((C \<times> C) set) set "
consts G\<^sub>e :: "((C \<times> C) set) set "




definition "futures    \<equiv>   F  = {{((L1, None), (L2, None)),((L2, None), (L3, None)),((L3, None), (L4, None)),((L4, None), (L5, None))}}
                         \<and> F\<^sub>1 = {{((L2, None), (L3, None)),((L3, None), (L4, None)),((L4, None), (L5, None))}}
                         \<and> F\<^sub>2 = {{((L3, None), (L4, None)),((L4, None), (L5, None))}}
                         \<and> F\<^sub>3 = {{((L4, None), (L5, None))}}
                         \<and> F\<^sub>4 = {{((L5, None), (L5, None))}}
                         \<and> F\<^sub>e = {{((END1, None), (END1, None))}}
                         \<and> G = {{((L6, Some 0), (L6, Some 0))}, {((L6, Some 1), (L6, Some 1))}}
                         \<and> G\<^sub>6\<^sub>2 = {{((L7, None), (L7, None))}} 
                         \<and> G\<^sub>e = {{((END2, None), (END2, None))}} \<and> G\<^sub>6\<^sub>0 = G\<^sub>e \<and> G\<^sub>6\<^sub>1 = G\<^sub>e"

lemmas [simp] =  thrdsvars_def

definition "members s \<equiv> {a . a \<in> Domain s \<or> a \<in> Range s}"

definition "rel_id rel \<equiv> {(a1, a2) . a1 \<in> members rel \<and> a2 \<in> members rel \<and> a1 = a2} "

definition "minimal (p) (s) \<equiv> p\<in>Domain s \<and> p\<notin>Range (s - rel_id s)"

lemma "\<forall> e . e\<in>rel_id s \<longrightarrow> fst e = snd e"
  apply(simp add: rel_id_def members_def)
  done

lemma p_not_in_Range: "c - rel_id c = c \<Longrightarrow> minimal p c \<Longrightarrow> p \<notin> Range c"
  apply(simp add: minimal_def )
  done

lemma pL1:"futures \<Longrightarrow> c\<in>F \<Longrightarrow>  minimal p c \<Longrightarrow>  p = (L1, None)"
  apply(subgoal_tac "c = {((L1, None), L2, None), ((L2, None), L3, None),
      ((L3, None), L4, None), ((L4, None), L5, None)}")
  defer  apply(simp add: futures_def)
  apply(elim conjE)
   apply (smt (z3) singletonD)
  apply(subgoal_tac "c - rel_id c = c") defer
  apply(simp add: rel_id_def members_def) apply safe
  by (metis Domain_empty Domain_insert Range_empty Range_insert insert_iff minimal_def)

lemma pL2:"futures \<Longrightarrow> c\<in>F\<^sub>1 \<Longrightarrow>  minimal p c \<Longrightarrow> p = (L2,None)"
  apply(subgoal_tac "c = { ((L2, None), L3, None),
      ((L3, None), L4, None), ((L4, None), L5, None)}")
  defer  apply(simp add: futures_def)
  apply(elim conjE)
   apply (smt (z3) singletonD)
  apply(subgoal_tac "c - rel_id c = c") defer
  apply(simp add: rel_id_def members_def) apply safe
  by (metis Domain_empty Domain_insert Range_empty Range_insert insert_iff minimal_def)

lemma pL3:"futures \<Longrightarrow>c\<in>F\<^sub>2 \<Longrightarrow> minimal p c \<Longrightarrow> p = (L3, None)"
  apply(subgoal_tac "c = {((L3, None), L4, None), ((L4, None), L5, None)}")
  defer  apply(simp add: futures_def)
  apply(elim conjE)
   apply (smt (z3) singletonD)
  apply(subgoal_tac "c - rel_id c = c") defer
  apply(simp add: rel_id_def members_def) apply safe
  by (metis Domain_empty Domain_insert Range_empty Range_insert insert_iff minimal_def)

lemma pL4: "futures \<Longrightarrow> c\<in>F\<^sub>3 \<Longrightarrow>  minimal p c \<Longrightarrow> p = (L4, None)"
  apply(subgoal_tac "c = { ((L4, None), L5, None)}")
  defer  apply(simp add: futures_def)
  apply(elim conjE)
   apply (smt (z3) singletonD)
  apply(subgoal_tac "c - rel_id c = c") defer
  apply(simp add: rel_id_def members_def) apply safe
  by (metis Domain_empty Domain_insert Range_empty Range_insert insert_iff minimal_def)

lemma pL5: "futures \<Longrightarrow> c\<in>F\<^sub>4 \<Longrightarrow> minimal p c \<Longrightarrow> p = (L5, None)"
  apply(subgoal_tac "c = { ((L5, None), L5, None)}")
  defer  apply(simp add: futures_def)
  apply(elim conjE)
   apply (smt (z3) singletonD)
  by (simp add: minimal_def)



lemma pL6: "futures \<Longrightarrow>c\<in>G \<Longrightarrow> minimal p c \<Longrightarrow> fst p = L6"
  apply(simp add:futures_def minimal_def rel_id_def)
  by (smt (z3) Domain_empty Domain_insert fst_conv insert_iff singletonD)

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
        r3 s = r3 s' \<and>
        r4 s = r4 s' \<and>
        f s' = F\<^sub>1 \<and> g s' = g s \<and> rv = Some (r1 s')
  else
      if p = L2
      then
           r2 s' = r1 s \<and> r4 s = r4 s' 
         \<and> r1 s = r1 s' \<and> r3 s = r3 s'   
         \<and> f s' = F\<^sub>2 \<and> g s' = g s \<and> state s = state s' \<and> rv = None         
      else
      if p = L3
      then
        (state s) [y := r2 s]\<^sub>t (state s') 
         \<and> r4 s = r4 s' \<and> r1 s = r1 s' \<and> r2 s = r2 s' \<and> r3 s = r3 s'   
         \<and> f s' = F\<^sub>3 \<and> g s' = g s \<and> rv = None        
      else
      if p = L4
      then
        (state s) [r3 s' \<leftarrow> y]\<^sub>t (state s') 
         \<and> r1 s = r1 s' \<and> r2 s = r2 s' \<and> r4 s' = r4 s 
         \<and> f s' = F\<^sub>4 \<and> g s' = g s \<and> rv = Some (r3 s')            
      else
      if p = L5
      then
        (state s) [z := ((r3 s) + 1)]\<^sub>t (state s') 
         \<and> r1 s = r1 s' \<and> r2 s = r2 s' \<and> r3 s = r3 s' \<and> r4 s = r4 s'  
         \<and> f s' = F\<^sub>e \<and> g s' = g s \<and> rv = None            
      else
        False
else
  if t = t2
    then
      if p = L6
        then
          (state s) [r4 s' \<leftarrow> z]\<^sub>t (state s')                 
          \<and> r1 s = r1 s' \<and> r2 s = r2 s' 
          \<and> r3 s = r3 s' \<and>  f s' = f s
          \<and> (r4 s' = 2 \<longrightarrow> g s' = G\<^sub>6\<^sub>2) 
          \<and> (r4 s' \<noteq> 2 \<longrightarrow> g s' = G\<^sub>e) \<and> rv = Some (r4 s') 

      else
        if p = L7
          then
            (state s) [x := 1]\<^sub>t (state s') 
            \<and> r1 s = r1 s' \<and> r2 s = r2 s'  
            \<and> f s' = f s 
            \<and> g s' = G\<^sub>e \<and> rv = None
               
          else
            False
  else
    False
)"




definition prog_future_inv :: "((C \<times> C) set) set \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_future_inv p s \<equiv> 
  if p = F  then 

      [y =\<^sub>t1 0] (state s) \<and> [z =\<^sub>t2 0] (state s)
      \<and> (\<forall> i . i\<noteq>0 \<longrightarrow> \<not>[x \<approx>\<^sub>t1 i] (state s))

  else  if p = F\<^sub>1 then

     [y =\<^sub>t1 0] (state s) \<and> [z =\<^sub>t2 0] (state s) \<and>
     r1 s = 0

  else  if p = F\<^sub>2 then

     [y =\<^sub>t1 0] (state s) \<and> [z =\<^sub>t2 0] (state s) \<and>
     r2 s = 0

  else  if p = F\<^sub>3 then

      [y =\<^sub>t1 0] (state s) \<and> [z =\<^sub>t2 0] (state s)

  else  if p = F\<^sub>4 then

     [z =\<^sub>t2 0] (state s) \<and> r3 s = 0

  else if p = F\<^sub>e  then

     r3 s = 0

  else if p = G then

     (\<forall> i . i \<notin> {0,1} \<longrightarrow> \<not>[z \<approx>\<^sub>t2 i] (state s))

  else if p = G\<^sub>6\<^sub>2 then

     False

  else if p = G\<^sub>e then
  
     r4 s \<in> {0,1}
 
  else  False
  "



lemma noteq[simp]: "futures \<Longrightarrow> F\<noteq>F\<^sub>1 \<and> F\<noteq>F\<^sub>e \<and> F\<^sub>1\<noteq>F\<^sub>e \<and>
 F\<^sub>1 \<noteq> G \<and> F\<^sub>e \<noteq> G \<and> G \<noteq> F \<and>
  G \<noteq> F\<^sub>e \<and> F\<^sub>e \<noteq> F\<^sub>1 \<and> F\<^sub>1 \<noteq> F 
 \<and> G\<^sub>e\<noteq> G \<and> G \<noteq> F\<^sub>1 \<and> F\<^sub>e \<noteq> F \<and> F\<^sub>2 \<noteq> F\<^sub>1 \<and> F\<^sub>2 \<noteq> F \<and> F\<^sub>4 \<noteq> F\<^sub>3 \<and> F\<^sub>3 \<noteq> F\<^sub>2 \<and> F\<^sub>4 \<noteq> F\<^sub>2
\<and> F\<^sub>4 \<noteq> F\<^sub>1 \<and>  F\<^sub>4 \<noteq> F \<and> F\<^sub>e \<noteq> F\<^sub>4 \<and> F\<^sub>e \<noteq> F\<^sub>3 \<and> F\<^sub>e \<noteq> F\<^sub>2 \<and>
G\<^sub>e \<noteq> G\<^sub>6\<^sub>2 \<and> G\<^sub>6\<^sub>2 \<noteq> G \<and> G \<noteq> F\<^sub>4 \<and> G\<^sub>e \<noteq> F\<^sub>e \<and> G\<^sub>e \<noteq> F\<^sub>4 \<and> G\<^sub>e \<noteq> F\<^sub>3 \<and> G\<^sub>e \<noteq> F\<^sub>2 \<and> G\<^sub>e \<noteq> F\<^sub>1 \<and> G\<^sub>e \<noteq> F 
\<and> G\<^sub>6\<^sub>2 \<noteq> F\<^sub>e \<and> G\<^sub>6\<^sub>2 \<noteq> F\<^sub>4 \<and> G\<^sub>6\<^sub>2 \<noteq> F\<^sub>3\<and> G\<^sub>6\<^sub>2 \<noteq> F\<^sub>2 \<and> G\<^sub>6\<^sub>2 \<noteq> F\<^sub>1 \<and> G\<^sub>6\<^sub>2 \<noteq> F \<and>  G \<noteq> F\<^sub>3 \<and> G \<noteq> F\<^sub>2 \<and> F \<noteq> F\<^sub>3 \<and>
F\<^sub>3 \<noteq> F "
  apply(simp add: futures_def)
  apply (intro conjI)
  apply (smt (verit, ccfv_SIG) PC.distinct(3) PC.distinct(5) fst_conv insert_iff singleton_iff snd_conv)
  apply (smt (verit, ccfv_threshold) PC.distinct(13) Pair_inject insert_absorb insert_iff insert_not_empty singleton_inject)
  apply (smt (verit, ccfv_threshold) PC.distinct(39) Pair_inject insert_absorb insert_iff singleton_inject)
  apply (smt (verit) One_nat_def Pair_inject insert_absorb insert_eq_iff insert_not_empty option.inject singletonD zero_neq_one)
  apply (metis insertI1 option.distinct(1) singletonD snd_conv)
  apply (smt (verit) One_nat_def Pair_inject insert_absorb insert_eq_iff insert_not_empty option.inject singletonD zero_neq_one)
  apply (metis insertI1 option.distinct(1) singletonD snd_conv)
  apply (smt (verit, ccfv_SIG) PC.distinct(27) fst_conv insertCI singletonD)
  apply (smt (verit, del_insts) Domain_empty Domain_insert PC.distinct(1) PC.distinct(3) PC.distinct(5) insert_iff singletonD)
  apply (metis (no_types, lifting) PC.distinct(65) fst_conv insertCI singletonD)
  apply (smt (verit, ccfv_threshold) insertI1 option.distinct(1) singletonD snd_conv)
  apply (smt (verit, best) PC.distinct(27) fst_conv insertI1 singletonD snd_conv)
  apply (smt (verit) PC.distinct(31) PC.distinct(33) Pair_inject insertCI insertE singletonD)
  apply (smt (verit, ccfv_SIG) PC.distinct(3) Pair_inject insertCI insertE singletonD)
  apply (metis PC.distinct(43) fst_conv the_elem_eq)
  apply (metis PC.distinct(44) Pair_inject insertI1 singletonD)
  apply (smt (verit, best) PC.distinct(34) Pair_inject insertI1 singletonD)
  apply (smt (verit) PC.distinct(34) Pair_inject insertI1 singletonD)
  apply (smt (verit, ccfv_SIG) PC.distinct(1) fst_conv insertCI singletonD)
  apply (metis PC.distinct(57) Pair_inject singleton_inject)
  apply (metis PC.distinct(43) Pair_inject singleton_inject)
  apply (metis PC.distinct(49) Pair_inject insertI1 singletonD)
  apply (metis PC.distinct(69) Pair_inject singleton_inject)
  apply (metis insertI1 option.distinct(1) singletonD snd_conv)
  apply (metis insertI1 option.distinct(1) singletonD snd_conv)
  apply (metis PC.distinct(71) fst_conv the_elem_eq)
  apply (metis PC.distinct(59) Pair_inject singleton_inject)
  apply (metis PC.distinct(51) fst_conv the_elem_eq)
  apply (metis PC.distinct(52) Pair_inject insertI1 singletonD)
  apply (smt (verit, best) PC.distinct(41) Pair_inject insertI1 singletonD)
  apply (smt (verit, ccfv_SIG) PC.distinct(15) fst_conv insertI1 singletonD)
  apply (metis PC.distinct(67) fst_conv the_elem_eq)
  apply (metis PC.distinct(55) fst_conv the_elem_eq)
  apply (metis PC.distinct(47) fst_conv the_elem_eq)
  apply (metis PC.distinct(47) Pair_inject insertI1 singletonD)
  apply (metis (no_types, opaque_lifting) PC.distinct(18) fst_conv insertI1 pair_in_Id_conv singletonD)
  apply (smt (verit, ccfv_SIG) PC.distinct(1) fst_conv insertCI singletonD)
  apply (metis (no_types, lifting) PC.distinct(43) fst_conv insertCI singletonD snd_conv)
  apply (smt (verit) One_nat_def Pair_inject insert_absorb insert_eq_iff insert_not_empty option.inject singletonD zero_neq_one)
  apply (smt (verit, ccfv_SIG) PC.distinct(21) fst_conv insertCI singletonD snd_conv)
  by (smt (z3) PC.distinct(43) Pair_inject doubleton_eq_iff insert_absorb2 insert_commute)


  lemma po_local_t1:
    assumes "wfs (state s)"
      and "thrdsvars"
      and "futures"
      and "f s \<in> {F, F\<^sub>1, F\<^sub>2, F\<^sub>3, F\<^sub>4}"
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
    apply (metis d_obs_RdX_other dobs_RdX_pres less_linear less_nat_zero_code not_pobs_RdX_pres p_obs_RdX_intro)
    apply (metis fstI pL1)
        apply(subgoal_tac "fst p = L2")
         apply(simp add: prog_future_inv_def prog_def)
    apply (metis fstI pL2)
       apply(subgoal_tac "fst p = L3")
       apply(simp add: prog_future_inv_def prog_def)
    apply (smt (z3) PC.distinct(19) Pair_inject d_obs_WrX_set dobs_WrX_pres futures_def insertI1 singletonD)
    apply (metis fstI pL3)
    apply(subgoal_tac "fst p = L4")
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI impI)   
    apply (metis dobs_RdX_pres)
      apply (meson d_obs_read_value)
    apply (metis fstI pL4)
    apply (simp add: pL4)
    apply(subgoal_tac "fst p = L5")
    apply(simp add: prog_future_inv_def prog_def)
    using pL5 by fastforce



  lemma po_local_t2:
  assumes "wfs (state s)"
      and "futures"
      and "thrdsvars"
      and "g s \<in> {G, G\<^sub>6\<^sub>2}"
      and "c \<in> g s"
      and "minimal p c"
      and "prog_future_inv (g s) s"
      and "prog t2 (fst p) (snd p) s s'"
    shows "prog_future_inv (g s') s'"
    using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac " fst p  = L6")
    apply clarsimp
    apply(simp add: prog_future_inv_def prog_def)
    apply(intro conjI impI)
    apply simp_all
    apply(case_tac "G = F\<^sub>2";case_tac "G = F\<^sub>3"; simp)
    apply (metis neq0_conv not_pobs_RdX_pres p_obs_RdX_intro)
    apply(case_tac "G = F\<^sub>2";simp)
    apply (elim conjE, simp)
    apply(case_tac "G = F\<^sub>3";simp)
      apply (metis less_2_cases_iff n_not_Suc_n not_pobs_RdX_pres numeral_2_eq_2 p_obs_RdX_intro)
    using pL6 apply blast
    using prog_future_inv_def by auto



lemma po_global_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in>  {F, F\<^sub>1, F\<^sub>2, F\<^sub>3, F\<^sub>4, F\<^sub>e}"
    and "g s \<in> {G, G\<^sub>6\<^sub>2}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv (f s') s'"
  using assms
    apply clarsimp
    apply(elim disjE)
    apply(subgoal_tac "fst p = L6")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
              apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
    using pL6 apply blast
    using prog_future_inv_def apply auto[1]
    apply(subgoal_tac "fst p = L6")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(case_tac "G = F\<^sub>2"; simp)
              apply (metis d_obs_RdX_pres dobs_RdX_pres)
    using pL6 apply blast
    apply(subgoal_tac "fst p = L6")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(case_tac "G = F\<^sub>2"; simp)
           apply (metis d_obs_RdX_pres dobs_RdX_pres)
    using pL6 apply blast
    apply(subgoal_tac "fst p = L6")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(case_tac "F = F\<^sub>3"; case_tac "F\<^sub>3 = F\<^sub>1"; simp)
    apply (metis d_obs_RdX_pres dobs_RdX_pres)
    apply (metis  d_obs_RdX_pres dobs_RdX_pres)
    using pL6 apply blast
    apply(subgoal_tac "fst p = L6")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    apply(case_tac "F = F\<^sub>3"; case_tac "F\<^sub>3 = F\<^sub>1"; simp)
    apply (metis d_obs_RdX_pres )
    apply (metis  d_obs_RdX_pres)
    using pL6 apply blast
    apply(subgoal_tac "fst p = L6")
    apply clarsimp 
    apply(simp add: prog_future_inv_def prog_def)
    using pL6 apply blast
    using prog_future_inv_def apply force
    using prog_future_inv_def apply force
    using prog_future_inv_def apply force
    using prog_future_inv_def apply force
    using prog_future_inv_def apply force
    done


lemma po_global_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in>  {F, F\<^sub>1, F\<^sub>2, F\<^sub>3, F\<^sub>4}"
    and "g s \<in> {G, G\<^sub>6\<^sub>2, G\<^sub>e}"
    and "c \<in> f s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t1 (fst p) (snd p) s s'"
  shows "prog_future_inv (g s') s'"
  using assms
  apply clarsimp
  apply(elim disjE)
  apply(subgoal_tac "fst p = L1")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis Suc_neq_Zero d_obs_p_obs_agree gr0_implies_Suc not_pobs_RdX_pres)
  apply (metis fstI pL1)
  apply(subgoal_tac "fst p = L1")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis fstI pL1)
  apply(subgoal_tac "fst p = L1")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis fstI pL1)
  apply(subgoal_tac "fst p = L2")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis fstI pL2)
  apply(subgoal_tac "fst p = L3")
  apply(simp add: prog_future_inv_def prog_def)
  apply (metis not_p_obs_WrX_pres)
  apply (metis fstI pL3)
  apply(subgoal_tac "fst p = L4")
  apply(simp add: prog_future_inv_def prog_def) 
  apply(case_tac "F\<^sub>3 = F"; simp)
  apply (metis not_pobs_RdX_pres)
  apply (metis fstI pL4)
  apply(subgoal_tac "fst p = L5")
  apply(simp add: prog_future_inv_def prog_def) 
  apply (metis not_p_obs_WrX_val_pres)
  apply (metis fstI pL5)
  apply (simp add: prog_future_inv_def)
  apply (simp add: prog_future_inv_def)
  apply (smt (verit, del_insts) prog_def)  
  using prog_future_inv_def apply auto[1]
  using prog_future_inv_def apply auto[1]
  using prog_future_inv_def apply force
  apply (simp add: prog_future_inv_def prog_def)
  apply presburger
  apply (simp add: prog_future_inv_def prog_def)
  apply presburger
  apply (simp add: prog_future_inv_def prog_def)
  by presburger

end
