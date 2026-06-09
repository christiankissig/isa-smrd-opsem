theory PartialConditional
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
| L8
| END

consts t1 :: T 
consts t2 :: T
consts x  :: L
consts y  :: L
consts w  :: L
consts z  :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and> x \<noteq> y \<and> w \<noteq> x \<and> w \<noteq> y \<and> z \<noteq> x \<and> z \<noteq> y \<and> z \<noteq> w"

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
consts F\<^sub>2 :: "((C \<times> C) set) set "
consts F\<^sub>e :: "((C \<times> C) set) set "

consts G  :: "((C \<times> C) set) set "

consts G\<^sub>3\<^sub>m :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>0 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>1 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>1\<^sub>5 :: "((C \<times> C) set) set "

consts G\<^sub>4\<^sub>n :: "((C \<times> C) set) set "
consts G\<^sub>4\<^sub>0 :: "((C \<times> C) set) set "
consts G\<^sub>4\<^sub>1 :: "((C \<times> C) set) set "
consts G\<^sub>4\<^sub>1\<^sub>6 :: "((C \<times> C) set) set "

consts G\<^sub>5 :: "((C \<times> C) set) set "
consts G\<^sub>6 :: "((C \<times> C) set) set "
consts G\<^sub>e :: "((C \<times> C) set) set "

consts G\<^sub>3\<^sub>0\<^sub>4\<^sub>0 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 :: "((C \<times> C) set) set "

consts G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 :: "((C \<times> C) set) set "
consts G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 :: "((C \<times> C) set) set "


definition "futures    \<equiv>   F  = {{((L1, None), (L1, None)), ((L2, None), (L2, None))}} \<and>
                           F\<^sub>1  = {{((L2, None), (L2, None))}} \<and>
                           F\<^sub>2  = {{((L1, None), (L1, None))}} \<and>
                           F\<^sub>e = {{}} \<and>
                           G = {{((L3,Some 1), (L5, None)), ((L4, Some 1),(L6, None))}, 
                                {((L3, Some 1),(L8, None)), ((L4, Some 0),(L4, Some 0))},
                                {((L4, Some 1),(L7, None)), ((L3, Some 0),(L3, Some 0))},
                                {((L3, Some 0),(L3, Some 0)), ((L4, Some 0),(L4, Some 0))}} \<and>
                          G\<^sub>3\<^sub>1 = {{((L5, None),(L5, None)), ((L4, Some 1),(L6, None))},
                                {((L8, None),(L8, None)), ((L4, Some 0),(L4, Some 0))}} \<and>
                          G\<^sub>3\<^sub>1\<^sub>5 = {{((L4, Some 1),(L6, None))}} \<and>
                          G\<^sub>3\<^sub>0 = {{((L4, Some 0),(L4, Some 0))}, {((L4, Some 1),(L7, None))}} \<and>
                          
                          G\<^sub>4\<^sub>1\<^sub>6 = {{((L3,Some 1), (L5, None))}} \<and>     
                          G\<^sub>4\<^sub>0 = {{((L3, Some 1),(L8, None))}, {((L3, Some 0),(L3, Some 0))}} \<and>
                          G\<^sub>4\<^sub>1 = {{((L7, None),(L7, None)), ((L3, Some 0),(L3, Some 0))}, 
                                 {((L3,Some 1), (L5, None)), ((L6, None),(L6, None))}} \<and>
                          G\<^sub>e = {{((END, None),(END, None))}} \<and>
                          G\<^sub>3\<^sub>0\<^sub>4\<^sub>0 = {{((END, None),(END, None))}} \<and>
                          G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 = {{((L7, None),(L7, None))}} \<and>
                          G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 = {{((L8, None),(L8, None))}} \<and>
                          G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 = {{((L5, None), (L5, None)), ((L6, None),(L6, None))}} \<and>
                          G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 = {{((L5, None), (L5, None))}} \<and>
                          G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 = {{((L6, None), (L6, None))}}"


lemmas [simp] =  thrdsvars_def

(*definition "rel_id rel \<equiv> {(a,a) . a\<in>Domain rel \<or> a\<in>Range rel} "*)

definition "members rel \<equiv> {a . a\<in>Domain rel \<or>  a\<in>Range rel} "

definition "rel_id S \<equiv> { e . fst e = snd e \<and> fst e \<in>members S}"

(*definition "minimal (p::PC) (s::(PC\<times>PC) set) \<equiv> \<forall> e . e \<in> s \<longrightarrow> p\<in>Domain s \<and> p\<notin>Range (s - rel_id s)"*)

definition "minimal (p) (s) \<equiv>  p\<in>Domain s \<and> p\<notin>Range (s - rel_id s)"

definition "fu S p v \<equiv> {}"


definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


definition prog :: "T \<Rightarrow> PC \<Rightarrow> nat option \<Rightarrow> prog_state \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog t p rv  s s' \<equiv> 
(
  if t = t1
    then
      if p = L1
      then
        (state s) [x := 1]\<^sub>t (state s') \<and>
        r1 s = r1 s'  \<and> r2 s = r2 s' \<and>
        (f s = F \<longrightarrow> f s' =  F\<^sub>1) \<and>
        (f s = F\<^sub>2 \<longrightarrow> f s' =  F\<^sub>e) \<and>
         g s' = g s \<and> rv = None
  else
      if p = L2
      then
        (state s) [y := 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s'   \<and>
         (f s = F \<longrightarrow> f s' =  F\<^sub>2) \<and>
         (f s = F\<^sub>1 \<longrightarrow> f s' =  F\<^sub>e) \<and>
         g s' = g s  \<and> rv = None           
      else
        False
else
  if t = t2
    then
      if p = L3
        then
          (state s) [r1 s' \<leftarrow> x]\<^sub>t (state s')                 
          \<and> r2 s = r2 s' \<and> f s' = f s
          \<and> (g s = G \<and> r1 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>0)
          \<and> (g s = G \<and> r1 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1)
          \<and> (g s = G\<^sub>4\<^sub>0  \<and> r1 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>0\<^sub>4\<^sub>0)
          \<and> (g s = G\<^sub>4\<^sub>0  \<and> r1 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>0)
          \<and> (g s = G\<^sub>4\<^sub>1  \<and> r1 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>0\<^sub>4\<^sub>1)
          \<and> (g s = G\<^sub>4\<^sub>1  \<and> r1 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1)
          \<and> (g s = G\<^sub>4\<^sub>1\<^sub>6 \<longrightarrow>  g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6)
          \<and> rv = Some (r1 s')
      else
        if p = L4
          then
             (state s) [r2 s' \<leftarrow> y]\<^sub>t (state s')                 
            \<and> r1 s = r1 s'  \<and> f s' = f s 
          \<and> (g s = G \<and> r2 s' = 0 \<longrightarrow> g s' = G\<^sub>4\<^sub>0)
          \<and> (g s = G \<and> r2 s' = 1 \<longrightarrow> g s' = G\<^sub>4\<^sub>1)
          \<and> (g s = G\<^sub>3\<^sub>0  \<and> r2 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>0\<^sub>4\<^sub>0)
          \<and> (g s = G\<^sub>3\<^sub>0  \<and> r2 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>0\<^sub>4\<^sub>1)
          \<and> (g s = G\<^sub>3\<^sub>1  \<and> r2 s' = 0 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>0)
          \<and> (g s = G\<^sub>3\<^sub>1  \<and> r2 s' = 1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1)
          \<and> (g s = G\<^sub>3\<^sub>1\<^sub>5 \<longrightarrow>  g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5)
          \<and> rv = Some (r2 s')

          else
        if p = L5
        then 
         (state s) [w := 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s' \<and>
         f s' = f s  \<and> 
         (g s = G\<^sub>3\<^sub>1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>5) \<and>
         (g s = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5) \<and>
         (g s = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<longrightarrow> g s' = G\<^sub>e) 
          \<and> rv = None                  
        else
        if p = L6
        then 
         (state s) [z := 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s' \<and>
         f s' = f s \<and> 
         (g s = G\<^sub>4\<^sub>1 \<longrightarrow> g s' = G\<^sub>4\<^sub>1\<^sub>6) \<and>
         (g s = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<longrightarrow> g s' = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6) \<and>
         (g s = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<longrightarrow> g s' = G\<^sub>e) 
         \<and> rv = None                     
        else
        if p = L7
        then 
         (state s) [z := 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s' \<and>
         f s' = f s \<and> g s' = G\<^sub>e \<and> rv = None                     
        else
        if p = L8
        then 
         (state s) [w := 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s' \<and>
         f s' = f s \<and> g s' = G\<^sub>e \<and> rv = None                   
        else
            False
  else
    False
)"



definition "I s \<equiv>  [w =\<^sub>t2 0] (state s) \<and> [z =\<^sub>t2 0] (state s)
"

definition prog_future_inv :: "((C \<times> C) set) set \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_future_inv p s \<equiv> 
  if p = F  then 

      [x =\<^sub>t2 0] (state s) \<and> [y =\<^sub>t2 0] (state s)

  else  if p = F\<^sub>1 then

      [y =\<^sub>t2 0] (state s) \<and> ([x \<approx>\<^sub>t2 0](state s) \<or> [x \<approx>\<^sub>t2 1](state s)) 

  else  if p = F\<^sub>2 then

      [x =\<^sub>t2 0] (state s) \<and> ([y \<approx>\<^sub>t2 0](state s) \<or> [y \<approx>\<^sub>t2 1](state s)) 

  else if p = F\<^sub>e  then

      ([y \<approx>\<^sub>t2 0](state s) \<or> [y \<approx>\<^sub>t2 1](state s)) \<and> ([x \<approx>\<^sub>t2 0](state s) \<or> [x \<approx>\<^sub>t2 1](state s)) 

  else if p = G then

     I s \<and> r1 s = 0 \<and> r2 s = 0
 
   else if p = G\<^sub>3\<^sub>0 then  

     r1 s = 0 \<and> r2 s = 0 \<and> I s

  else if p = G\<^sub>3\<^sub>1 then

    r1 s = 1 \<and> r2 s = 0 \<and> I s

  else if p = G\<^sub>3\<^sub>1\<^sub>5 then

    r1 s = 1 \<and> r2 s = 0 \<and> [w =\<^sub>t2 1] (state s) \<and> [z =\<^sub>t2 0] (state s)

  else if p = G\<^sub>4\<^sub>0 then

    r2 s = 0 \<and> r1 s = 0 \<and> I s

  else if p = G\<^sub>4\<^sub>1 then

    r2 s = 1 \<and> r1 s = 0 \<and> I s

  else if p = G\<^sub>4\<^sub>1\<^sub>6 then

    r2 s = 1 \<and> r1 s = 0 \<and> [w =\<^sub>t2 0] (state s) \<and> [z =\<^sub>t2 1] (state s)

  else if p = G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 then

    r1 s = 0 \<and> r2 s = 1 \<and> I s

  else if p = G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 then

    r1 s = 1 \<and> r2 s = 0 \<and> I s

  else if p = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 then

    r1 s = 1 \<and> r2 s = 1 \<and> I s

  else if p = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 then

     r1 s = 1 \<and> r2 s = 1 \<and> [w =\<^sub>t2 1] (state s) \<and> [z =\<^sub>t2 0] (state s)

  else if p = G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 then

     r1 s = 1 \<and> r2 s = 1 \<and> [w =\<^sub>t2 0] (state s) \<and> [z =\<^sub>t2 1] (state s)

  else if p = G\<^sub>e then
  
     [w =\<^sub>t2 (r1 s)] (state s) \<and> [z =\<^sub>t2 (r2 s)] (state s)
 
  else  False
  "
(*
  else if p = G\<^sub>3\<^sub>0\<^sub>4\<^sub>0 then

    r1 s = 0 \<and> r2 s = 0 \<and> I s

*)

lemmas [simp] = I_def

lemma po_local_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>2}"
    and "c \<in> f s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog t1 (fst p) (snd p) s s'"
  shows "prog_future_inv (f s') s'"
  using assms
  apply(simp add: futures_def)
  apply clarsimp
  apply(elim disjE)
  apply simp
  apply(subgoal_tac "c = {((L1, None), L1, None), ((L2, None), L2, None)}")
  apply simp
  apply(subgoal_tac "p \<in> {(L1, None), (L2,None)}", simp, elim disjE)
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI, simp_all)
  apply auto[1]
  apply (metis dobs_WrX_pres)
  apply (metis dobs_WrX_pres)
  apply (metis d_obs_implies_p_obs p_obs_Wr_pres_write)
  apply(simp add: prog_future_inv_def prog_def)
  apply(intro conjI impI, simp_all)
  apply (metis dobs_WrX_pres)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insertI1 insert_absorb the_elem_eq)
  apply (metis d_obs_implies_p_obs p_obs_Wr_pres_write)
  apply (metis dobs_WrX_pres)
  apply (metis empty_iff insert_iff)
  apply (metis dobs_WrX_pres)
  apply (metis d_obs_implies_p_obs p_obs_Wr_pres_write)
  apply(simp add: minimal_def)
  apply blast
  apply(subgoal_tac "c = {((L2, None), L2, None)}")
  apply(subgoal_tac "p = (L2, None)")
  apply(simp add: prog_future_inv_def  prog_def)
  apply(intro conjI impI, simp_all)  
  apply (metis dobs_WrX_pres)
  apply (metis insert_not_empty singleton_inject)
  apply (metis the_elem_eq)
  apply (metis the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis)
  apply blast
  apply (metis insert_not_empty the_elem_eq)
  apply (metis p_obs_Wr_pres_write)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis d_obs_implies_p_obs p_obs_Wr_pres_write)
  apply (metis One_nat_def p_obs_Wr_pres_write)
  using minimal_def 
  apply (metis Domain_empty Domain_insert empty_iff insert_iff) 
  apply blast
  apply(subgoal_tac "c = {((L1, None), L1, None)}")
  apply(subgoal_tac "p = (L1, None)")
  apply(simp add: prog_future_inv_def  prog_def) 
  apply(intro conjI impI, simp_all)  
  apply (metis insert_not_empty the_elem_eq)
  apply (metis dobs_WrX_pres)
  apply (metis dobs_WrX_pres)
  apply (metis p_obs_Wr_pres_write)
  apply blast
  apply blast
  apply (metis insert_not_empty the_elem_eq)
  apply (metis p_obs_Wr_pres_write)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis insert_not_empty the_elem_eq)
  apply (metis One_nat_def d_obs_implies_p_obs p_obs_Wr_pres_write)
  apply (metis One_nat_def d_obs_implies_p_obs p_obs_Wr_pres_write)
  apply (metis(full_types) Domain_empty Domain_insert insertI1 minimal_def singletonD)
  by blast


lemma distinct_gs: "futures \<Longrightarrow> S = {G, G\<^sub>3\<^sub>0, G\<^sub>3\<^sub>1, G\<^sub>4\<^sub>0, G\<^sub>4\<^sub>1, G\<^sub>3\<^sub>0\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>0, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6} \<Longrightarrow>
    \<forall> a b . a \<in> S \<and> b \<in> S - {a} \<longrightarrow> a \<noteq> b"
  by blast

lemma noteq1[simp]: "futures \<Longrightarrow> G \<noteq> F \<and> G \<noteq> F\<^sub>1 \<and> G \<noteq> F\<^sub>2  \<and> G \<noteq> F\<^sub>e \<and> G\<^sub>e \<noteq> F\<^sub>e"
  apply(simp add: futures_def)
  by (smt (z3) Diff_insert_absorb PC.distinct(19) PC.distinct(5) Pair_inject insertI1 insert_absorb insert_commute singleton_iff)

lemma noteq2[simp]: "futures \<Longrightarrow>  G \<noteq> G\<^sub>3\<^sub>1 \<and> G \<noteq> G\<^sub>3\<^sub>0 
     \<and> G \<noteq> G\<^sub>4\<^sub>0 \<and> G \<noteq> G\<^sub>4\<^sub>1 \<and> G \<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>0 \<and> G \<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G \<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G \<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>1 \<noteq>  G\<^sub>3\<^sub>0"
  apply(simp add: futures_def)
  apply clarsimp
  apply(intro conjI)
  apply (smt (z3) PC.distinct(33) Pair_inject empty_iff insertE insertI1)
  apply (smt (z3) Pair_inject doubleton_eq_iff insertE insertI1 insert_absorb insert_commute option.distinct(1))
  apply (smt (z3) Diff_insert_absorb PC.distinct(33) Pair_inject fst_conv insertI1 insert_iff singletonD)
  apply (smt (verit, ccfv_threshold) PC.simps(45) Pair_inject empty_iff insertE insertI1 insert_commute)
  apply (smt (z3) PC.distinct(59) Pair_inject insertI1 singletonD)
  apply (smt (z3) PC.distinct(39) Pair_inject insertI1 singletonD)
  apply (smt (z3) PC.distinct(33) PC.distinct(35) doubleton_eq_iff fst_conv insertI1 singletonD)
  apply (smt (z3) PC.distinct(37) fst_conv insertI1 singletonD)
  by (smt (z3) PC.distinct(43) doubleton_eq_iff fst_conv insertI1 singletonD)


lemma noteq3[simp]: "futures \<Longrightarrow> F\<^sub>e \<noteq> F \<and> F\<^sub>2 \<noteq> F\<^sub>1 \<and> F\<^sub>e \<noteq> F\<^sub>2 \<and> F\<^sub>e \<noteq> F\<^sub>1 \<and> F \<noteq> F\<^sub>1 \<and> F \<noteq> F\<^sub>2 "
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(1) PC.distinct(15) Pair_inject doubleton_eq_iff insert_absorb2)


lemma noteq4[simp]: "futures \<Longrightarrow> G \<noteq> F \<and> G\<^sub>3\<^sub>0  \<noteq> F \<and> G\<^sub>3\<^sub>1 \<noteq> F \<and> G\<^sub>4\<^sub>0 \<noteq> F \<and> G\<^sub>4\<^sub>1 \<noteq> F \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<noteq> F \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<noteq> F \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<noteq> F \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<noteq> F \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<noteq> F"
  apply(simp add: futures_def)
  by (smt (z3) Diff_insert_absorb PC.distinct(1) PC.distinct(23) PC.distinct(9) fst_conv insertE insertI1 insert_absorb insert_not_empty snd_conv)


lemma noteq5[simp]: "futures \<Longrightarrow> G \<noteq> F\<^sub>1 \<and> G\<^sub>3\<^sub>0  \<noteq>  F\<^sub>1 \<and> G\<^sub>3\<^sub>1 \<noteq>  F\<^sub>1 \<and> G\<^sub>4\<^sub>0 \<noteq>  F\<^sub>1 \<and> G\<^sub>4\<^sub>1 \<noteq>  F\<^sub>1 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<noteq>  F\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<noteq>  F\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<noteq>  F\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<noteq>  F\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<noteq>  F\<^sub>1"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(19) PC.distinct(21) PC.distinct(23) PC.distinct(25) PC.distinct(27) fst_conv insertI1 singleton_iff snd_conv)


lemma noteq6[simp]: "futures \<Longrightarrow> G \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>0  \<noteq>  F\<^sub>2 \<and> G\<^sub>3\<^sub>1 \<noteq>  F\<^sub>2 \<and> G\<^sub>4\<^sub>0 \<noteq>  F\<^sub>2 \<and> G\<^sub>4\<^sub>1 \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<noteq> F\<^sub>2"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(11) PC.distinct(13) PC.distinct(5) PC.distinct(7) PC.distinct(9) fst_conv insertI1 singleton_iff snd_conv)


lemma noteq7[simp]: "futures \<Longrightarrow> G \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>0  \<noteq>  F\<^sub>e \<and> G\<^sub>3\<^sub>1 \<noteq>  F\<^sub>e \<and> G\<^sub>4\<^sub>0 \<noteq>  F\<^sub>e \<and> G\<^sub>4\<^sub>1 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<noteq> F\<^sub>e"
  apply(simp add: futures_def)
  by (smt (z3)  insertI1 insert_not_empty singletonD)


lemma noteq_all: "futures \<Longrightarrow> a \<in>  {G, G\<^sub>3\<^sub>0, G\<^sub>3\<^sub>1, G\<^sub>4\<^sub>0, G\<^sub>4\<^sub>1, G\<^sub>3\<^sub>0\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>0, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6} \<Longrightarrow> b \<in>  {G, G\<^sub>3\<^sub>0, G\<^sub>3\<^sub>1, G\<^sub>4\<^sub>0, G\<^sub>4\<^sub>1, G\<^sub>3\<^sub>0\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>0, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6} - {a} \<Longrightarrow> a \<noteq> b"
  apply safe
  done

lemma noteq8[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>3\<^sub>0 \<and>  G\<^sub>3\<^sub>1\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>3\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq> G\<^sub>3\<^sub>0"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(31) Pair_inject doubleton_eq_iff insertE insertI1 insert_absorb option.distinct(1) singleton_inject)

lemma noteq9[simp]:"futures \<Longrightarrow> G \<noteq>  G\<^sub>3\<^sub>1 \<and>  G\<^sub>3\<^sub>0\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>4\<^sub>0\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>4\<^sub>1\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq>  G\<^sub>3\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq>  G\<^sub>3\<^sub>1"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(31) PC.distinct(33) PC.distinct(49) PC.simps(45) fst_conv insertE insertI1 insert_commute insert_not_empty singleton_iff)

lemma noteq10[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>4\<^sub>0 \<and>  G\<^sub>3\<^sub>0\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq> G\<^sub>4\<^sub>0"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(31) Pair_inject doubleton_eq_iff insertE insertI1 insert_absorb option.distinct(1) singleton_inject)


lemma noteq11[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>0 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>4\<^sub>0 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<noteq> G\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<noteq> G\<^sub>4\<^sub>1"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(31) Pair_inject Range_insert doubleton_eq_iff insertE insertI1 insert_absorb option.distinct(1))

lemma noteq12[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>0\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>1\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<and>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(47) PC.distinct(55) PC.distinct(61) PC.distinct(67) Pair_inject insertI1 insert_absorb insert_ident insert_not_empty singleton_iff)

lemma noteq13[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and>  G\<^sub>3\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and>  G\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(39) PC.distinct(49) PC.distinct(57) PC.distinct(63) PC.distinct(67) fst_conv insertI1 singleton_iff)

lemma noteq14[simp]:"futures \<Longrightarrow> G \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>0 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>4\<^sub>0 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>4\<^sub>1 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<noteq>  G\<^sub>3\<^sub>1\<^sub>4\<^sub>1"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(33) PC.distinct(53) doubleton_eq_iff fst_conv insertI1 insert_commute n_not_Suc_n option.inject singletonD snd_conv)


lemma noteq15[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and>  G\<^sub>3\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5  \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5"
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(45) PC.distinct(53) PC.distinct(61) PC.distinct(63) Pair_inject insertI1 singletonD)


lemma noteq16[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 "
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(53) PC.distinct(55) PC.distinct(57) fst_conv insertI1 insert_absorb insert_ident insert_not_empty singletonD snd_conv)


lemma noteq17[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>0\<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>e \<and> G\<^sub>4\<^sub>0\<noteq> G\<^sub>e \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq>G\<^sub>e "
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(51) PC.distinct(59) PC.distinct(65) PC.distinct(69) PC.distinct(71) fst_conv insertI1 singletonD snd_conv)

lemma noteq18[simp] : "futures \<Longrightarrow> G\<^sub>e \<noteq> F\<^sub>2 \<and> G\<^sub>e \<noteq> F\<^sub>1 \<and> G\<^sub>e \<noteq> F \<and> F\<^sub>e \<noteq> G\<^sub>3\<^sub>1\<^sub>5"
  apply(simp add: futures_def)
  apply(intro conjI)
  apply (metis PC.distinct(15) fst_conv the_elem_eq)
  apply (metis PC.distinct(29) fst_conv the_elem_eq)
  apply (smt (z3) PC.distinct(15) fst_conv insertI1 singletonD)
  by (metis empty_not_insert the_elem_eq)

lemma noteq19[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq>G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>4\<^sub>1\<^sub>6 \<noteq> G\<^sub>3\<^sub>1\<^sub>5 "
  apply(simp add: futures_def)
  by (smt (verit, del_insts) PC.distinct(31) PC.distinct(45) fst_conv singleton_insert_inj_eq' snd_conv the_elem_eq)

lemma noteq20[simp]:"futures \<Longrightarrow> G \<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>0\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>4\<^sub>0\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>4\<^sub>1\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>0\<^sub>4\<^sub>1\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>0\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5\<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6\<noteq>G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>4\<^sub>1\<^sub>6 \<noteq> G\<^sub>3\<^sub>1\<^sub>5 "
  apply(simp add: futures_def)
  by (smt (z3) PC.distinct(31) PC.distinct(33) Pair_inject insertI1 insert_absorb insert_ident insert_not_empty singletonD)

lemma noteq0 [simp] : "futures \<Longrightarrow> G\<^sub>3\<^sub>1\<^sub>5 \<noteq> F\<^sub>2 \<and> G\<^sub>4\<^sub>1\<^sub>6 \<noteq> F\<^sub>2 \<and> G\<^sub>3\<^sub>1\<^sub>5 \<noteq> F\<^sub>1 \<and> G\<^sub>4\<^sub>1\<^sub>6 \<noteq> F\<^sub>1 \<and> G\<^sub>3\<^sub>1\<^sub>5 \<noteq> F \<and> G\<^sub>4\<^sub>1\<^sub>6 \<noteq> F \<and> G\<^sub>e \<noteq> G\<^sub>4\<^sub>1\<^sub>6 \<and> G\<^sub>e \<noteq> G\<^sub>3\<^sub>1\<^sub>5 \<and> G\<^sub>4\<^sub>1\<^sub>6 \<noteq> F\<^sub>e \<and> G\<^sub>3\<^sub>1\<^sub>5 \<noteq> F\<^sub>e"
  apply(simp add: futures_def)
  apply(intro conjI)
  apply (metis PC.distinct(9) fst_conv snd_conv the_elem_eq)
  apply (metis PC.distinct(7) Pair_inject the_elem_eq)
  apply (metis PC.distinct(23) fst_conv snd_conv the_elem_eq)
  apply (metis PC.distinct(21) fst_conv snd_conv the_elem_eq)
  apply (smt (z3) PC.simps(10) fst_conv insertI1 singletonD snd_conv)
  apply (smt (z3) PC.distinct(3) fst_conv insertI1 singletonD)
  apply (metis PC.distinct(59) fst_conv snd_conv the_elem_eq)
  apply (metis PC.distinct(65) fst_conv snd_conv the_elem_eq)
  apply (metis empty_not_insert the_elem_eq)
  by (metis empty_not_insert the_elem_eq)


lemma empeq [simp]: "futures \<Longrightarrow> G\<^sub>3\<^sub>0\<^sub>4\<^sub>0 = G\<^sub>e"
  apply(simp add: futures_def)
  by metis

lemma G_minmals: "futures \<Longrightarrow> c\<in>G \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L3, Some 0),(L3, Some 1),(L4, Some 0),(L4, Some 1)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G30_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>3\<^sub>0 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L4, Some 0),(L4, Some 1)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G31_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>3\<^sub>1 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L5, None),(L8, None),(L4, Some 1),(L4, Some 0)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G40_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>4\<^sub>0 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L3, Some 1),(L3, Some 0)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G41_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>4\<^sub>1 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L6, None),(L7, None),(L3, Some 0),(L3, Some 1)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G3041_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>3\<^sub>0\<^sub>4\<^sub>1 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L7, None)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G3141_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>3\<^sub>1\<^sub>4\<^sub>1 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{(L5, None), (L6, None)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G31415_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{ (L6, None)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma G31416_minmals: "futures \<Longrightarrow> c\<in>G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6 \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{ (L5, None)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)


lemma F_minmals: "futures \<Longrightarrow> c\<in>F \<Longrightarrow>  minimal p c \<Longrightarrow> p\<in>{ (L1, None), (L2, None)}"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma F1_minmals: "futures \<Longrightarrow> c\<in>F\<^sub>1 \<Longrightarrow>  minimal p c \<Longrightarrow> p=  (L2, None)"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)

lemma F2_minmals: "futures \<Longrightarrow> c\<in>F\<^sub>2 \<Longrightarrow>  minimal p c \<Longrightarrow> p=  (L1, None)"
  apply(simp add: futures_def minimal_def)
  apply(elim conjE exE)
  by (smt (z3) Domain_empty Domain_insert insertE insertI1 singletonD)


lemma po_global_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>2}"
    and "g s \<in> {G, G\<^sub>3\<^sub>0, G\<^sub>3\<^sub>1, G\<^sub>3\<^sub>1\<^sub>5, G\<^sub>4\<^sub>0, G\<^sub>4\<^sub>1,G\<^sub>4\<^sub>1\<^sub>6, G\<^sub>3\<^sub>0\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>0, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6, G\<^sub>e}"
    and "c \<in> f s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t1 (fst p) (snd p) s s'"
  shows "prog_future_inv (g s') s'"
  using assms
  apply clarsimp
  apply(elim conjE disjE)
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis dobs_WrX_pres)
  apply (metis dobs_WrX_pres)  
  apply (metis F_minmals)
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def dobs_WrX_pres)
  apply (metis I_def dobs_WrX_pres)
  using F_minmals apply blast
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq2) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq8)
  using F_minmals apply blast
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply(case_tac "G\<^sub>3\<^sub>1\<^sub>5 = G"; simp)
  apply (smt (z3) One_nat_def dobs_WrX_pres noteq19)
  apply(case_tac "G\<^sub>3\<^sub>1\<^sub>5 = G\<^sub>3\<^sub>0"; simp)
  using noteq19 apply presburger
  apply(case_tac "G\<^sub>3\<^sub>1\<^sub>5 = G\<^sub>3\<^sub>1"; simp)
  using noteq19 apply presburger
  apply (metis dobs_WrX_pres noteq19)
  apply(case_tac "G\<^sub>3\<^sub>1\<^sub>5 = G"; simp)
  apply (smt (z3) One_nat_def dobs_WrX_pres noteq19)
  apply(case_tac "G\<^sub>3\<^sub>1\<^sub>5 = G\<^sub>3\<^sub>0"; simp)
  using noteq19 apply presburger 
  apply(case_tac "G\<^sub>3\<^sub>1\<^sub>5 = G\<^sub>3\<^sub>1"; simp)
  using noteq19 apply presburger 
  apply (metis dobs_WrX_pres noteq19)
  using F_minmals apply blast
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def dobs_WrX_pres noteq19 noteq9)
  apply (metis I_def dobs_WrX_pres noteq19 noteq9)
  apply (metis F_minmals)
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq11 noteq19)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq19 noteq8 noteq9)
  using F_minmals apply blast
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (smt (z3) One_nat_def dobs_WrX_pres noteq20)
  apply (smt (z3) One_nat_def dobs_WrX_pres noteq20)
  using F_minmals apply blast
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq19 noteq20 noteq8 noteq9)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq12 noteq19 noteq20)
  using F_minmals apply blast
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq11 noteq12 noteq19 noteq20 noteq8)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq11 noteq12 noteq19 noteq20 noteq8)
  using F_minmals apply auto[1]
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq11 noteq12 noteq13 noteq19 noteq20 noteq8 noteq9)
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq11 noteq12 noteq13 noteq19 noteq20 noteq8 noteq9)
  apply (metis F_minmals)
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis One_nat_def dobs_WrX_pres noteq15 noteq19 noteq20)
  apply (metis One_nat_def dobs_WrX_pres noteq15 noteq19 noteq20)
  apply (metis F_minmals)
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (metis One_nat_def dobs_WrX_pres noteq16 noteq19 noteq20)
  apply (metis One_nat_def dobs_WrX_pres noteq16 noteq19 noteq20)
  apply (metis F_minmals)
  apply(subgoal_tac "p\<in>{(L1, None), (L2, None)}") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply(elim disjE; simp)
  apply (smt (z3) dobs_WrX_pres noteq17)
  apply (smt (z3) dobs_WrX_pres noteq17) 
  apply (metis F_minmals)
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis dobs_WrX_pres)
  using F1_minmals apply blast
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis dobs_WrX_pres)
  using F2_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def dobs_WrX_pres)  using F1_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq2)
  using F1_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis One_nat_def dobs_WrX_pres noteq19)
  using F1_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def dobs_WrX_pres noteq10 noteq19) 
  using F1_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq19 noteq8 noteq9) 
  using F1_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq10 noteq19 noteq8 noteq9) 
  using F1_minmals apply blast
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq12 noteq19 noteq20)
  using F1_minmals apply blast  
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq13 noteq19 noteq20)
  using F1_minmals apply blast      
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq14 noteq19 noteq20)
  using F1_minmals apply blast    
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis One_nat_def dobs_WrX_pres noteq15 noteq19 noteq20) 
  using F1_minmals apply blast      
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis One_nat_def dobs_WrX_pres noteq16 noteq19 noteq20)
  using F1_minmals apply blast      
  apply(subgoal_tac "p=(L2, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (smt (z3) dobs_WrX_pres noteq17) 
  using F1_minmals apply blast 
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def dobs_WrX_pres)
  using F2_minmals apply blast      
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq9)
  using F2_minmals apply blast  
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq9)
  using F2_minmals apply blast  
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def dobs_WrX_pres noteq10 noteq19) 
  using F2_minmals apply blast    
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq11 noteq19) 
  using F2_minmals apply blast      
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis One_nat_def dobs_WrX_pres noteq20) 
  using F2_minmals apply blast      
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq12 noteq19 noteq20)
  using F2_minmals apply blast        
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq13 noteq19 noteq20) 
  using F2_minmals apply blast        
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis I_def One_nat_def dobs_WrX_pres noteq14 noteq19 noteq20)
  using F2_minmals apply blast        
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis One_nat_def dobs_WrX_pres noteq15 noteq19 noteq20) 
  using F2_minmals apply blast    
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (metis One_nat_def dobs_WrX_pres noteq16 noteq19 noteq20)
  using F2_minmals apply blast    
  apply(subgoal_tac "p=(L1, None)") 
  apply( simp add: prog_def prog_future_inv_def) 
  apply (smt (z3) dobs_WrX_pres noteq17)  using F2_minmals apply blast      
  done

lemma po_local_t2:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "g s \<in> {G, G\<^sub>3\<^sub>0, G\<^sub>3\<^sub>1, G\<^sub>3\<^sub>1\<^sub>5, G\<^sub>4\<^sub>0, G\<^sub>4\<^sub>1,G\<^sub>4\<^sub>1\<^sub>6, G\<^sub>3\<^sub>0\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>0, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv (g s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv (g s') s'"
    using assms
    apply clarsimp
    apply(elim disjE)
    apply clarsimp
    apply(subgoal_tac "p\<in>{(L3, Some 0),(L3, Some 1),(L4, Some 0),(L4, Some 1)} ", clarsimp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply(intro conjI impI)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply(simp add: prog_def prog_future_inv_def)
    apply(subgoal_tac "p\<in>{(L3, Some 0),(L3, Some 1),(L4, Some 0),(L4, Some 1)} ", clarsimp, erule disjE; case_tac "fst p"; clarsimp)
    apply(intro conjI impI)
    apply simp_all
    apply (metis noteq2)
    apply (metis d_obs_RdX_other)  
    apply (metis d_obs_RdX_other) 
    apply (smt (z3) PC.simps(32) Pair_inject prod.collapse)
    apply(intro allI impI conjI) 
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 noteq18 noteq19 noteq20 apply presburger+
    using noteq10 noteq11 option.inject snd_conv apply metis
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 noteq18 noteq19 noteq20 apply presburger+
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 noteq18 noteq19 noteq20 apply presburger+
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 noteq18 noteq19 noteq20 apply presburger+
    apply (metis noteq10 noteq11 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 noteq18 noteq19 noteq20 apply presburger+
    apply (metis noteq10 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    using noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 apply presburger+
    apply (metis noteq10 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    using noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 apply presburger+
    apply (metis noteq10 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply (metis noteq10 option.inject snd_conv)
    apply (metis d_obs_RdX_other)
    apply (metis option.inject snd_conv)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (metis eq_snd_iff option.inject)
    apply (smt (z3) PC.distinct(43) fst_conv)
    apply (smt (z3) PC.distinct(45) fst_conv)
    apply (metis PC.distinct(47) fst_conv)
    apply (metis PC.distinct(49) fst_conv)
    using G_minmals One_nat_def apply blast
    apply(subgoal_tac "p \<in> {(L4, Some 0), (L4, Some 1)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply(case_tac "G\<^sub>3\<^sub>0 = G";simp)
    apply(intro conjI impI)
    apply simp_all
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17  noteq18  noteq19  noteq20 apply presburger+
    apply(intro conjI impI)
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17  noteq18  noteq19  noteq20 apply presburger+
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    apply(simp add: prog_def prog_future_inv_def)
    apply(case_tac "G\<^sub>3\<^sub>0 = G";simp)
    apply(intro conjI impI)
    using noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17 apply presburger+
    apply(intro conjI impI)
    apply (metis noteq2)
    apply (metis d_obs_RdX_other)
    apply (metis d_obs_RdX_other)
    using G30_minmals One_nat_def apply blast
    apply(subgoal_tac "p \<in> {(L5, None), (L4, Some 1), (L8, None), (L4, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_WrX_other d_obs_WrX_set noteq18 noteq19 noteq2)
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_RdX_other noteq2)
    apply(intro conjI impI)
    apply simp_all
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17  noteq18  noteq19  noteq20 apply presburger+
    apply (metis I_def One_nat_def d_obs_WrX_set noteq2)
    apply (metis I_def d_obs_WrX_other)
    apply (metis I_def One_nat_def d_obs_RdX_other noteq2)
    using G31_minmals One_nat_def apply blast
    apply(subgoal_tac "p = (L4, Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_RdX_other noteq15 noteq18)
    apply(simp add: minimal_def futures_def) 
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p \<in> {(L3, Some 1), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def d_obs_RdX_other noteq19 noteq2)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def d_obs_RdX_other noteq17 noteq19)
    using G40_minmals apply presburger
    apply(subgoal_tac "p \<in> {(L3,Some 1), (L6, None), (L7, None), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_RdX_other noteq10 noteq19 noteq2 noteq8 noteq9)
    apply(elim disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply(intro conjI impI)
    using noteq0 noteq1 noteq2 noteq3 noteq4 noteq5 noteq6 noteq7 noteq8 noteq9 noteq10 noteq11 noteq12 noteq13 noteq14 noteq15 noteq16  noteq17  noteq18  noteq19  noteq20 apply presburger+
    using One_nat_def noteq11 noteq19 apply presburger
    apply (metis noteq19 noteq9)
    apply (metis I_def d_obs_WrX_other noteq19)
    apply (metis I_def d_obs_WrX_set)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_WrX_other d_obs_WrX_set noteq10 noteq17 noteq19 noteq2 noteq8 noteq9)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_RdX_other noteq10 noteq19 noteq2 noteq8 noteq9)
    using G41_minmals apply blast
    apply(subgoal_tac "p = (L3,Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_RdX_other noteq16 noteq20)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L7, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (smt (z3) I_def One_nat_def d_obs_WrX_other d_obs_WrX_set noteq10 noteq17 noteq19 noteq2 noteq8 noteq9)
    using G3041_minmals apply blast
    apply(subgoal_tac "p = (L8, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_WrX_other d_obs_WrX_set noteq10 noteq11 noteq12 noteq17 noteq2 noteq20 noteq8)
    apply(simp add: minimal_def futures_def)
    apply (metis Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L5, None) \<or> p = (L6, None)") 
    apply(elim disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_WrX_other d_obs_WrX_set noteq10 noteq11 noteq12 noteq13 noteq15 noteq19 noteq2 noteq20 noteq8 noteq9)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis I_def One_nat_def d_obs_WrX_other d_obs_WrX_set noteq10 noteq11 noteq12 noteq13 noteq16 noteq19 noteq2 noteq20 noteq8 noteq9)
    using G3141_minmals apply blast
    apply(subgoal_tac "p = (L6, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (smt (z3) One_nat_def d_obs_WrX_other d_obs_WrX_set noteq15 noteq17 noteq19)
    using G31415_minmals apply blast
    apply(subgoal_tac "p = (L5, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (smt (z3) One_nat_def d_obs_WrX_other d_obs_WrX_set noteq16 noteq17 noteq20)
    using G31416_minmals by blast


lemma po_global_t1:
  assumes "wfs (state s)"
    and "thrdsvars"
    and "futures"
    and "f s \<in> {F, F\<^sub>1, F\<^sub>2, F\<^sub>e}"
    and "g s \<in> {G, G\<^sub>3\<^sub>0, G\<^sub>3\<^sub>1, G\<^sub>3\<^sub>1\<^sub>5, G\<^sub>4\<^sub>0, G\<^sub>4\<^sub>1,G\<^sub>4\<^sub>1\<^sub>6, G\<^sub>3\<^sub>0\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>0, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>5, G\<^sub>3\<^sub>1\<^sub>4\<^sub>1\<^sub>6}"
    and "c \<in> g s"
    and "minimal p c"
    and "prog_future_inv (f s) s"
    and "prog_future_inv (g s) s"
    and "prog t2 (fst p) (snd p) s s'"
  shows "prog_future_inv (f s') s'"
  using assms
    apply clarsimp
    apply(elim conjE disjE)
    apply(subgoal_tac "p\<in>{(L3, Some 0),(L3, Some 1),(L4, Some 0),(L4, Some 1)} ", clarsimp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis d_obs_RdX_other d_obs_RdX_pres)
    apply(elim disjE)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis d_obs_RdX_other d_obs_RdX_pres)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply (metis G_minmals)
    apply(subgoal_tac "p \<in> {(L4, Some 0), (L4, Some 1)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other d_obs_RdX_pres)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)  
    using G30_minmals One_nat_def apply blast
    apply(subgoal_tac "p \<in> {(L5, None), (L4, Some 1), (L8, None), (L4, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_WrX_other)
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply (metis d_obs_WrX_other)  
    apply (metis d_obs_RdX_other d_obs_RdX_pres)  
    using G31_minmals apply blast
    apply(subgoal_tac "p = (L4, Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p \<in> {(L3, Some 1), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other d_obs_RdX_pres)
    apply (metis G40_minmals)
    apply(subgoal_tac "p \<in> {(L3,Some 1), (L6, None), (L7, None), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_WrX_other)
    apply (metis d_obs_WrX_other)
    apply (metis d_obs_RdX_other d_obs_RdX_pres)
    using G41_minmals apply blast
    apply(subgoal_tac "p = (L3,Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L7, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_WrX_other)
    using G3041_minmals apply blast
    apply(subgoal_tac "p = (L8, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_WrX_other)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L5, None) \<or> p = (L6, None)") 
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_WrX_other)
    apply (metis d_obs_WrX_other)
    using G3141_minmals apply blast
    apply(subgoal_tac "p = (L6, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (smt (z3) One_nat_def d_obs_WrX_other d_obs_WrX_set noteq15 noteq17 noteq19)
    using G31415_minmals apply blast
    apply(subgoal_tac "p = (L5, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (smt (z3) One_nat_def d_obs_WrX_other d_obs_WrX_set noteq16 noteq17 noteq20)
    using G31416_minmals apply blast
    (****)
    apply(subgoal_tac "p\<in>{(L3, Some 0),(L3, Some 1),(L4, Some 0),(L4, Some 1)} ", clarsimp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(elim disjE; simp add: prog_def prog_future_inv_def)  
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(intro conjI impI allI)
    using noteq3 apply presburger
    using noteq3 apply presburger
    apply (metis d_obs_RdX_pres)
    apply(case_tac "F\<^sub>1 = F"; simp)
    apply(elim conjE disjE; simp)
    apply(intro disjI1)
    using d_obs_pre_p_obs_post apply presburger
    using d_obs_pre_p_obs_post apply presburger
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply (metis G_minmals)
    apply(subgoal_tac "p\<in>{(L3, Some 0),(L3, Some 1),(L4, Some 0),(L4, Some 1)} ", clarsimp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply(case_tac "F\<^sub>2 = F"; simp)
    apply (metis d_obs_RdX_other d_obs_RdX_pres)
    apply(intro conjI)  
    apply (metis d_obs_RdX_pres)
    apply(elim conjE)
    apply simp
    apply(elim disjE, intro disjI1)
    using d_obs_pre_p_obs_post  
    apply presburger
    using d_obs_pre_p_obs_post apply presburger
    apply(elim disjE, simp add: prog_def prog_future_inv_def; case_tac "F\<^sub>2 = F"; simp)
    apply (metis  noteq3 )
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    using noteq3 apply presburger
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other p_obs_RdX_intro)
    using noteq3 apply presburger
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other p_obs_RdX_intro)
    apply (metis G_minmals)
    apply(simp add: prog_def prog_future_inv_def)
    apply(case_tac "fst p"; simp)
    apply(elim disjE conjE)
    apply (smt (z3) G_minmals One_nat_def Pair_inject d_obs_pre_p_obs_post insertE noteq0 noteq1 noteq7 option.inject p_obs_RdX_intro prod.collapse singletonD)
    apply (smt (z3) G_minmals One_nat_def Pair_inject d_obs_pre_p_obs_post insertE noteq0 noteq1 noteq7 option.inject p_obs_RdX_intro prod.collapse singletonD)
    apply (smt (z3) G_minmals One_nat_def Pair_inject d_obs_pre_p_obs_post insertE noteq0 noteq1 noteq7 option.inject p_obs_RdX_intro prod.collapse singletonD)
    apply (smt (z3) G_minmals One_nat_def Pair_inject d_obs_pre_p_obs_post insertE noteq0 noteq1 noteq7 option.inject p_obs_RdX_intro prod.collapse singletonD)
    apply (smt (z3) G_minmals One_nat_def Pair_inject d_obs_pre_p_obs_post insertE noteq0 noteq1 noteq7 option.inject p_obs_RdX_intro prod.collapse singletonD)
    apply (smt (z3) Domain.simps Domain_insert G_minmals PC.distinct(33) PC.distinct(43) empty_iff insert_iff prod.exhaust_sel)
    apply (metis Domain.simps Domain_insert G_minmals PC.distinct(36) PC.distinct(45) empty_iff insert_iff prod.exhaust_sel)
    apply (smt (z3) DiffD2 Diff_insert_absorb G_minmals Pair_inject insert_iff option.distinct(1) prod.collapse)
    apply (smt (z3) G_minmals PC.distinct(39) PC.distinct(49) Pair_inject insertE prod.collapse singletonD)
    apply(subgoal_tac "p \<in> {(L4, Some 0), (L4, Some 1)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_RdX_pres d_obs_pre_p_obs_post noteq3)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    using G30_minmals apply blast
    apply(subgoal_tac "p \<in> {(L5, None), (L4, Some 1), (L8, None), (L4, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply(intro impI conjI)
    apply (metis noteq3)
    using noteq3 apply presburger
    apply (metis d_obs_WrX_other)
    apply(case_tac "F\<^sub>1 = F"; case_tac "G\<^sub>3\<^sub>1 = G"; simp)
    using noteq2 apply presburger
    apply(elim conjE disjE)
    apply(intro disjI1)
    using d_obs_pre_write_p_obs_post apply presburger
    using d_obs_pre_write_p_obs_post apply presburger
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    apply (metis One_nat_def d_obs_RdX_pres d_obs_pre_p_obs_post noteq3)   
    using G31_minmals apply blast
    apply(subgoal_tac "p = (L4, Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value zero_neq_one)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p \<in> {(L3, Some 1), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    using G40_minmals apply blast
    apply(subgoal_tac "p \<in> {(L3,Some 1), (L6, None), (L7, None), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(elim conjE disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)   
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)   
    using G41_minmals apply blast
    apply(subgoal_tac "p = (L3,Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L7, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    using G3041_minmals apply blast
    apply(subgoal_tac "p = (L8, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    apply(simp add: minimal_def futures_def)
    apply (metis Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L5, None) \<or> p = (L6, None)") 
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    using G3141_minmals apply blast
    apply(subgoal_tac "p = (L6, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    using G31415_minmals apply blast
    apply(subgoal_tac "p = (L5, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post)
    using G31416_minmals apply blast
    apply(subgoal_tac "p \<in> {(L4, Some 0), (L4, Some 1)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    using G30_minmals apply blast
    apply(subgoal_tac "p \<in> {(L4, Some 0), (L4, Some 1)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    using G30_minmals apply blast
    apply(subgoal_tac "p \<in> {(L5, None), (L4, Some 1), (L8, None), (L4, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    using G31_minmals apply blast
    apply(subgoal_tac "p = (L4, Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_RdX_other noteq3 p_obs_RdX_intro)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p \<in> {(L3, Some 1), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value noteq3 zero_neq_one)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_RdX_pres d_obs_pre_p_obs_post noteq3)
    using G40_minmals apply blast 
    apply(subgoal_tac "p \<in> {(L3,Some 1), (L6, None), (L7, None), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_read_value noteq3 zero_neq_one)
    apply(elim conjE disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)   
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply (metis One_nat_def d_obs_RdX_pres d_obs_pre_p_obs_post noteq3)
    using G41_minmals apply blast
    apply(subgoal_tac "p = (L3,Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_read_value noteq3 zero_neq_one)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L7, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    using G3041_minmals apply blast
    apply(subgoal_tac "p = (L8, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply(simp add: minimal_def futures_def)
    apply (metis Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L5, None) \<or> p = (L6, None)") 
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    using G3141_minmals apply blast  
    apply(subgoal_tac "p = (L6, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)  using G31415_minmals apply blast
    apply(subgoal_tac "p = (L5, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    using G31416_minmals apply blast
    apply(subgoal_tac "p \<in> {(L5, None), (L4, Some 1), (L8, None), (L4, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    using G31_minmals apply blast
    apply(subgoal_tac "p = (L4, Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p \<in> {(L3, Some 1), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    using G40_minmals apply blast 
    apply(subgoal_tac "p \<in> {(L3,Some 1), (L6, None), (L7, None), (L3, Some 0)}", simp, erule disjE)
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    apply(elim conjE disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)   
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    using G41_minmals apply blast
    apply(subgoal_tac "p = (L3,Some 1)")
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis d_obs_pre_p_obs_post p_obs_RdX_intro)
    apply(simp add: minimal_def futures_def)
    apply (metis (no_types, lifting) Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L7, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    using G3041_minmals apply blast
    apply(subgoal_tac "p = (L8, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply(simp add: minimal_def futures_def)
    apply (metis Domain_empty Domain_insert insertI1 singletonD)
    apply(subgoal_tac "p = (L5, None) \<or> p = (L6, None)") 
    apply(elim disjE; simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    using G3141_minmals apply blast  
    apply(subgoal_tac "p = (L6, None)") 
    apply(simp add: prog_def prog_future_inv_def)
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)  using G31415_minmals apply blast
    apply(subgoal_tac "p = (L5, None)") 
    apply(simp add: prog_def prog_future_inv_def) 
    apply (metis One_nat_def d_obs_WrX_other d_obs_pre_write_p_obs_post noteq3)
    using G31416_minmals apply blast
    done





end
