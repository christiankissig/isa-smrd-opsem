theory OpSem
imports Main HOL.Rat (*SetADT*)
begin

type_synonym TS = rat (* Timestamp *)
type_synonym T = nat (* Thread ID *)
type_synonym L = nat (* Location *)
type_synonym V = nat

definition "null = (0 :: nat)"


(* bool: true = release/aquire or false = relaxed*)
datatype action =
    Read bool L V
  | Write bool L V
  | Update L V V

fun avar :: "action \<Rightarrow> L" where
    "avar (Read _ x v) = x"
  | "avar (Write _ x v) = x"
  | "avar (Update x e v) = x"

fun wr_val :: "action \<Rightarrow> V option" where
    "wr_val (Write _ _ v) =  Some v"
  | "wr_val (Update _ _ v) = Some v"
  | "wr_val _ = None"

fun rd_val :: "action \<Rightarrow> V option" where
    "rd_val (Read _ _ v) = Some v"
  | "rd_val (Update _ v _) = Some v"
  | "rd_val _ = None"

fun isRA :: "action \<Rightarrow> bool" where
    "isRA (Read b _ _) = b"
  | "isRA (Write b _ _) = b"
  | "isRA (Update _ _ _) = True"

fun isWr :: "action \<Rightarrow> bool" where
    "isWr (Read _ _ _) = False"
  | "isWr (Write _ _ _) = True"
  | "isWr (Update _ _ _) = False"

fun isRd :: "action \<Rightarrow> bool" where
    "isRd (Read _ _ _) = True"
  | "isRd (Write _ _ _) = False"
  | "isRd (Update _ _ _) = False"

fun isUp :: "action \<Rightarrow> bool" where
    "isUp (Read _ _ _) = False"
  | "isUp (Write _ _ _) = False"
  | "isUp (Update _ _ _) = True"


abbreviation "reads a \<equiv> a \<in> (dom rd_val)"
abbreviation "writes a \<equiv> a \<in> (dom wr_val)"


type_synonym View = "L \<Rightarrow> T"

type_synonym event = "TS \<times> T \<times> action"

definition time_stamp :: "event \<Rightarrow> TS" where "time_stamp e \<equiv> fst e"
definition tid :: "event \<Rightarrow> T" where "tid e \<equiv> fst (snd e)"
definition act :: "event \<Rightarrow> action" where "act e \<equiv> snd (snd e)"

definition var :: "L \<times> TS \<Rightarrow> L" where "var = fst"
definition tst :: "L \<times> TS \<Rightarrow> TS" where "tst = snd"

lemma [simp]: "var (x, ts) = x" by(simp add: var_def)
lemma [simp]: "tst (x, ts) = ts" by(simp add: tst_def)

record write_record =
  val :: V
  is_releasing :: bool




record surrey_state =
  writes :: "(L \<times> TS) set"
  thrView :: "T \<Rightarrow> L \<Rightarrow> (L \<times> TS)"
  modView :: "(L \<times> TS) \<Rightarrow> L \<Rightarrow> (L \<times> TS)"
  mods :: "(L \<times> TS) \<Rightarrow> write_record"
  covered :: "(L \<times> TS) set"


definition "value \<sigma> w \<equiv>  val (mods \<sigma> w)"
definition "releasing \<sigma> w \<equiv>  is_releasing (mods \<sigma> w)"

definition "writes_on \<sigma> x = {w . var w = x \<and> w \<in> writes \<sigma>}"
definition "visible_writes \<sigma> t x \<equiv> {w \<in> writes_on \<sigma> x . tst(thrView \<sigma> t x) \<le> tst w}"



lemma writes_on_var [simp]: "w \<in> writes_on \<sigma> x \<Longrightarrow> var w = x"
  by (simp add: writes_on_def)

lemma visible_var [simp]: "w \<in> visible_writes \<sigma> t x \<Longrightarrow> var w = x"
  by (auto simp add: visible_writes_def)

lemma visible_writes_in_writes: "visible_writes \<sigma> t x \<subseteq> writes \<sigma>"
  using visible_writes_def writes_on_def by fastforce

definition "valid_fresh_ts \<sigma> w ts' \<equiv> tst w < ts' \<and> (\<forall> w' \<in> writes_on \<sigma> (var w). tst w < tst w' \<longrightarrow> ts' < tst w')"

definition "ts_oride m m' x \<equiv> if tst (m x) \<le> tst (m' x) then m' x else m x"

definition rev_app :: "'s \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> 't" (infixl ";;" 150)
  where
  "rev_app s f \<equiv> f s"


definition
  "update_thrView t nv \<sigma> \<equiv> \<sigma> \<lparr> thrView := (thrView \<sigma>)(t := nv)\<rparr>"

definition
  "update_modView w nv \<sigma> \<equiv> \<sigma> \<lparr> modView := (modView \<sigma>)(w := nv) \<rparr>"

definition
  "update_mods w nwr \<sigma> \<equiv> \<sigma> \<lparr> mods := (mods \<sigma>)(w := nwr)\<rparr> \<lparr>writes := writes \<sigma> \<union> {w}\<rparr>"

definition
  "add_cv w \<sigma> \<equiv> \<sigma> \<lparr> covered := covered \<sigma> \<union> {w}\<rparr>"

definition "syncing \<sigma> w b \<equiv> releasing \<sigma> w \<and> b"

lemma [simp]: "syncing \<sigma> w False = False"
  by (simp add: syncing_def)

lemma [simp]: "syncing \<sigma> w True = releasing \<sigma> w"
  by (simp add: syncing_def)

definition
  "read_trans t b w \<sigma>  \<equiv>
       let new_thr_idx = (thrView \<sigma> t)(var w := w) in
       let new_thr_idx' =
             if syncing \<sigma> w b then ts_oride new_thr_idx (modView \<sigma> w) else new_thr_idx in
          \<sigma> ;; update_thrView t new_thr_idx'"

lemma [simp]: "\<not> syncing \<sigma> w b \<Longrightarrow> thrView (read_trans t b w \<sigma>) t = (thrView \<sigma> t)(var w := w)"
  by (simp add: read_trans_def rev_app_def update_thrView_def)

lemma syncing_thrView_read_trans [simp]: "syncing \<sigma> w b \<Longrightarrow>
                     thrView (read_trans t b w \<sigma>) t = ts_oride ((thrView \<sigma> t)(var w := w)) (modView \<sigma> w)"
  by (simp add: read_trans_def rev_app_def update_thrView_def)


lemma [simp]: "t' \<noteq> t \<Longrightarrow> thrView (read_trans t b w \<sigma>) t' = (thrView \<sigma> t')"
  apply (simp add: read_trans_def rev_app_def update_thrView_def)
  by (metis fun_upd_other surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2))

lemma [simp]: "var w \<noteq> x \<Longrightarrow> b = False \<Longrightarrow> thrView (read_trans t b w \<sigma>) t x = thrView \<sigma> t x"
  by (simp add: read_trans_def rev_app_def update_thrView_def Let_def ts_oride_def)

lemma [simp]: "modView (read_trans t b w \<sigma>) = modView \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "mods (read_trans t b w \<sigma>) = mods \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "covered (read_trans t b w \<sigma>) = covered \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "writes (read_trans t b w \<sigma>) = writes \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "writes_on (read_trans t b w \<sigma>) x = writes_on \<sigma> x"
  apply(unfold writes_on_def)
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)


lemma [simp]: "value (read_trans t False w \<sigma>) x  = value \<sigma> x"
  apply(unfold value_def)
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)


definition
  "write_trans t b w v \<sigma> ts' \<equiv>
          \<sigma> ;; update_thrView t ((thrView \<sigma> t)(var w := (var w, ts')))
            ;; update_modView (var w, ts') ((thrView \<sigma> t)(var w := (var w, ts')))
            ;; update_mods (var w, ts') \<lparr> val = v, is_releasing = b\<rparr>"


lemma [simp]: "thrView (write_trans t b w v \<sigma> ts') t = (thrView \<sigma> t)(var w := (var w, ts'))"
  by (simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "t' \<noteq> t \<Longrightarrow> thrView (write_trans t b w v \<sigma> ts') t' = (thrView \<sigma> t')"
  by (simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' = (thrView \<sigma> t)(var w := (var w, ts'))"
  apply (simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse tst_def var_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' y = modView \<sigma> w' y"
  by (auto simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow> mods (write_trans t b w v \<sigma> ts') w' = \<lparr> val = v, is_releasing = b\<rparr>"
  apply (simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse tst_def var_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> mods (write_trans t b w v \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> mods (write_trans t b w v \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "covered (write_trans t b w v \<sigma> ts') = covered \<sigma>"
  by (simp add: write_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "writes (write_trans t b w v \<sigma> ts') = writes \<sigma> \<union> {(var w, ts')}"
  by(simp add: Let_def rev_app_def
                   write_trans_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "x = var w \<Longrightarrow> writes_on (write_trans t b w v \<sigma> ts') x = writes_on \<sigma> x \<union> {(var w, ts')}"
  apply(unfold writes_on_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  using Collect_cong by auto

lemma [simp]: "y \<noteq> var w \<Longrightarrow> writes_on (write_trans t b w v \<sigma> ts') y = writes_on \<sigma> y"
  apply(unfold writes_on_def)
  by(auto simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "w \<in> writes_on \<sigma> y \<Longrightarrow>  w \<in> writes_on (write_trans t b w' v \<sigma> ts') y"
  apply(unfold writes_on_def)
  by simp




definition "update_trans t w v' \<sigma> ts' \<equiv>
       let new_thr_idx = (thrView \<sigma> t)(var w := (var w, ts')) in
         let new_thr_idx' =
             if releasing \<sigma> w
             then
                 ts_oride new_thr_idx (modView \<sigma> w)
             else
                 new_thr_idx
             in
                 \<sigma> ;; update_thrView t new_thr_idx'
                   ;; update_modView (var w, ts') new_thr_idx'
                   ;; update_mods (var w, ts') \<lparr> val = v', is_releasing = True\<rparr>
                   ;; add_cv w"


definition "update_trans_a t w v' \<sigma> ts' \<equiv>
       let new_thr_idx = (thrView \<sigma> t)(var w := (var w, ts')) in
         let new_thr_idx' =
             if releasing \<sigma> w
             then
                 ts_oride new_thr_idx (modView \<sigma> w)
             else
                 new_thr_idx
             in
                 \<sigma> ;; update_thrView t new_thr_idx'
                   ;; update_modView (var w, ts') new_thr_idx'
                   ;; update_mods (var w, ts') \<lparr> val = v', is_releasing = False\<rparr>
                   ;; add_cv w"

definition "update_trans_r t w v' \<sigma> ts' \<equiv>
       let new_thr_idx = (thrView \<sigma> t)(var w := (var w, ts')) in
                 \<sigma> ;; update_thrView t new_thr_idx
                   ;; update_modView (var w, ts') new_thr_idx
                   ;; update_mods (var w, ts') \<lparr> val = v', is_releasing = True\<rparr>
                   ;; add_cv w"


definition "CAS t w cv nv' \<sigma> ts' \<equiv>
      if  w \<notin> covered \<sigma> \<and> value \<sigma> w = cv
      then
        (update_trans t w nv' \<sigma> ts', True)
      else
        (read_trans t False w \<sigma>, False)"

definition cas_step :: "T \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> surrey_state \<Rightarrow> surrey_state \<Rightarrow> bool"
  where
    "cas_step t l cv nv \<sigma> \<sigma>'\<equiv>
      \<exists> w ts'.
          w \<in> visible_writes \<sigma> t l
        \<and> w \<notin> covered \<sigma> \<comment>\<open> CK copied this line from Semyenuk artifact \<close>
        \<and> valid_fresh_ts \<sigma> w ts'
        \<and> \<sigma>' = fst(CAS t w cv nv \<sigma> ts')"

lemma [simp]: "\<not> releasing \<sigma> w \<Longrightarrow>
                     thrView (update_trans  t w v' \<sigma> ts') t = (thrView \<sigma> t)(var w := (var w, ts'))"
  by (simp add: Let_def rev_app_def update_modView_def update_mods_def update_thrView_def update_trans_def add_cv_def)

lemma [simp]: "\<not> releasing \<sigma> w \<Longrightarrow>
                     thrView (update_trans_a  t w v' \<sigma> ts') t = (thrView \<sigma> t)(var w := (var w, ts'))"
  by (simp add: Let_def rev_app_def update_modView_def update_mods_def update_thrView_def update_trans_a_def add_cv_def)

lemma [simp]: " releasing \<sigma> w \<Longrightarrow>
                  thrView (update_trans  t w v' \<sigma> ts') t = ts_oride ((thrView \<sigma> t)(var w := (var w, ts'))) (modView \<sigma> w)"
  by (auto simp add: Let_def update_trans_def add_cv_def rev_app_def update_modView_def update_mods_def update_thrView_def)

lemma [simp]: " releasing \<sigma> w \<Longrightarrow>
                  thrView (update_trans_a  t w v' \<sigma> ts') t = ts_oride ((thrView \<sigma> t)(var w := (var w, ts'))) (modView \<sigma> w)"
  by (auto simp add: Let_def update_trans_a_def add_cv_def rev_app_def update_modView_def update_mods_def update_thrView_def)


lemma [simp]: "thrView (update_trans_r  t w v' \<sigma> ts') t = (thrView \<sigma> t)(var w := (var w, ts'))"
  by (simp add: Let_def rev_app_def update_modView_def update_mods_def update_thrView_def update_trans_r_def add_cv_def)


lemma [simp]: "t' \<noteq> t \<Longrightarrow> thrView (update_trans  t w v' \<sigma> ts') t' = (thrView \<sigma> t')"
  by (simp add: Let_def update_trans_def add_cv_def rev_app_def update_modView_def update_mods_def update_thrView_def)


lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow>
             \<not> releasing \<sigma> w \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = (thrView \<sigma> t)(var w := (var w, ts'))"
  apply (simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse tst_def var_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow>
             releasing \<sigma> w \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = ts_oride ((thrView \<sigma> t)(var w := (var w, ts'))) (modView \<sigma> w)"
  apply (simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse tst_def var_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: Let_def fun_upd_idem_iff fun_upd_twist rev_app_def update_modView_def update_mods_def update_thrView_def update_trans_def add_cv_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> mods (update_trans t w v' \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> mods (update_trans t w v' \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow>
             mods (update_trans t w v' \<sigma> ts') w' = \<lparr> val = v', is_releasing = True\<rparr>"
  apply (simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse tst_def var_def)

lemma [simp]: "covered (update_trans t w v' \<sigma> ts')  = covered \<sigma> \<union> {w}"
  by (simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "writes (update_trans t w v' \<sigma> ts') = writes \<sigma> \<union> {(var w, ts')}"
 by (auto simp add: Let_def update_trans_def rev_app_def add_cv_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "x = var w \<Longrightarrow> writes_on (update_trans t w v' \<sigma> ts') x = writes_on \<sigma> x \<union> {(x, ts')}"
  apply(unfold writes_on_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  using Collect_cong by auto

lemma [simp]: "y \<noteq> var w \<Longrightarrow> writes_on (update_trans t w v' \<sigma> ts') y = writes_on \<sigma> y"
  apply(unfold writes_on_def)
  by(auto simp add: read_trans_def Let_def rev_app_def update_thrView_def)






definition step :: "T \<Rightarrow> action \<Rightarrow> surrey_state \<Rightarrow> surrey_state \<Rightarrow> bool"
  where
    "step t a \<sigma> \<sigma>'\<equiv>
       \<exists> w. w \<in> visible_writes \<sigma> t (avar a) \<and>
       (case a of
         Read b x v \<Rightarrow>
           v = value \<sigma> w \<and>
           \<sigma>' = read_trans t b w \<sigma>
       | Write b x v \<Rightarrow> \<exists> ts'.
           w \<notin> covered \<sigma> \<and>
           valid_fresh_ts \<sigma> w ts' \<and>
           \<sigma>' = write_trans t b w v \<sigma> ts'
       | Update x v v' \<Rightarrow> \<exists> ts'.
           v = value \<sigma> w \<and>
           w \<notin> covered \<sigma> \<and>
           valid_fresh_ts \<sigma> w ts' \<and>
           \<sigma>' = update_trans t w v' \<sigma> ts')
           "

lemma step_cases:
       "step t a \<sigma> \<sigma>'
          \<Longrightarrow>
        \<lbrakk>\<And> w b x v. \<sigma>' = read_trans t b w \<sigma> \<and> a = Read b x v \<and> w \<in> visible_writes \<sigma> t (avar a) \<and>
          v = value \<sigma> w \<Longrightarrow> P \<sigma> (read_trans t b w \<sigma>)\<rbrakk>
         \<Longrightarrow>
       \<lbrakk>\<And> w b x v ts'. \<sigma>' = write_trans t b w v \<sigma> ts' \<and> a = Write b x v \<and> w \<in> visible_writes \<sigma> t (avar a) \<and>
           w \<notin> covered \<sigma> \<and>
           valid_fresh_ts \<sigma> w ts'
           \<Longrightarrow> P \<sigma> (write_trans t b w v \<sigma> ts') \<rbrakk>
         \<Longrightarrow>
       \<lbrakk>\<And> w x v v' ts'. \<sigma>' = update_trans t w v' \<sigma> ts' \<and> a = Update x v v' \<and>
           w \<in> visible_writes \<sigma> t (avar a) \<and>
           v = value \<sigma> w \<and>
           w \<notin> covered \<sigma> \<and>
           valid_fresh_ts \<sigma> w ts'
           \<Longrightarrow> P \<sigma> (update_trans t w v' \<sigma> ts')\<rbrakk>
  \<Longrightarrow> P \<sigma> \<sigma>'"
  apply(simp add: step_def) apply(case_tac a) by auto

definition "WrX x v \<equiv> Write False x v"
definition "WrR x v \<equiv> Write True x v"
definition "RdX x v \<equiv> Read False x v"
definition "RdA x v \<equiv> Read True x v"

abbreviation WrX_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ [_ := _]\<^sub>_ _" [100,100,100,100,100])
where "\<sigma> [x := v]\<^sub>t \<sigma>' \<equiv> step t (WrX x v) \<sigma> \<sigma>'"

abbreviation WrR_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ [_ :=\<^sup>R _]\<^sub>_ _" [100,100,100,100,100])
where "\<sigma> [x :=\<^sup>R v]\<^sub>t \<sigma>' \<equiv> step t (WrR x v) \<sigma> \<sigma>'"

abbreviation RdX_state_abbr:: " surrey_state \<Rightarrow> V \<Rightarrow> L \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ [_ \<leftarrow> _]\<^sub>_ _" [100,100,100,100,100])
where "\<sigma> [r \<leftarrow> x]\<^sub>t \<sigma>' \<equiv> step t (RdX x r) \<sigma> \<sigma>'"

abbreviation RdA_state_abbr:: " surrey_state \<Rightarrow> V \<Rightarrow> L \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ [_ \<leftarrow>\<^sup>A _]\<^sub>_ _" [100,100,100,100,100])
where "\<sigma> [r \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>' \<equiv> step t (RdA x r) \<sigma> \<sigma>'"

abbreviation Up_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ RMW[_, _, _]\<^sub>_ _" [100,100,100,100,100,100])
where "\<sigma> RMW[x, u, v]\<^sub>t \<sigma>' \<equiv> step t (Update x u v) \<sigma> \<sigma>'"

abbreviation Up_A_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ RMW\<^sup>A[_, _, _]\<^sub>_ _" [100,100,100,100,100,100])
where "\<sigma> RMW\<^sup>A[x, u, v]\<^sub>t \<sigma>' \<equiv> step t (Update x u v) \<sigma> \<sigma>'"

abbreviation Up_R_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ RMW\<^sup>R[_, _, _]\<^sub>_ _" [100,100,100,100,100,100])
where "\<sigma> RMW\<^sup>R[x, u, v]\<^sub>t \<sigma>' \<equiv> step t (Update x u v) \<sigma> \<sigma>'"

abbreviation Swap_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool"
  ("_ SWAP[_, _]\<^sub>_ _" [100,100,100,100,100])
where "\<sigma> SWAP[x, v]\<^sub>t \<sigma>' \<equiv> \<exists>u . step t (Update x u v) \<sigma> \<sigma>'"

definition "initial_state \<sigma> I \<equiv>
                 \<exists> F . writes \<sigma> = {(x, F x) | x. True} \<and>
                       (\<forall> t x. thrView \<sigma> t x = (x, F x)) \<and>
                       (\<forall> w x. modView \<sigma> w x = (x, F x)) \<and>
                       (\<forall> w. mods \<sigma> w = \<lparr> val = I (var w), is_releasing = False \<rparr>) \<and>
                       covered \<sigma> = {}"

definition "wfs \<sigma> \<equiv>
      (\<forall> t x. thrView \<sigma> t x \<in> writes_on \<sigma> x) \<and>
      (\<forall> w x. modView \<sigma> w x \<in> writes_on \<sigma> x) \<and>
      (\<forall> x. finite(writes_on \<sigma> x)) \<and>
      (\<forall> w. w \<in> writes \<sigma> \<longrightarrow> modView \<sigma> w (var w) = w) \<and>
      covered \<sigma> \<subseteq> writes \<sigma>"

definition "lastWr \<sigma> x \<equiv> (x, Max (tst`(writes_on \<sigma> x)))"

definition "p_obs \<sigma> t x u \<equiv> \<exists> w. w \<in> visible_writes \<sigma> t x \<and> u = value \<sigma> w"

definition "d_obs \<sigma> view x u \<equiv> view x = lastWr \<sigma> x \<and> value \<sigma> (lastWr \<sigma> x) = u"

definition "d_obs_t \<sigma> t x u \<equiv> d_obs \<sigma> (thrView \<sigma> t) x u"

definition "c_obs \<sigma> x u t y v \<equiv>
              \<forall> w \<in> visible_writes \<sigma> t x. value \<sigma> w = u \<longrightarrow>
                         d_obs \<sigma> (modView \<sigma> w) y v \<and>
                         releasing \<sigma> w"

abbreviation p_obs_abbr:: "nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[_ \<approx>\<^sub>_ _] _" [100, 100, 100, 100])
  where "[x \<approx>\<^sub>t u] \<sigma> \<equiv> p_obs \<sigma> t x u"

abbreviation d_obs_abbr:: "nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> surrey_state \<Rightarrow> bool" ("[_ =\<^sub>_ _] _" [100, 100, 100, 100])
  where "[x =\<^sub>t u] \<sigma> \<equiv> d_obs_t \<sigma> t x u"

abbreviation c_obs_abbr:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> surrey_state \<Rightarrow> bool" ("[_ = _]\<^sub>_\<lparr>_ = _ \<rparr> _" [100, 100, 100, 100, 100, 100])
  where "[x = u]\<^sub>t\<lparr>y = v\<rparr> \<sigma> \<equiv> c_obs \<sigma> x u t y v"

definition "covered_v \<sigma> x v \<equiv>
  \<forall> w .
      w \<in> writes_on \<sigma> x
    \<and> w \<notin> covered \<sigma>
    \<longrightarrow> w = lastWr \<sigma> x
      \<and> value \<sigma> w = v"

abbreviation covered_v_abbr:: "L \<Rightarrow> V  \<Rightarrow> surrey_state \<Rightarrow> bool" ("cvd[_, _] _" [100, 100,100])
  where "cvd[x, u] \<sigma> \<equiv> covered_v \<sigma> x u"


definition "mo w w'\<equiv> var(w) = var(w') \<and> tst(w) < tst(w')"

definition "enc \<sigma> view x u \<equiv> \<exists> w . w \<in> writes_on \<sigma> x \<and> tst(w) \<le> tst(view x) \<and> value \<sigma> w = u"

definition "enc_t \<sigma> t x u \<equiv>  enc \<sigma> (thrView \<sigma> t) x u"

definition "p_vorder \<sigma> u x v \<equiv> \<exists> w w'.  w \<in> writes_on \<sigma> x  \<and>  w' \<in> writes_on \<sigma> x \<and>
                                        value \<sigma> w = u \<and> value \<sigma> w' = v \<and>
                                        mo w w' "

definition "d_vorder \<sigma> u x v \<equiv> (\<forall> w w'.  w \<in> writes_on \<sigma> x  \<and>  w' \<in> writes_on \<sigma> x \<and>
                                        value \<sigma> w = u \<and> value \<sigma> w' = v \<longrightarrow>
                                        mo w w') \<and> p_vorder \<sigma> u x v"

definition "init_val \<sigma> x v \<equiv>
  \<exists> w . w \<in> writes_on \<sigma> x \<and>
        (\<forall>w'\<in> writes_on \<sigma> x .  w \<noteq> w' \<longrightarrow>  mo w w') \<and>
        value \<sigma> w = v"

definition "amo \<sigma> x u \<equiv> \<not> p_vorder \<sigma> u x u"

definition "no_val \<sigma> x i u \<equiv> init_val \<sigma> x i \<and> \<not> p_vorder \<sigma> i x u"

definition "last_val \<sigma> x u i \<equiv>
                init_val \<sigma> x i \<and> p_vorder \<sigma> i x u
                \<and> (\<forall> w. w \<noteq> u \<longrightarrow> \<not> p_vorder \<sigma> u x w)"



abbreviation p_vorder_abbr:: "V  \<Rightarrow> L \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[_ \<leadsto>\<^sub>_ _] _" [100,100,100,100])
  where "[u \<leadsto>\<^sub>x v] \<sigma> \<equiv> p_vorder \<sigma> u x v"

abbreviation d_vorder_abbr:: "V  \<Rightarrow> L \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[_ \<hookrightarrow>\<^sub>_ _] _" [100,100,100,100])
  where "[u \<hookrightarrow>\<^sub>x v] \<sigma> \<equiv> d_vorder \<sigma> u x v"

abbreviation amo_abbr:: "L \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[\<one>\<^sub>_ _] _" [100,100,100])
  where "[\<one>\<^sub>x u] \<sigma> \<equiv> amo \<sigma> x u"

abbreviation no_abbr:: "L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> surrey_state \<Rightarrow> bool" ("[\<zero>\<^sub>_ _]\<^sub>_ _" [100,100,100,100])
  where "[\<zero>\<^sub>x u]\<^sub>i \<sigma> \<equiv> no_val \<sigma> x i u"

abbreviation enc_abbr:: "L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("[en _ _]\<^sub>_ _" [100,100,100,100])
  where "[en x u]\<^sub>t \<sigma> \<equiv> enc_t \<sigma> t x u"

abbreviation last_abbr:: "L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("[last _ _ _]\<^sub>_ _" [100, 100,100,100,100])
  where "[last x i u]\<^sub>t \<sigma> \<equiv> last_val \<sigma> x u i"

abbreviation init_abbr:: "L \<Rightarrow> V  \<Rightarrow> surrey_state \<Rightarrow> bool" ("[init _ _] _" [100, 100,100])
  where "[init x v] \<sigma> \<equiv> init_val \<sigma> x v"



lemma initially_write_unique: "initial_state \<sigma> I \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> w' \<in> writes_on \<sigma> x \<Longrightarrow> w = w'"
  apply(unfold initial_state_def writes_on_def) by auto

lemma initial_wfs: assumes "initial_state \<sigma> I"  shows "wfs \<sigma>"
  apply(simp add: initial_state_def wfs_def)
  apply(rule conjI)
  using assms writes_on_def
   apply (smt CollectI fst_conv initial_state_def var_def)
  apply(rule conjI)
  using assms writes_on_def initial_state_def apply simp
  apply (smt CollectI fst_conv initial_state_def var_def writes_on_def)
  apply rule using initially_write_unique[OF assms(1)]
  apply (smt CollectI Collect_cong finite.emptyI finite.insertI insert_compr not_finite_existsD singletonD writes_on_def)
    apply(rule conjI)
  apply (smt CollectD Pair_inject assms initial_state_def)
  using assms initial_state_def by fastforce


lemma [simp]: "wfs \<sigma> \<Longrightarrow> writes_on \<sigma> x \<noteq> {}"
  apply(simp add: wfs_def)
  by (metis empty_iff)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> finite(writes_on \<sigma> x)"
  by(simp add: wfs_def)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> thrView \<sigma> t x \<in> writes_on \<sigma> x"
  by(simp add: wfs_def)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> modView \<sigma> w x \<in> writes_on \<sigma> x"
  using wfs_def by blast


lemma [simp]: "wfs \<sigma> \<Longrightarrow> modView (read_trans t b w \<sigma>) w x \<in> writes_on (read_trans t b w \<sigma>) x"
  by auto

lemma [simp]: "wfs \<sigma> \<Longrightarrow> writes_on \<sigma> x =  writes_on (read_trans t b w \<sigma>) x"
  by auto


lemma last_write_max: "wfs \<sigma> \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> tst w \<le> tst (lastWr \<sigma> x)"
  by(simp add: lastWr_def)
end
