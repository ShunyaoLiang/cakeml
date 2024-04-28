(*
  Automate verification of the property that a Pancake program does not access
  memory that is out of bounds.
*)

(* Below is a glossary of identifiers used in this file.
     * addr:  Used for memory addresses. Pluralised as addrs.
     * ctxt:  Short for "context".
     * m:     Stands for "memory". Pluralised as ms.
     * s:     Stands for "state". It refers to both the state in panSemTheory,
              and the state used by working_set. Pluralised also as s.
     * v:     1. Used for Pancake variable names. 2. A Pancake value.
     * ws:    1. Short for "working set". Here, it is usually an upper bound on
              the range of heap addresses that a Pancake program or expression
              will access. Thanks COMP3891! 2. Plural of w.
   *)

open preamble panLangTheory panSemTheory;

val _ = new_theory "panWorkSet";


(* A "nice" modification of the Pancake functional semantics that does not check
   for out-of-bounds memory accesses. *)

(* The type variables in the types of the functions we are substituting get
   instatiated, so we have to instatiate them the same way. The naming
   convention originates from spec64 in compiler64ProgTheory. *)
val specffi = inst [beta |-> Type `:'ffi`];

(* Remove the universal quanitifications in each equation of a specification.
   This is necessary because definition mechanisms expect to add the
   universal quantifiers themselves. *)
fun spec_eqn_strip_forall tm =
  list_mk_conj (map (snd o strip_forall) (strip_conj tm));

val mem_load_ty = specffi (ty_antiq (type_of (Term `mem_load`)));
val mem_loads_ty = specffi (ty_antiq (type_of (Term `mem_loads`)));

Definition nice_mem_load_def:
  (nice_mem_load One addr dm m = SOME (Val (m addr))) ∧
  ^(spec_eqn_strip_forall
    (subst
      [ Term `mem_load:^mem_load_ty`   |-> Term `nice_mem_load:^mem_load_ty`
      , Term `mem_loads:^mem_loads_ty` |-> Term `nice_mem_loads:^mem_loads_ty` ]
      (concl mem_load_def)))
Termination
  wf_rel_tac `measure (λx. case x of
                             | (INR (shapes, _)) => list_size shape_size shapes
                             | (INL (shapes, _)) => shape_size shapes)`
End

Definition nice_mem_load_byte_def:
  nice_mem_load_byte (m:'a word -> 'a word_lab) (dm:'a word set) be w =
    case m (byte_align w) of
      | Label _ => NONE
      | Word v  => SOME (get_byte w v be)
End

val eval_ty = specffi (ty_antiq (type_of (Term `eval`)));

Definition nice_eval_def:
  ^(spec_eqn_strip_forall
    (subst
      [ Term `eval :^eval_ty` |-> Term `nice_eval :^eval_ty`,
        Term `mem_load`       |-> Term `nice_mem_load`,
        Term `mem_load_byte`  |-> Term `nice_mem_load_byte` ]
      (concl eval_def)))
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
End

Definition nice_mem_store_byte_def:
  nice_mem_store_byte (m:'a word -> 'a word_lab) (dm:'a word set) be w b =
    case m (byte_align w) of
     | Word v => SOME ((byte_align w =+ Word (set_byte w b v be)) m)
     | Label _ => NONE
End

Definition nice_mem_store_def:
  nice_mem_store (addr:'a word) (w:'a word_lab) (dm:'a word set) m =
    SOME ((addr =+ w) m)
End

val mem_stores_ty = specffi (ty_antiq (type_of (Term `mem_stores`)));

Definition nice_mem_stores_def:
  ^(spec_eqn_strip_forall
    (subst
      [ Term `mem_stores:^mem_stores_ty` |->
        Term `nice_mem_stores:^mem_stores_ty`,
        Term `mem_store`                 |-> Term `nice_mem_store` ]
      (concl mem_stores_def)))
End

val evaluate_ty = specffi (ty_antiq (type_of (Term `evaluate`)));

Definition nice_evaluate_def:
  nice_evaluate (While e c, s) = evaluate (While e c, s) ∧
  nice_evaluate (Call rtyp e es, s) = evaluate (Call rtyp e es, s) ∧
  nice_evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s) =
    evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s) ∧
  ^(spec_eqn_strip_forall
    (subst
      [ Term `evaluate:^evaluate_ty` |-> Term `nice_evaluate:^evaluate_ty`,
        Term `eval`                  |-> Term `nice_eval`,
        Term `mem_stores`            |-> Term `nice_mem_stores`,
        Term `mem_store_byte`        |-> Term `nice_mem_store_byte` ]
      (concl evaluate_def)))
End


(* Find an upper bound on the working set of a Pancake program. *)

Datatype:
  context = <| code      : funname |-> ((varname # shape) list # ('a panLang$prog)) ;
               be        : bool ;
               base_addr : 'a word ;
               ffi       : 'ffi itself |>
End

Definition context_from_state_def:
  context_from_state (s:('a, 'ffi) panSem$state) =
    <| code := s.code ; be := s.be ; base_addr := s.base_addr ; ffi := (:'ffi) |>
End

Type state = (Type ‘:(varname |-> 'a v) # ('a word -> 'a word_lab)’)

Definition value_range_def:
  value_range (ctxt:('a, 'ffi) context) e sts =
    let state (l, m) =
        <| code      := ctxt.code ;
           locals    := l ;
           memory    := m ;
           memaddrs  := UNIV ;
           be        := ctxt.be ;
           ffi       := (ARB : 'ffi ffi_state) ;
           base_addr := ctxt.base_addr |>
    in { x | SOME x ∈ IMAGE (λst. eval (state st) e) sts }
End

Definition working_set_mem_load_def:
  working_set_mem_load sh addr =
  (case sh of
     One => {addr}
   | Comb shs => working_set_mem_loads shs addr) ∧
  working_set_mem_loads [] addr = {} ∧
  working_set_mem_loads (sh::shs) addr =
    working_set_mem_load sh addr ∪
    working_set_mem_loads shs (addr + bytes_in_word * n2w (size_of_shape sh))
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL (sh, addr) => shape_size sh
                           | INR (shs, addr) => list_size shape_size shs)’
End

Definition working_set_mem_stores_def:
  working_set_mem_stores a [] = {a} ∧
  working_set_mem_stores a (w::ws) =
  {a} ∪ working_set_mem_stores (a + bytes_in_word) ws
End

Definition working_set_exp_def:
  working_set_exp ctxt ((Const w):'a panLang$exp) (sts:'a state set) = ({}:'a word set) ∧
  working_set_exp ctxt (Var v) sts = {} ∧
  working_set_exp ctxt (Label fname) sts = {}  ∧
  working_set_exp ctxt (panLang$Struct es) sts =
    FOLDR (λe ws. ws ∪ working_set_exp ctxt e sts) {} es ∧
  working_set_exp ctxt (Field index e) sts = working_set_exp ctxt e sts ∧
  working_set_exp ctxt (Load shape src) sts =
    working_set_exp ctxt src sts ∪
    BIGUNION { working_set_mem_load shape addr | ValWord addr ∈ value_range ctxt src sts } ∧
  working_set_exp ctxt (LoadByte e) sts =
    (let addrs = { addr | ValWord addr ∈ value_range ctxt e sts } in
      working_set_exp ctxt e sts ∪ addrs) ∧
  working_set_exp ctxt (Op op es) sts =
    FOLDR (λe ws. ws ∪ working_set_exp ctxt e sts) {} es ∧
  working_set_exp ctxt (Panop op es) sts =
    FOLDR (λe ws. ws ∪ working_set_exp ctxt e sts) {} es ∧
  working_set_exp ctxt (Cmp cmp e1 e2) sts =
    working_set_exp ctxt e1 sts ∪ working_set_exp ctxt e2 sts ∧
  working_set_exp ctxt (Shift sh e n) sts = working_set_exp ctxt e sts ∧
  working_set_exp ctxt BaseAddr sts = {}
Termination
  WF_REL_TAC ‘measure (exp_size ARB o (FST o SND))’
End

Definition working_set_prog_def:
  working_set_prog ctxt Skip s = ({}, s) ∧
  working_set_prog ctxt (Dec v e p) sts =
  (let ws = working_set_exp ctxt e sts;
       sts' = { (l |+ (v, val), m)
              | (l, m) ∈ sts ∧ val ∈ value_range ctxt e sts };
       (ws', sts'') = working_set_prog ctxt p sts' in
     (ws ∪ ws', sts'')) ∧
  working_set_prog ctxt (Assign v e) sts =
  (let ws = working_set_exp ctxt e sts and
       sts' = { (l |+ (v, val), m)
              | (l, m) ∈ sts ∧ val ∈ value_range ctxt e sts} in
     (ws, sts')) ∧
  working_set_prog ctxt (Store dst src) sts =
  (let ws = working_set_exp ctxt dst sts and
       ws' = working_set_exp ctxt src sts and
       addrs = { addr | ValWord addr ∈ value_range ctxt dst sts } and
       vals = value_range ctxt src sts;
       ws'' = BIGUNION { working_set_mem_stores addr (flatten val)
                       | addr ∈ addrs ∧ val ∈ vals } and
       sts' = { (l, THE (mem_stores addr (flatten val) UNIV m))
       | (l, m) ∈ sts ∧ ValWord addr ∈ value_range ctxt dst sts ∧
         val ∈ vals } in
     (ws ∪ ws' ∪ ws'', sts')) ∧
  working_set_prog ctxt (StoreByte dst src) sts =
  (let ws = working_set_exp ctxt dst sts and
       ws' = working_set_exp ctxt src sts and
       addrs = { addr | ValWord addr ∈ value_range ctxt dst sts };
       sts' = { (l, THE (mem_store_byte m UNIV ctxt.be addr (w2w w)))
              | (l, m, addr, w)
              | (l, m) ∈ sts ∧ addr ∈ addrs ∧
                ValWord w ∈ value_range ctxt src sts } in
     (ws ∪ ws' ∪ IMAGE byte_align addrs, sts')) ∧
  working_set_prog ctxt (Seq c1 c2) s =
  (let (ws, s') = working_set_prog ctxt c1 s;
       (ws', s'') = working_set_prog ctxt c2 s' in
     (ws ∪ ws', s'')) ∧
  working_set_prog ctxt (If e c1 c2) s =
  (let ws = working_set_exp ctxt e s and
       (ws', s') = working_set_prog ctxt c1 s and
       (ws'', s'') = working_set_prog ctxt c2 s in
     (ws ∪ ws' ∪ ws'', s' ∪ s'')) ∧
  (* For the purposes of defining the major theorem below, this is sound because
     the nice semantics are the same as the semantics for While. This saves us
     a huge headache, but restricts working_set_prog to finding the bound up until
     the next While loop. *)
  working_set_prog ctxt (While _ _) s = ({}, s) ∧
  working_set_prog ctxt Break s = ({}, s) ∧
  working_set_prog ctxt Continue s = ({}, s) ∧
  (* See the note above on the While case. *)
  working_set_prog ctxt (Call _ _ _) s = ({}, s) ∧
  (* See the note above on the While case. *)
  working_set_prog ctxt (ExtCall _ _ _ _ _) s = ({}, s) ∧
  working_set_prog ctxt (Return e) s = (working_set_exp ctxt e s, s) ∧
  working_set_prog ctxt (Raise _ e) s = (working_set_exp ctxt e s, s) ∧
  working_set_prog ctxt Tick s = ({}, s)
End

Definition working_set_def:
  working_set p s = FST (working_set_prog (context_from_state s) p {(s.locals, s.memory)})
End


(* Prove the major theorem: that if our bound on the working set of a Pancake
   program is within the allocated heap, we may replace the semantics with the
   nicer semantics. *)

Theorem OPT_MMAP_exist:
  ∀xs es f e.
    SOME xs = OPT_MMAP f es ∧ MEM e es ⇒
    ∃x. f e = SOME x
Proof cheat
QED

Theorem mem_load_mono:
  ∀sh dm dm' w m.
    dm ⊆ dm' ⇒
    mem_load sh w dm m = mem_load sh w dm' m
Proof cheat
QED

Theorem eval_value_range:
  ∀s e x.
    eval s e = SOME x ⇒
    x ∈ value_range (context_from_state s) e {(s.locals,s.memory)}
Proof
  recInduct eval_ind
  >> rpt strip_tac
  >> gvs[eval_def, value_range_def, context_from_state_def, AllCaseEqs()]
  >- (pop_assum $ assume_tac o GSYM >> simp[]
      >> match_mp_tac OPT_MMAP_cong
      >> rw[]
      >> imp_res_tac OPT_MMAP_exist
      >> metis_tac[])
  >- (EXISTS_TAC “(Struct vs)” >> rw[])
  >- (EXISTS_TAC “(ValWord w)” >> rw[]
      >> fs[mem_load_def]
      >> cheat)
  >> cheat
QED

Theorem working_set_prog_mono:
  ∀s1 s2. s1 ⊆ s2 ⇒
          FST (working_set_prog ctxt p s1) ⊆ FST (working_set_prog ctxt p s2)
Proof cheat
QED

Theorem evaluate_preserves_state:
  ∀p s res s1.
    evaluate (p, s) = (res, s1) ⇒
    s1.code = s.code ∧
    s1.be = s.be ∧
    s1.base_addr = s.base_addr ∧
    s1.memaddrs = s.memaddrs
Proof
  recInduct panSemTheory.evaluate_ind
  >> rpt conj_tac
  >> rpt gen_tac
  >> rpt $ disch_then strip_assume_tac
  >> rpt gen_tac
  >> rpt $ disch_then strip_assume_tac
  >~ [‘While’]
  >- (qpat_x_assum ‘evaluate (While e c,s) = (res, s1)’ mp_tac
      >> once_rewrite_tac[evaluate_def]
      >> TOP_CASE_TAC >> fs[]
      >> TOP_CASE_TAC >> fs[]
      >> TOP_CASE_TAC >> fs[]
      >> strip_tac
      >> pairarg_tac >> gvs[]
      >> Cases_on ‘c' = 0w’
      >> gs[]
      >> Cases_on ‘s.clock’
      >> gvs[empty_locals_def, context_from_state_def]
      >> ‘SUC n ≠ 0’ by rw[]
      >> gvs[]
      >> Cases_on ‘res'’
      >- gvs[context_from_state_def, dec_clock_def]
      >- (Cases_on ‘x’ >> gvs[context_from_state_def, dec_clock_def, empty_locals_def]))
  >> fs[evaluate_def]
  >> gvs[AllCaseEqs(), empty_locals_def, context_from_state_def, dec_clock_def, empty_locals_def, set_var_def]
  >> rpt (pairarg_tac >> gvs[])
  >> gvs[AllCaseEqs()]
QED

Theorem evaluate_preserves_context:
  ∀p s res s1. evaluate (p, s) = (res, s1) ⇒
               context_from_state s1 = context_from_state s
Proof rw[] >> fs[context_from_state_def] >> metis_tac[evaluate_preserves_state]
QED

Theorem working_set_prog_Seq:
  ∀p c1 c2 ctxt s s' dm.
    p = Seq c1 c2 ∧ FST (working_set_prog ctxt p s) ⊆ dm ∧
    s' = SND (working_set_prog ctxt c1 s) ⇒
    FST (working_set_prog ctxt c1 s) ⊆ dm ∧
    FST (working_set_prog ctxt c2 s') ⊆ dm
Proof rw[] >> fs[working_set_prog_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem working_set_prog_If:
  ∀p e c1 c2 ctxt s dm.
    p = If e c1 c2 ∧ working_set p s ⊆ s.memaddrs ⇒
    working_set c1 s ⊆ s.memaddrs ∧
    working_set c2 s ⊆ s.memaddrs
Proof
  rw[working_set_def]
  >> fs[working_set_prog_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem mem_store_nice:
  ∀w c dm m. c ∈ dm ⇒ mem_store c w dm m = nice_mem_store c w dm m
Proof rw[mem_store_def, nice_mem_store_def]
QED

Theorem mem_stores_nice:
  ∀ws c dm m. working_set_mem_stores c ws ⊆ dm ⇒
              mem_stores c ws dm m = nice_mem_stores c ws dm m
Proof
  Induct
  >> simp[mem_stores_def, nice_mem_stores_def, working_set_mem_stores_def]
  >> rw[mem_store_nice]
QED

Theorem mem_store_byte_nice:
  ∀m dm be w b.
     byte_align w ∈ dm ⇒
     mem_store_byte m dm be w b = nice_mem_store_byte m dm be w b
Proof
  rw[mem_store_byte_def, nice_mem_store_byte_def]
  >> TOP_CASE_TAC >> gvs[]
QED

Theorem working_set_prog_over_evaluate:
  ∀c1 s s1 sts sts'.
    evaluate (c1,s) = (NONE,s1) ∧
    sts' = SND (working_set_prog (context_from_state s) c1 {(s.locals,s.memory)}) ⇒
    {(s1.locals,s1.memory)} ⊆ sts'
Proof
  recInduct panSemTheory.evaluate_ind
  >> rpt strip_tac
  >> simp[working_set_prog_def]
  >> cheat
QED

Theorem working_set:
  ∀p s.
    working_set p s ⊆ s.memaddrs ⇒
    evaluate (p, s) = nice_evaluate (p, s)
Proof
  recInduct panSemTheory.evaluate_ind
  >> rpt strip_tac
  >> simp[Once nice_evaluate_def]
  >> simp[evaluate_def]
  (* Dec case *)
  >- (rpt (TOP_CASE_TAC >> gvs[])
      >> rpt (pairarg_tac >> gvs[])
      >> fs[working_set_def]
      >> fs[working_set_prog_def]
      >> rpt (pairarg_tac >> gvs[])
      >> ‘context_from_state (s with locals := s.locals |+ (v, x)) = context_from_state s’
                             by rw[context_from_state_def] >> gvs[]
      >> ‘x ∈ value_range (context_from_state s) e {(s.locals, s.memory)}’
            by metis_tac[eval_value_range]
      >> Q.ABBREV_TAC ‘A = {(s.locals |+ (v,x),s.memory)}’
      >> Q.MATCH_ASSUM_ABBREV_TAC ‘working_set_prog (context_from_state s) prog B = (ws',sts'')’
      >> ‘A ⊆ B’ by (gvs[Abbr ‘A’, Abbr ‘B’, GSPECIFICATION, IN_DEF, SUBSET_DEF]
                     (* I could not explain to you why this type annotation is necessary. *)
                     >> EXISTS_TAC “(s.locals, x, s.memory)
                                    :((mlstring |-> 'a v) # 'a v # ('a word -> 'a word_lab))”
                     >> gvs[])
      >> ‘FST (working_set_prog (context_from_state s) prog A) ⊆
          FST (working_set_prog (context_from_state s) prog B)’
        by metis_tac[working_set_prog_mono]
      >> ‘FST (working_set_prog (context_from_state s) prog B) ⊆ s.memaddrs’
        by rw[]
      >> metis_tac[SUBSET_TRANS])
  (* Store case *)
  >- (TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> gs[working_set_def, working_set_prog_def]
      >> imp_res_tac eval_value_range
      >> imp_res_tac BIGUNION_SUBSET
      >> qmatch_assum_abbrev_tac ‘∀Y. Y ∈ Z ⇒ Y ⊆ s.memaddrs’
      >> ‘working_set_mem_stores c (flatten x) ∈ Z’
        by (gvs[Abbr ‘Z’, GSPECIFICATION, IN_DEF, SUBSET_DEF]
            >> EXISTS_TAC “(c, x):('a word # 'a v)”
            >> gvs[])
      >> ‘working_set_mem_stores c (flatten x) ⊆ s.memaddrs’
        by metis_tac[]
      >> metis_tac[mem_stores_nice])
  (* StoreByte case *)
  >- (TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> TOP_CASE_TAC >> gvs[]
      >> gs[working_set_def, working_set_prog_def]
      >> imp_res_tac eval_value_range
      >> fs[IMAGE_DEF]
      >> ‘{byte_align c} ⊆ {byte_align x | ValWord x ∈ value_range (context_from_state s) dst {(s.locals,s.memory)}}’
        by (rw[] >> EXISTS_TAC “c:'a word” >> rw[])
      >> ‘{byte_align c} ⊆ s.memaddrs’ by metis_tac[SUBSET_TRANS]
      >> ‘byte_align c ∈ s.memaddrs’ by gvs[]
      >> metis_tac[mem_store_byte_nice])
  (* Seq case *)
  >- (fs[working_set_def]
      >> imp_res_tac working_set_prog_Seq >> rw[]
      >> rpt (pairarg_tac >> gvs[]) >> rw[]
      >> ‘context_from_state s1 = context_from_state s’
         by metis_tac[evaluate_preserves_context] >> gvs[]
      >> ‘s1.memaddrs = s.memaddrs’ by metis_tac[evaluate_preserves_state] >> gvs[]
      >> ‘{(s1.locals, s1.memory)} ⊆
          SND (working_set_prog (context_from_state s) c1 {(s.locals, s.memory)})’
        by metis_tac[working_set_prog_over_evaluate]
      >> ‘FST (working_set_prog (context_from_state s) c2 {(s1.locals, s1.memory)}) ⊆
          FST (working_set_prog (context_from_state s) c2
                                (SND (working_set_prog (context_from_state s) c1
                                                       {(s.locals, s.memory)})))’
        by metis_tac[working_set_prog_mono]
      >> ‘FST (working_set_prog (context_from_state s) c2 {(s1.locals, s1.memory)}) ⊆ s.memaddrs’
        by metis_tac[SUBSET_TRANS]
      >> metis_tac[])
  (* If case *)
  >- (imp_res_tac working_set_prog_If >> rw[]
      >> rpt (TOP_CASE_TAC >> gvs[]))
QED

val workset_tac = DEP_PURE_ONCE_REWRITE_TAC [working_set] >> conj_tac;

val _ = export_theory ();


(*
Definition working_set_prog_def:
  working_set_prog (Skip:'a panLang$prog) (ctxt:('a, 'ffi) context) = (ctxt, {}) ∧
  working_set_prog (Dec v e p) ctxt =
    (let ws = working_set_exp e ctxt and
         values = range e ctxt;
         lm = { (locals |+ (v, value), memory)
              | (locals, memory) ∈ ctxt.locals_memory ∧ value ∈ values };
         ctxt' = ctxt with locals_memory := lm;
         (ctxt'', ws') = working_set_prog p ctxt' in
      (ctxt'', ws ∪ ws')) ∧
  working_set_prog (Assign v e) ctxt =
    (let ws = working_set_exp e ctxt and
         values = range e ctxt;
         lm = { (locals |+ (v, value), memory)
              | (locals, memory) ∈ ctxt.locals_memory ∧ value ∈ values } in
      (ctxt with locals_memory := lm, ws)) ∧
  working_set_prog (Store dst src) ctxt =
    (let ws = working_set_exp dst ctxt and
         ws' = working_set_exp src ctxt and
         addrs = { addr | ValWord addr ∈ range dst ctxt } and
         values = range src ctxt;
         lm = { (locals, THE (mem_stores addr (flatten value) UNIV memory))
              | (locals, memory) ∈ ctxt.locals_memory ∧ addr ∈ addrs ∧
                value ∈ values} in
      (ctxt with locals_memory := lm, ws ∪ ws' ∪ addrs)) ∧
  working_set_prog (StoreByte dst src) ctxt =
    (let ws = working_set_exp dst ctxt and
         ws' = working_set_exp src ctxt and
         addrs = { addr | ValWord addr ∈ range dst ctxt } and
         ws = { w | ValWord w ∈ range src ctxt };
         lm = { (locals, THE (mem_store_byte memory UNIV ctxt.be addr (w2w w)))
              | locals, memory, addr, w
              | (locals, memory) ∈ ctxt.locals_memory ∧ addr ∈ addrs ∧
                w ∈ ws} in
      (ctxt with locals_memory := lm, ws ∪ ws' ∪ addrs)) ∧
  working_set_prog (Seq c1 c2) ctxt =
    (let (ctxt', ws) = working_set_prog c1 ctxt;
        (ctxt'', ws') = working_set_prog c2 ctxt' in
      (ctxt'', ws ∪ ws')) ∧
  working_set_prog (If e c1 c2) ctxt =
    (let ws = working_set_exp e ctxt and
        (ctxt', ws') = working_set_prog c1 ctxt and
        (ctxt'', ws'') = working_set_prog c2 ctxt in
      (context_union ctxt' ctxt'', ws ∪ ws' ∪ ws'')) ∧
  working_set_prog (While _ _) ctxt = (ctxt, {}) ∧
  working_set_prog Break ctxt = (ctxt, {}) ∧
  working_set_prog Continue ctxt = (ctxt, {}) ∧
  (* See the note above on the While case. *)
  working_set_prog (Call _ _ _) ctxt = (ctxt, {}) ∧
  (* See the note above on the While case. *)
  working_set_prog (ExtCall _ _ _ _ _) ctxt = (ctxt, {}) ∧
  working_set_prog (Return e) ctxt = (ctxt, working_set_exp e ctxt) ∧
  working_set_prog (Raise eid e) ctxt = (ctxt, working_set_exp e ctxt) ∧
  working_set_prog Tick ctxt = (ctxt, {})
End



Theorem working_set_exp:
  ∀s e.
    working_set_exp (context_from_state s) e {(s.locals, s.memory)} ⊆ s.memaddrs ⇒
    eval s e = nice_eval s e
Proof
  recInduct panSemTheory.eval_ind
  >> rpt strip_tac
  >> simp[eval_def, nice_eval_def]
  >- (FULL_CASE_TAC >> gvs[] >> cheat)
  >> cheat
     (* OPT_MMAP_CONG *)
QED
*)

(*


Theorem IN_SINGLETON_SUBSET:
  ∀a X. a ∈ X ⇒ {a} ⊆ X
Proof rw[]
QED

(* The types representing local variables and memory in the semantics. *)
(* XXX: I don't like type names conflicting with variable names. I think we can
        just delete these. *)
Type locals = (Type `:varname |-> 'a v`)
Type memory = (Type `:'a word -> 'a word_lab`)

(* The fields are named after the fields of state in panSemTheory. *)
Datatype:
  context = <| locals_memory : ('a locals # 'a memory) set ;
               be            : bool ;
               base_addr     : 'a word ;
               ffi           : 'ffi itself |>
End

Definition state_to_context_def:
  state_to_context (s:('a, 'ffi) state) =
    <| locals_memory := {(s.locals, s.memory)} ;
       be            := s.be ;
       base_addr     := s.base_addr ;
       ffi           := (:'ffi) |>
End

Definition range_def:
  range (e:'a panLang$exp) (ctxt:('a, 'ffi) context) =
    { THE (eval <| memory    := memory ;
                   locals    := locals ;
                   memaddrs  := UNIV ;
                   be        := ctxt.be ;
                   base_addr := ctxt.base_addr ;
                   ffi       := ARB:'ffi ffi_state |>
                e)
    | locals, memory | (locals, memory) ∈ ctxt.locals_memory }
End
∈
(* Find an upper bound on the working set of an expression. *)
Definition working_set_exp_def:
  working_set_exp (Const w) ctxt = ({}:'a word set) ∧
  working_set_exp (Var v) ctxt = {} ∧
  working_set_exp (Label fname) ctxt = {} ∧
  working_set_exp (Struct es) ctxt =
    FOLDL (λws e. ws ∪ working_set_exp e ctxt) {} es ∧
  working_set_exp (Field index e) ctxt = working_set_exp e ctxt ∧
  working_set_exp (Load shape src) ctxt =
    (let addrs = { addr | ValWord addr ∈ range src ctxt } in
      { x | (addr, x) | addr ∈ addrs ∧
                        addr ≤ x ∧ x ≤ addr + n2w (size_of_shape shape) }) ∧
  working_set_exp (LoadByte e) ctxt =
    (let addrs = { addr | ValWord addr ∈ range e ctxt } in
      working_set_exp e ctxt ∪ addrs) ∧
  working_set_exp (Op op es) ctxt =
    FOLDL (λws e. ws ∪ working_set_exp e ctxt) {} es ∧
  working_set_exp (Panop op es) ctxt =
    FOLDL (λws e. ws ∪ working_set_exp e ctxt) {} es ∧
  working_set_exp (Cmp cmp e1 e2) ctxt =
    working_set_exp e1 ctxt ∪ working_set_exp e2 ctxt ∧
  working_set_exp (Shift sh e n) ctxt = working_set_exp e ctxt ∧
  working_set_exp BaseAddr ctxt = {}
Termination
  wf_rel_tac `measure (exp_size ARB o FST)`
End

Definition context_union_def:
  context_union ctxt1 ctxt2 =
    <| locals_memory := ctxt1.locals_memory ∪ ctxt2.locals_memory ;
       be            := ctxt1.be ;
       base_addr     := ctxt1.base_addr ;
       ffi           := ctxt1.ffi |>
End

(* Find an upper bound on the working set of a program. *)
d*)
