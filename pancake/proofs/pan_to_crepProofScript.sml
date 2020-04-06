(*
  Correctness proof for pan_simp
*)

open preamble
     panSemTheory crepSemTheory
     listRangeTheory
     pan_to_crepTheory


val _ = new_theory "pan_to_crepProof";

val _ = set_grammar_ancestry  ["panSem", "crepSem", "listRange", "pan_to_crep"];

Datatype:
  context =
  <| var_nums : panLang$varname |-> shape # num list;
     max_var : num|>
End

Definition with_shape_def:
  (with_shape [] _ = []) ∧
  (with_shape (sh::shs) e =
     TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e))
End


(* using this style to avoid using HD for code extraction later *)
Definition cexp_heads_def:
  (cexp_heads [] = SOME []) /\
  (cexp_heads (e::es) =
   case (e,cexp_heads es) of
   | [], _ => NONE
   | _ , NONE => NONE
   | x::xs, SOME ys => SOME (x::ys))
End


Definition comp_field_def:
  (comp_field i [] es = ([Const 0w], One)) ∧
  (comp_field i (sh::shs) es =
   if i = (0:num) then (TAKE (size_of_shape sh) es, sh)
   else comp_field (i-1) shs (DROP (size_of_shape sh) es))
End

Definition compile_exp_def:
  (compile_exp ctxt ((Const c):'a panLang$exp) =
   ([(Const c): 'a crepLang$exp], One)) /\
  (compile_exp ctxt (Var vname) =
   case FLOOKUP ctxt.var_nums vname of
   | SOME (shape, ns) => (MAP Var ns, shape)
   | NONE => ([Const 0w], One)) /\
  (compile_exp ctxt (Label fname) = ([Label fname], One)) /\

  (compile_exp ctxt (Struct es) =
   let cexps = MAP (compile_exp ctxt) es in
   (FLAT (MAP FST cexps), Comb (MAP SND cexps))) /\
  (compile_exp ctxt (Field index e) =
   let (cexp, shape) = compile_exp ctxt e in
   case shape of
   | One => ([Const 0w], One)
   | Comb shapes => comp_field index shapes cexp) /\
  (compile_exp ctxt (Load sh e) =
   let (cexp, shape) = compile_exp ctxt e in
   case cexp of
   | e::es => (load_shape (0w) (size_of_shape sh) e, sh)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (LoadByte e) =
   let (cexp, shape) = compile_exp ctxt e in
   case (cexp, shape) of
   | (e::es, One) => ([LoadByte e], One)
   | (_, _) => ([Const 0w], One)) /\
  (* have a check here for the shape *)
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   case cexp_heads cexps of
   | SOME es => ([Op bop es], One)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (Cmp cmp e e') =
   let ce  = FST (compile_exp ctxt e);
       ce' = FST (compile_exp ctxt e') in
   case (ce, ce') of
   | (e::es, e'::es') => ([Cmp cmp e e'], One)
   | (_, _) => ([Const 0w], One)) /\
  (compile_exp ctxt (Shift sh e n) = (* TODISC: to avoid [], and MAP [] *)
   case FST (compile_exp ctxt e) of
   | [] => ([Const 0w], One)
   | e::es => ([Shift sh e n], One))
Termination
  cheat
End

val s = ``(s:('a,'ffi) panSem$state)``

Definition code_rel_def:
  code_rel s_code t_code = ARB
End

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  code_rel s.code t.code
End

Definition flatten_def:
  (flatten (Val w) = [w]) ∧
  (flatten (Struct vs) = FLAT (MAP flatten vs))
Termination
  wf_rel_tac `measure (\v. v_size ARB v)` >>
  fs [MEM_IMP_v_size]
End

Definition no_overlap_def:
  no_overlap fm <=>
    (!x a xs.
       FLOOKUP fm x = SOME (a,xs) ==> ALL_DISTINCT xs) /\
    (!x y a b xs ys.
       FLOOKUP fm x = SOME (a,xs) /\
       FLOOKUP fm y = SOME (b,ys) /\
       ~DISJOINT (set xs) (set ys) ==> x = y)
End

Definition ctxt_max_def:
  ctxt_max n fm <=>
    0 < n ∧
    (!x a xs.
       FLOOKUP fm x = SOME (a,xs) ==>  list_max xs < n)
End

Definition locals_rel_def:
  locals_rel ctxt (s_locals:mlstring |-> 'a v) t_locals <=>
  no_overlap ctxt.var_nums /\ ctxt_max ctxt.max_var ctxt.var_nums /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃ns vs. FLOOKUP (ctxt.var_nums) vname = SOME (shape_of v, ns) ∧
    OPT_MMAP (FLOOKUP t_locals) ns = SOME vs ∧ flatten v = vs
End

Theorem lookup_locals_eq_map_vars:
  ∀ns t.
  OPT_MMAP (FLOOKUP t.locals) ns =
  OPT_MMAP (eval t) (MAP Var ns)
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_MAP_o] >>
  fs [MAP_EQ_f] >> rw [] >>
  fs [crepSemTheory.eval_def]
QED

Theorem opt_mmap_eq_some:
  ∀xs f ys.
  OPT_MMAP f xs = SOME ys <=>
   MAP f xs = MAP SOME ys
Proof
  Induct >> rw [OPT_MMAP_def]
  >- metis_tac [] >>
  eq_tac >> rw [] >> fs [] >>
  cases_on ‘ys’ >> fs []
QED

Theorem length_flatten_eq_size_of_shape:
  !v.
   LENGTH (flatten v) = size_of_shape (shape_of v)
Proof
  ho_match_mp_tac flatten_ind >> rw []
  >- (cases_on ‘w’ >> fs [shape_of_def, flatten_def, panLangTheory.size_of_shape_def]) >>
  fs [shape_of_def, flatten_def, panLangTheory.size_of_shape_def] >>
  fs [LENGTH_FLAT, MAP_MAP_o] >> fs[SUM_MAP_FOLDL] >>
  match_mp_tac FOLDL_CONG >> fs []
QED


Theorem map_append_eq_drop:
  !xs ys zs f.
   MAP f xs = ys ++ zs ==>
     MAP f (DROP (LENGTH ys) xs) = zs
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> fs [DROP]
QED

Definition cexp_heads_simp_def:
  cexp_heads_simp es =
  if (MEM [] es) then NONE
  else SOME (MAP HD es)
End


Theorem cexp_heads_eq:
  !es. cexp_heads es = cexp_heads_simp es
Proof
  Induct >>
  rw [cexp_heads_def, cexp_heads_simp_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

Theorem opt_mmap_mem_func:
  ∀l f n g.
  OPT_MMAP f l = SOME n ∧ MEM g l ==>
  ?m. f g = SOME m
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_mem_defined:
  !l f m e n.
   OPT_MMAP f l = SOME m ∧
   MEM e l ∧ f e = SOME n ==>
    MEM n m
Proof
  Induct >> rw [] >>
  fs [OPT_MMAP_def] >> rveq
  >- fs [MEM] >>
  res_tac >> fs []
QED

Definition v2word_def:
  v2word (ValWord v) = Word v
End

Theorem opt_mmap_el:
  ∀l f x n.
  OPT_MMAP f l = SOME x ∧
  n < LENGTH l ==>
  f (EL n l) = SOME (EL n x)
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  cases_on ‘n’ >> fs []
QED

Theorem opt_mmap_length_eq:
  ∀l f n.
  OPT_MMAP f l = SOME n ==>
  LENGTH l = LENGTH n
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_opt_map:
  !l f n g.
  OPT_MMAP f l = SOME n ==>
  OPT_MMAP (λa. OPTION_MAP g (f a)) l = SOME (MAP g n)
Proof
  Induct >> rw [] >>
  fs [OPT_MMAP_def] >> rveq >>
  res_tac >> fs []
QED

Theorem length_load_shape_eq_shape:
  !n a e.
   LENGTH (load_shape a n e) = n
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >>
  fs [] >>
  every_case_tac >> fs []
QED


Theorem mem_load_some_shape_eq:
  ∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==>
  shape_of v = sh
Proof
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==> shape_of v = sh) /\
  (∀sh adr dm (m: 'a word -> 'a word_lab) v.
   mem_loads sh adr dm m = SOME v ==> MAP shape_of v = sh)’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >> rw [panSemTheory.mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >>
  rveq >> TRY (cases_on ‘m adr’) >> fs [shape_of_def] >>
  metis_tac []
QED


Theorem mem_load_flat_rel:
  ∀sh adr s v n.
  mem_load sh adr s.memaddrs (s.memory: 'a word -> 'a word_lab) = SOME v ∧
  n < LENGTH (flatten v) ==>
  crepSem$mem_load (adr + bytes_in_word * n2w (LENGTH (TAKE n (flatten v)))) s =
  SOME (EL n (flatten v))
Proof
  rw [] >>
  qmatch_asmsub_abbrev_tac `mem_load _ adr dm m = _` >>
  ntac 2 (pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘n’,‘s’, `v`,`m`,`dm`,`adr`, `sh`] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
       mem_load sh adr dm m = SOME v ⇒
       ∀(s :(α, β) state) n.
           n < LENGTH (flatten v) ⇒
           dm = s.memaddrs ⇒
           m = s.memory ⇒
           mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (flatten v))) /\
       (∀sh adr dm (m: 'a word -> 'a word_lab) v.
       mem_loads sh adr dm m = SOME v ⇒
       ∀(s :(α, β) state) n.
           n < LENGTH (FLAT (MAP flatten v)) ⇒
           dm = s.memaddrs ⇒
           m = s.memory ⇒
           mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (FLAT (MAP flatten v))))’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >>
  rpt strip_tac >> rveq
  >- (
   fs [panSemTheory.mem_load_def] >>
   cases_on ‘sh’ >> fs [option_case_eq] >>
   rveq
   >- (fs [flatten_def] >> rveq  >> fs [mem_load_def]) >>
   first_x_assum drule >>
   disch_then (qspec_then ‘s’ mp_tac) >>
   fs [flatten_def, ETA_AX])
  >-  (
   fs [panSemTheory.mem_load_def] >>
   rveq >> fs [flatten_def]) >>
  fs [panSemTheory.mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >> rveq
  >- (
   fs [flatten_def] >>
   cases_on ‘n’ >> fs [EL] >>
   fs [panLangTheory.size_of_shape_def] >>
   fs [n2w_SUC, WORD_LEFT_ADD_DISTRIB]) >>
  first_x_assum drule >>
  disch_then (qspec_then ‘s’ mp_tac) >>
  fs [] >>
  strip_tac >>
  first_x_assum (qspec_then ‘s’ mp_tac) >>
  strip_tac >> fs [] >>
  fs [flatten_def, ETA_AX] >>
  cases_on ‘0 <= n /\ n < LENGTH (FLAT (MAP flatten vs))’ >>
  fs []
  >- fs [EL_APPEND_EQN] >>
  fs [NOT_LESS] >>
  ‘n - LENGTH (FLAT (MAP flatten vs)) < LENGTH (FLAT (MAP flatten vs'))’ by
    DECIDE_TAC >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  fs [EL_APPEND_EQN] >>
  ‘size_of_shape (Comb l) = LENGTH (FLAT (MAP flatten vs))’ by (
    ‘mem_load (Comb l) adr s.memaddrs s.memory = SOME (Struct vs)’ by
       rw [panSemTheory.mem_load_def] >>
    drule mem_load_some_shape_eq >>
    strip_tac >> pop_assum (assume_tac o GSYM) >>
    fs [] >>
    metis_tac [GSYM length_flatten_eq_size_of_shape, flatten_def]) >>
  fs [] >>
  drule n2w_sub >>
  strip_tac >> fs [] >>
  fs [WORD_LEFT_ADD_DISTRIB] >>
  fs [GSYM WORD_NEG_RMUL]
QED


Theorem eval_load_shape_el_rel:
  !m n a t e.
  n < m ==>
  eval t (EL n (load_shape a m e)) =
  eval t (Load (Op Add [e; Const (a + bytes_in_word * n2w n)]))
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >>
  fs [ADD1] >>
  cases_on ‘n’ >> fs []
  >- (
   TOP_CASE_TAC >> fs [] >>
   fs [eval_def, OPT_MMAP_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   fs [wordLangTheory.word_op_def]) >>
  rw [] >>
  fs [ADD1] >>
  fs [GSYM word_add_n2w, WORD_LEFT_ADD_DISTRIB]
QED

Theorem compile_exp_val_rel:
  ∀s e v (t :('a, 'b) state) ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
  MAP (eval t) es = MAP SOME (flatten v) ∧
  LENGTH es = size_of_shape sh ∧
  shape_of v = sh
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [flatten_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def, crepSemTheory.eval_def,
       panLangTheory.size_of_shape_def, shape_of_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [locals_rel_def] >>
   first_x_assum drule >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [lookup_locals_eq_map_vars] >>
   fs [opt_mmap_eq_some] >>
   fs [MAP_MAP_o] >>
   metis_tac [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [flatten_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >> cheat (* should come from code_rel, define it later*))
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   fs [MAP_MAP_o, MAP_FLAT, flatten_def] >>
   fs [o_DEF] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs []
   >-  fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
   rename [‘_ = SOME vs’] >>
   fs [] >>
   last_x_assum mp_tac >>
   impl_tac >-
    metis_tac [] >>
    strip_tac >> fs [] >>
    last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
    disch_then drule >> disch_then drule >>
    cases_on ‘compile_exp ct h’ >> fs [])
  >-
   (
   (* Field case *)
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   first_x_assum drule_all >> fs [shape_of_def] >>
   strip_tac >> fs [] >> rveq >>
   qpat_x_assum ‘_ = SOME (Struct _)’ kall_tac >>
   qpat_x_assum ‘compile_exp _ _ = _’ kall_tac >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac
             [‘ct’,‘cexp’ ,‘sh’ , ‘es’, ‘t’, ‘s’, ‘index’, ‘vs’] >>
   Induct >> rpt gen_tac >- fs [] >>
   rewrite_tac [AND_IMP_INTRO] >>
   strip_tac >> fs [] >>
   cases_on ‘index’ >> fs []
   >- (
    fs [comp_field_def] >> rveq >>
    fs [MAP_TAKE, flatten_def] >>
    fs [panLangTheory.size_of_shape_def] >>
    fs [GSYM length_flatten_eq_size_of_shape] >>
    metis_tac [LENGTH_MAP, TAKE_LENGTH_APPEND]) >>
   fs [comp_field_def] >>
   last_x_assum drule >>
   ntac 3 (disch_then drule) >>
   fs [panLangTheory.size_of_shape_def, flatten_def] >>
   drule map_append_eq_drop >>
   fs [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   last_x_assum drule_all >>
   strip_tac >>
   fs [shape_of_def, panLangTheory.size_of_shape_def,flatten_def] >>
   rveq >> fs [] >> rveq >>
   fs [length_load_shape_eq_shape] >>
   drule mem_load_some_shape_eq >>
   strip_tac >> fs [] >>
   fs [MAP_EQ_EVERY2] >> fs [length_load_shape_eq_shape] >>
   rveq >> fs [GSYM length_flatten_eq_size_of_shape] >>
   fs [LIST_REL_EL_EQN] >>  fs [length_load_shape_eq_shape] >>
   rw [] >> fs [state_rel_def] >>
   drule mem_load_flat_rel >>
   disch_then drule >>
   strip_tac >> fs [] >>
   drule eval_load_shape_el_rel >>
   disch_then (qspecl_then [‘0w’, ‘t’,‘x0’] mp_tac) >> fs [] >>
   strip_tac >>
   fs [eval_def, OPT_MMAP_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs[EVERY_DEF] >> cases_on ‘h’ >> fs [] >>
   fs [wordLangTheory.word_op_def] >> rveq >>
   qpat_x_assum ‘mem_load _ _ = _’ (mp_tac o GSYM) >>
   strip_tac >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   first_x_assum drule_all >> fs [shape_of_def] >>
   strip_tac >> fs [] >> rveq >>
   cases_on ‘cexp’ >> fs [panLangTheory.size_of_shape_def, flatten_def] >> rveq >>
   fs [panLangTheory.size_of_shape_def] >>
   fs [eval_def, state_rel_def])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [cexp_heads_eq] >>
   fs [cexp_heads_simp_def] >>
   ‘~MEM [] (MAP FST (MAP (λa. compile_exp ct a) es))’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     fs [MEM_MAP] >> rveq >>
     drule opt_mmap_mem_func >>
     disch_then drule >>
     strip_tac >> fs [] >>
     rename1 ‘MEM e es’ >>
     cases_on ‘compile_exp ct e’ >> fs [] >>
     ‘shape_of m = One’ by (
       ‘MEM m ws’ by (
         drule opt_mmap_mem_defined >>
         strip_tac >> res_tac >> fs []) >>
       qpat_x_assum ‘EVERY _ ws’ mp_tac >>
       fs [EVERY_MEM] >>
       disch_then (qspec_then ‘m’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [shape_of_def]) >>
     last_x_assum drule_all >>
     strip_tac >> rveq >> rfs [panLangTheory.size_of_shape_def]) >>
     fs [] >> rveq >>
     fs [panLangTheory.size_of_shape_def, shape_of_def] >>
     fs [flatten_def, eval_def, MAP_MAP_o] >>
     ‘OPT_MMAP (λa. eval t a)
      (MAP (HD ∘ FST ∘ (λa. compile_exp ct a)) es) =
      OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es’ by (
       ho_match_mp_tac IMP_OPT_MMAP_EQ >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
       rw [] >>
       drule opt_mmap_length_eq >>
       strip_tac >> fs [] >>
       first_x_assum (qspec_then ‘EL n es’ mp_tac) >>
       impl_tac >- metis_tac [EL_MEM] >>
       drule opt_mmap_el >> fs [] >>
       disch_then drule >>
       strip_tac >> fs [] >>
       disch_then drule >>
       disch_then drule >>
       disch_then (qspecl_then [‘FST (compile_exp ct (EL n es))’,
                                ‘SND(compile_exp ct (EL n es))’] mp_tac) >>
       fs [] >>
       strip_tac >>
       fs [EVERY_EL] >>
       last_x_assum (qspec_then ‘n’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [] >>
       qpat_x_assum ‘LENGTH es = LENGTH _’ (mp_tac o GSYM) >>
       strip_tac >> fs [] >>
       drule (INST_TYPE [``:'a``|->``:'a panLang$exp``,
                         ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
       disch_then (qspec_then ‘(HD ∘ FST ∘ (λa. compile_exp ct a))’ mp_tac) >>
       strip_tac >> fs [] >>
       fs [flatten_def, v2word_def] >> rveq) >>
     fs [] >>
     ‘OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es =
      SOME (MAP v2word ws)’ by (
       ho_match_mp_tac opt_mmap_opt_map >> fs []) >>
     fs [EVERY_MAP, MAP_MAP_o] >>
     ‘∀x. (λw. case w of ValWord v6 => T | ValLabel v7 => F | Struct v3 => F) x ==>
      (λx. case v2word x of Word v2 => T | Label v3 => F) x’ by (
       rw [] >> every_case_tac >> fs [v2word_def]) >>
     drule MONO_EVERY >>
     disch_then (qspec_then ‘ws’ mp_tac) >> fs [] >>
     strip_tac >> fs [flatten_def] >>
     fs [GSYM MAP_MAP_o] >>
     qmatch_goalsub_abbrev_tac ‘word_op op ins’ >>
     qmatch_asmsub_abbrev_tac ‘word_op op ins'’ >>
     ‘ins = ins'’ by (
       unabbrev_all_tac >> fs [MAP_EQ_EVERY2] >>
       fs [LIST_REL_EL_EQN] >>
       rw [] >>
       fs [EVERY_EL] >> (* for some reason, drule EL_MAP is not being inst. properly*)
       ‘EL n (MAP v2word ws) = v2word (EL n ws)’ by (
         match_mp_tac EL_MAP >> fs []) >>
       fs [] >>
       last_x_assum (qspec_then ‘n’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [v2word_def]) >>
     unabbrev_all_tac >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq, v_case_eq, panSemTheory.word_lab_case_eq] >> rveq >>
   (* open compile_exp *)
   fs [compile_exp_def] >>
   cases_on ‘compile_exp ct e’ >>
   cases_on ‘compile_exp ct e'’ >>
   first_x_assum drule_all >>
   first_x_assum drule_all >>
   strip_tac >> strip_tac >>
   fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
   rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   fs [crepSemTheory.eval_def] >>
   every_case_tac >> fs [] >> EVAL_TAC) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def] >>
  fs [option_case_eq, v_case_eq, panSemTheory.word_lab_case_eq] >> rveq >>
  fs [compile_exp_def] >>
  cases_on ‘compile_exp ct e’ >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
  rveq >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
  fs [eval_def] >>  every_case_tac >>
  fs [panLangTheory.size_of_shape_def, shape_of_def]
QED

(* compiler for prog *)

Definition var_cexp_def:
  (var_cexp (Const w:'a crepLang$exp) = ([]:num list)) ∧
  (var_cexp (Var v) = [v]) ∧
  (var_cexp (Label f) = []) ∧
  (var_cexp (Load e) = var_cexp e) ∧
  (var_cexp (LoadByte e) = var_cexp e) ∧
  (var_cexp (Op bop es) = FLAT (MAP var_cexp es)) ∧
  (var_cexp (Cmp c e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_cexp (Shift sh e num) = var_cexp e)
Termination
  cheat
End

Definition nested_seq_def:
  (nested_seq [] = (Skip:'a crepLang$prog)) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End


Definition nested_decs_def:
  (nested_decs [] [] p = p) /\
  (nested_decs (n::ns) (e::es) p = Dec n e (nested_decs ns es p)) /\
  (nested_decs [] _ p = p) /\
  (nested_decs _ [] p = p)
End

Definition distinct_lists_def:
  distinct_lists xs ys =
    EVERY (\x. ~MEM x ys) xs
End

Definition stores_def:
  (stores ad [] a = []) /\
  (stores ad (e::es) a =
     if a = 0w then Store ad e :: stores ad es (a + byte$bytes_in_word)
     else Store (Op Add [ad; Const a]) e :: stores ad es (a + byte$bytes_in_word))
End

Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog ctxt (Dec v e p) =
   let (es, sh) = compile_exp ctxt e;
       vmax = ctxt.max_var;
       nvars = GENLIST (λx. vmax + SUC x) (size_of_shape sh);
       nctxt = ctxt with  <|var_nums := ctxt.var_nums |+ (v, (sh, nvars));
                            max_var := ctxt.max_var + size_of_shape sh |> in
    nested_seq (MAP2 Assign nvars es ++ [compile_prog nctxt p])) /\

  (compile_prog ctxt (Assign v e) =
   let (es, sh) = compile_exp ctxt e in
   case FLOOKUP ctxt.var_nums v of
    | SOME (vshp, ns) =>
      if LENGTH ns = LENGTH es
      then if distinct_lists ns (FLAT (MAP var_cexp es))
      then nested_seq (MAP2 Assign ns es)
      else let vmax = ctxt.max_var;
               temps = GENLIST (λx. vmax + SUC x) (LENGTH ns) in
           nested_decs temps es
                       (nested_seq (MAP2 Assign ns (MAP Var temps)))
      else Skip:'a crepLang$prog
    | NONE => Skip) /\
  (compile_prog ctxt (Store dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (es, sh) => nested_seq (stores ad es 0w)
    | _ => Skip) /\
  (compile_prog ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (e::es, _) => StoreByte ad e
    | _ => Skip) /\
  (compile_prog ctxt (Seq p p') =
    Seq (compile_prog ctxt p) (compile_prog ctxt p')) /\
  (compile_prog ctxt (If e p p') =
   case compile_exp ctxt e of
    | (ce::ces, _) =>
      If ce (compile_prog ctxt p) (compile_prog ctxt p')
    | _ => Skip) /\
  (compile_prog ctxt (While e p) =
   case compile_exp ctxt e of
   | (ce::ces, _) =>
     While ce (compile_prog ctxt p)
   | _ => Skip) /\
  (compile_prog ctxt Break = Break) /\
  (compile_prog ctxt Continue = Continue) /\
  (compile_prog ctxt (Call rt e es) = ARB) /\
  (compile_prog ctxt (ExtCall f v1 v2 v3 v4) = ARB) /\
  (compile_prog ctxt (Raise e) = ARB) /\
  (compile_prog ctxt (Return e) = ARB) /\
  (compile_prog ctxt Tick = Tick)
End


val goal =
  ``λ(prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ⇒
      ∃res1 t1. evaluate (compile_prog ctxt prog,t) = (res1,t1) /\
      state_rel s1 t1 ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt s1.locals t1.locals
       | SOME (Return v) => res1 = SOME (Return (ARB v)) (* many return values *)
       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt s1.locals t1.locals /\
                       code_rel ctxt s1.code t1.code

       | SOME Continue => res1 = SOME Continue /\
                       locals_rel ctxt s1.locals t1.locals /\
                       code_rel ctxt s1.code t1.code
       | SOME TimeOut => res1 = SOME TimeOut
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
       | SOME (Exception v) => res1 = SOME (Exception (ARB v))
       | _ => F``

local
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_prog_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end



Theorem compile_Skip:
  ^(get_goal "compile_prog _ panLang$Skip")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, crepSemTheory.evaluate_def,
      compile_prog_def] >> rveq >> fs []
QED


Theorem locals_rel_lookup_ctxt:
  locals_rel ctxt lcl lcl' /\
  FLOOKUP lcl vr = SOME v ==>
  ?ns. FLOOKUP ctxt.var_nums vr = SOME (shape_of v,ns) /\
   LENGTH ns = LENGTH (flatten v) /\
   OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v)
Proof
  rw [locals_rel_def] >>
  metis_tac [opt_mmap_length_eq]
QED


Theorem distinct_lists_append:
  ALL_DISTINCT (xs ++ ys)  ==>
  distinct_lists xs ys
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_commutes:
  distinct_lists xs ys = distinct_lists ys xs
Proof
  EQ_TAC >>
  rw [] >>
  fs [distinct_lists_def, EVERY_MEM] >>
  metis_tac []
QED

Theorem distinct_lists_cons:
  distinct_lists (ns ++ xs) (ys ++ zs) ==>
  distinct_lists xs zs
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED


Theorem opt_mmap_flookup_update:
  OPT_MMAP (FLOOKUP fm) xs = SOME ys /\
  ~MEM x xs ==>
  OPT_MMAP (FLOOKUP (fm |+ (x,y))) xs = SOME ys
Proof
  rw [] >>
  fs [opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  fs [FLOOKUP_UPDATE, MEM_EL] >>
  metis_tac []
QED

Theorem update_locals_not_vars_eval_eq:
  ∀s e v n w.
  ~MEM n (var_cexp e) /\
  eval s e = SOME v ==>
  eval (s with locals := s.locals |+ (n,w)) e = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (fs [eval_def])
  >- fs [eval_def, var_cexp_def, FLOOKUP_UPDATE]
  >- fs [eval_def]
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def, ETA_AX] >>
   fs [eval_def, CaseEq "option", ETA_AX] >>
   qexists_tac ‘ws’ >>
   fs [opt_mmap_eq_some, ETA_AX,
       MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   fs [MEM_FLAT, MEM_MAP] >>
   metis_tac [EL_MEM]) >>
  rpt gen_tac >>
  strip_tac >> fs [var_cexp_def, ETA_AX] >>
  fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> metis_tac []
QED

Theorem eval_nested_assign_distinct_eq:
  !es ns t ev vs.
  MAP (eval t) es = MAP SOME ev /\
  OPT_MMAP (FLOOKUP t.locals) ns = SOME vs /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns /\
  LENGTH ns = LENGTH es ==>
  evaluate (nested_seq (MAP2 Assign ns es),t) =
      (NONE, t with locals := t.locals |++ ZIP (ns, ev))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       FUPDATE_LIST_THM,
       state_component_equality]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [MAP_EQ_CONS] >>
  rveq >> rfs [] >>
  fs [OPT_MMAP_def] >>
  rveq >> rfs [] >>
  rveq >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘FLOOKUP t.locals n = SOME nv’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  drule opt_mmap_flookup_update >>
  disch_then drule >>
  disch_then (qspec_then ‘v’ assume_tac) >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule >>
  fs [state_accfupds] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  fs [FUPDATE_LIST_THM]
QED

Theorem opt_mmap_some_eq_zip_flookup:
  ∀xs f ys.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys ⇒
  OPT_MMAP (FLOOKUP (f |++ ZIP (xs,ys))) xs =
  SOME ys
Proof
  Induct >> rw [OPT_MMAP_def] >>
  fs [] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘f’] assume_tac) >>
  fs [FLOOKUP_DEF]
QED

Theorem all_distinct_flookup_all_distinct:
  no_overlap fm /\
   FLOOKUP fm x = SOME (y,zs) ==>
  ALL_DISTINCT zs
Proof
  rw [] >>
  fs [no_overlap_def] >>
  metis_tac []
QED

Theorem no_overlap_flookup_distinct:
  no_overlap fm /\
  x ≠ y /\
  FLOOKUP fm x = SOME (a,xs) /\
  FLOOKUP fm y = SOME (b,ys) ==>
  distinct_lists xs ys
Proof
  rw [] >>
  match_mp_tac distinct_lists_append >>
  fs [no_overlap_def, ALL_DISTINCT_APPEND, DISJOINT_ALT] >>
  metis_tac []
QED

Theorem opt_mmap_disj_zip_flookup:
  ∀xs f ys zs.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ⇒
  OPT_MMAP (FLOOKUP (f |++ ZIP (xs,zs))) ys =
  OPT_MMAP (FLOOKUP f) ys
Proof
  Induct >> rw [] >>
  fs [distinct_lists_def]
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘zs’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ho_match_mp_tac IMP_OPT_MMAP_EQ >>
  ho_match_mp_tac MAP_CONG >> fs [] >>
  rw [] >>
  fs [FLOOKUP_UPDATE] >>
  metis_tac []
QED

Theorem res_var_commutes:
  n ≠ h ==>
  res_var (res_var lc (h,FLOOKUP lc' h))
  (n,FLOOKUP lc' n) =
  res_var (res_var lc (n,FLOOKUP lc' n))
  (h,FLOOKUP lc' h)
Proof
  rw [] >>
  cases_on ‘FLOOKUP lc' h’ >>
  cases_on ‘FLOOKUP lc' n’ >>
  fs[res_var_def] >>
  fs [DOMSUB_COMMUTES, DOMSUB_FUPDATE_NEQ] >>
  metis_tac [FUPDATE_COMMUTES]
QED


Theorem eval_nested_decs_seq_res_var_eq:
  !es ns t ev p.
  MAP (eval t) es = MAP SOME ev /\
  LENGTH ns = LENGTH es /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns ==>
  let (q,r) = evaluate (p, t with locals := t.locals |++ ZIP (ns, ev)) in
  evaluate (nested_decs ns es p, t) =
  (q, r with locals :=
        FOLDL res_var r.locals (ZIP (ns, MAP (FLOOKUP t.locals) ns)))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [nested_decs_def, FUPDATE_LIST_THM] >>
   cases_on ‘t’ >> cases_on ‘r’ >>
   fs [state_component_equality, state_locals_fupd]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_decs_def] >>
  fs [evaluate_def] >>
  fs [MAP_EQ_CONS] >>
  pairarg_tac >> fs [] >>
  rveq >> rfs [] >>
  pairarg_tac >> fs [] >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘~MEM n t'’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule_all >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [FUPDATE_LIST_THM] >>
  fs [state_component_equality] >>
  ‘MAP (FLOOKUP (t.locals |+ (n,v))) t' =
   MAP (FLOOKUP t.locals) t'’ by
    metis_tac [MAP_EQ_f, FLOOKUP_UPDATE] >>
  fs [] >>
  pop_assum kall_tac >>
  qpat_x_assum ‘~MEM n t'’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘r’, ‘n’,‘t’, ‘t'’] >>
  Induct >> rw [] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  fs [] >>
  disch_then (qspec_then ‘r with locals :=
                          res_var r.locals (h,FLOOKUP t.locals h)’ mp_tac) >>
  fs [] >>
  metis_tac [res_var_commutes]
QED

Theorem mem_comp_field:
  !sh i e shp ce es vs.
   i < LENGTH vs /\
  LENGTH e = size_of_shape (shape_of (Struct vs)) /\
  comp_field i sh e = (es,shp) /\
  Comb sh = shape_of (Struct vs) /\
  MEM ce es ==> MEM ce e
Proof
  Induct >> rw [comp_field_def] >>
  fs [] >> rveq
  >- fs [shape_of_def]
  >- (
   cases_on ‘vs’ >> fs [] >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >> fs [] >>
   ‘size_of_shape (shape_of h') <= LENGTH e’ by DECIDE_TAC >>
   metis_tac [MEM_TAKE]) >>
  cases_on ‘vs’ >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >>
  rveq >> fs [] >>
  first_x_assum (qspecl_then  [‘i-1’, ‘(DROP (size_of_shape (shape_of h')) e)’,
                               ‘shp’, ‘ce’, ‘es’, ‘t’] mp_tac) >>
  fs [] >>
  metis_tac [MEM_DROP_IMP]
QED

Theorem var_exp_load_shape:
  !i a e n.
   MEM n (load_shape a i e) ==>
   var_cexp n = var_cexp e
Proof
  Induct >>
  rw [load_shape_def] >>
  fs [var_cexp_def] >>
  metis_tac []
QED

Theorem eval_var_cexp_present_ctxt:
  ∀(s :('a, 'b) panSem$state) e v (t :('a, 'b) state) ct es sh.
  state_rel s t /\
  eval s e = SOME v /\
  locals_rel ct s.locals t.locals /\
  compile_exp ct e = (es,sh) ==>
  ∀ce. MEM ce es ==> (var_cexp ce = [] ∨
   (var_cexp ce <> [] ==>
   ?v shp ns. FLOOKUP ct.var_nums v = SOME (shp,ns)  /\
       EVERY (\x. MEM x ns) (var_cexp ce)))
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def] >>
   fs [CaseEq "option"] >> rveq
   >- fs [var_cexp_def] >>
   cases_on ‘v'’ >> fs [] >>
   rveq >>
   fs [MEM_MAP] >>
   rveq >>
   fs [var_cexp_def] >>
   metis_tac [])
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [MAP_MAP_o, MAP_FLAT] >>
   fs [o_DEF] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs [] >>
   rpt gen_tac >> strip_tac >>
   fs [OPT_MMAP_def] >>
   strip_tac >>
   strip_tac >>
   rveq >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
   disch_then drule >>
   cases_on ‘compile_exp ct h’ >> fs [] >>
   strip_tac >>
   strip_tac >>
   metis_tac [])
  >- (
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq
   >- rw [var_cexp_def] >>
   rpt gen_tac >> strip_tac >>
   first_x_assum drule >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   strip_tac >> rveq >> fs [] >>
   drule compile_exp_val_rel >>
   disch_then drule_all >>
   strip_tac >> fs [] >> rveq >>
   pop_assum (assume_tac o GSYM) >>
   fs [] >> rveq >>
   metis_tac [mem_comp_field])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   cases_on ‘cexp’ >> fs [] >> rveq
   >- (rw [] >> metis_tac [var_cexp_def]) >>
   rpt gen_tac >>
   strip_tac >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   strip_tac >> rveq >> fs [] >>
   pop_assum (qspec_then ‘h’ assume_tac) >> fs [] >>
   drule var_exp_load_shape >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   cases_on ‘cexp’ >> fs [] >> rveq
   >- (rw [] >> metis_tac [var_cexp_def]) >>
   reverse (cases_on ‘shape’) >> fs [] >> rveq
   >- (rw [] >> metis_tac [var_cexp_def]) >>
   rpt gen_tac >>
   strip_tac >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   strip_tac >> rveq >> fs [] >>
   pop_assum (qspec_then ‘h’ assume_tac) >> fs [] >>
   metis_tac [var_cexp_def])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [cexp_heads_eq] >>
   fs [cexp_heads_simp_def] >>
   FULL_CASE_TAC >>
   fs [] >> rveq
   >- (rw [] >> metis_tac [var_cexp_def]) >>
   cheat) >> cheat
QED


Theorem genlist_distinct_max:
  !ys y n.
  list_max ys < y ==>
  distinct_lists (GENLIST (λx. SUC x + y) n) ys
Proof
  Induct >> rw [] >>
  fs [list_max_def, distinct_lists_def,
      EVERY_GENLIST] >> rw [] >>
  every_case_tac >> fs [] >>
  first_x_assum (qspecl_then [‘y’, ‘x’] mp_tac) >>
  fs [] >>
  cases_on ‘x’ >> fs [] >>
  cheat
QED


Theorem update_eq_zip_flookup:
  ∀xs f ys n.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys /\
  n < LENGTH xs ⇒
  FLOOKUP (f |++ ZIP (xs,ys)) (EL n xs) =
        SOME (EL n ys)
Proof
  Induct >> rw [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
    cases_on ‘n’ >> fs [] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘f’] assume_tac) >>
  fs [FLOOKUP_DEF]
QED

Theorem map_var_cexp_eq_var:
  !vs. FLAT (MAP var_cexp (MAP Var vs)) = vs
Proof
  Induct >> rw [var_cexp_def] >>
  fs [var_cexp_def]
QED


Theorem flookup_res_var_distinct_eq:
  !xs x fm.
  ~MEM x (MAP FST xs) ==>
  FLOOKUP (FOLDL res_var fm xs) x =
  FLOOKUP fm x
Proof
  Induct >> rw [] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘r’ >> fs [res_var_def] >>
  fs [MEM_MAP]  >>
  metis_tac [DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED


Theorem flookup_res_var_distinct_zip_eq:
  LENGTH xs = LENGTH ys /\
  ~MEM x xs ==>
  FLOOKUP (FOLDL res_var fm (ZIP (xs,ys))) x =
  FLOOKUP fm x
Proof
  rw [] >>
  qmatch_goalsub_abbrev_tac `FOLDL res_var _ l` >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`x`,`ys`,`xs`,`fm`, `l`] >>
  Induct >> rw [] >> rveq >>
  cases_on ‘xs’ >> cases_on ‘ys’ >> fs [ZIP] >>
  rveq >>
  cases_on ‘h''’ >> fs [res_var_def] >>
  fs [MEM_MAP]  >>
  metis_tac [DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED



Theorem foo:
!ys xs as bs cs fm.
 ALL_DISTINCT ys /\
 distinct_lists xs ys /\
  LENGTH xs = LENGTH as /\
  LENGTH xs = LENGTH cs /\
  LENGTH ys = LENGTH bs ==>
        MAP
          (FLOOKUP
             (FOLDL res_var (fm |++ ZIP (xs,as) |++ ZIP (ys,bs))
                (ZIP (xs,cs)))) ys =
        MAP (FLOOKUP (fm |++ ZIP (ys,bs))) ys
Proof
  Induct
  >- rw[MAP] >>
  rw []
  >- (
  cases_on ‘bs’ >>
  fs []>>
  fs [distinct_lists_def] >>
  fs [EVERY_MEM] >>
  fs [FUPDATE_LIST_THM] >>
  fs [] >>
  drule flookup_res_var_distinct_zip_eq >>
  disch_then (qspecl_then [‘h’ ,
                           ‘((fm |++ ZIP (xs,as)) |+ (h,h') |++ ZIP (ys,t))’] mp_tac) >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [] >>
  cheat (* easy cheat*)) >>
  cases_on ‘bs’ >>
  fs [] >>
  cheat
QED


Theorem compile_Assign:
  ^(get_goal "compile_prog _ (panLang$Assign _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  rename [‘Assign vr e’] >>
  fs [panSemTheory.evaluate_def, is_valid_value_def] >>
  fs [CaseEq "option", CaseEq "bool"] >> rveq >> fs [] >>
  rename [‘eval _ e = SOME ev’] >>
  rename [‘FLOOKUP _ vr = SOME v’] >>
  (* open compiler def *)
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  drule locals_rel_lookup_ctxt >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  fs [length_flatten_eq_size_of_shape] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   ‘ALL_DISTINCT ns’
     by metis_tac [locals_rel_def, no_overlap_def] >>
   drule eval_nested_assign_distinct_eq >>
   disch_then drule >>
   strip_tac >> fs [] >>
   conj_tac
   >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   cases_on ‘vr = vname’ >> fs [] >> rveq
   >- (
    pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
    fs [] >> rveq >>
    match_mp_tac opt_mmap_some_eq_zip_flookup >>
    fs [] >>
    metis_tac [all_distinct_flookup_all_distinct,
               length_flatten_eq_size_of_shape]) >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   rfs [] >>
   drule no_overlap_flookup_distinct >>
   disch_then drule_all >>
   strip_tac >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  (* non-distinct Assign  *)
  qmatch_goalsub_abbrev_tac ‘nested_decs temps es _’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    qsuff_tac ‘(\n. n < ctxt.max_var) (list_max (FLAT (MAP var_cexp es)))’
    >- fs [] >>
    match_mp_tac list_max_intro >>
    conj_tac >- fs [locals_rel_def, ctxt_max_def] >>
    fs [EVERY_FLAT] >>
    fs [EVERY_MAP] >>
    fs [EVERY_MEM] >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    ‘var_cexp x ≠ []’ by metis_tac [MEM] >>
    fs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [] >>
    fs [EVERY_MEM] >>
    res_tac >> fs [] >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    MAP_EVERY qid_spec_tac [‘ctxt’, ‘n’, ‘ns'’] >>
    Induct >> rw [list_max_def] >>
    fs [list_max_def]) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten ev’,
                          ‘nested_seq (MAP2 Assign ns (MAP Var temps))’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  ‘MAP (eval (t with locals := t.locals |++ ZIP (temps,flatten ev)))
   (MAP Var temps) = MAP SOME (flatten ev)’ by (
     fs [MAP_MAP_o, MAP_EQ_EVERY2] >>
     fs [LIST_REL_EL_EQN] >>
     rw [] >> rfs [] >>
     ‘n < LENGTH temps’ by (
       unabbrev_all_tac >> fs [MAP_MAP_o, MAP_EQ_EVERY2]>>
       metis_tac []) >>
     drule (INST_TYPE [``:'a``|->``:num``,
                       ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
     disch_then (qspec_then ‘Var’ assume_tac) >> fs [] >>
     fs [eval_def] >>
     metis_tac [update_eq_zip_flookup]) >>
  ‘ALL_DISTINCT ns’ by metis_tac [locals_rel_def, no_overlap_def] >>
  ‘distinct_lists ns temps’ by (
    unabbrev_all_tac >>
    once_rewrite_tac [distinct_lists_commutes] >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  drule eval_nested_assign_distinct_eq >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  disch_then (qspec_then ‘flatten v’ mp_tac) >>
   impl_tac
   >- (
    fs [map_var_cexp_eq_var] >>
    fs [Once distinct_lists_commutes] >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``]
           opt_mmap_disj_zip_flookup) >>
    disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
    fs [length_flatten_eq_size_of_shape]) >>
   strip_tac >> fs [] >>
   rveq >>
   fs [state_rel_def] >>
   fs [locals_rel_def] >>
   rw [] >> fs [] >>
   cases_on ‘vr = vname’ >> fs [] >> rveq
   >- (
    pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
    fs [] >> rveq >>
    fs [opt_mmap_eq_some] >>
    drule foo >> cheat) >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   rfs [] >> cheat
QED





val _ = export_theory();
