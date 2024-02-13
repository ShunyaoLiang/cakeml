(*
  Automate verification of the property that a Pancake program does not access
  memory that is out of bounds.
*)

(* Below is a glossary of identifiers used in this file.
     * addr:  Used for memory addresses. Pluralised as addrs.
     * ctxt:  Short for "context".
     * m:     Stands for "memory". Pluralised as ms.
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
Definition working_set_def:
  working_set (Skip:'a panLang$prog) (ctxt:('a, 'ffi) context) = (ctxt, {}) ∧
  working_set (Dec v e p) ctxt =
    (let ws = working_set_exp e ctxt and
         values = range e ctxt;
         lm = { (locals |+ (v, value), memory)
              | (locals, memory) ∈ ctxt.locals_memory ∧ value ∈ values };
         ctxt' = ctxt with locals_memory := lm;
         (ctxt'', ws') = working_set p ctxt' in
      (ctxt'', ws ∪ ws')) ∧
  working_set (Assign v e) ctxt =
    (let ws = working_set_exp e ctxt and
         values = range e ctxt;
         lm = { (locals |+ (v, value), memory)
              | (locals, memory) ∈ ctxt.locals_memory ∧ value ∈ values } in
      (ctxt with locals_memory := lm, ws)) ∧
  working_set (Store dst src) ctxt =
    (let ws = working_set_exp dst ctxt and
         ws' = working_set_exp src ctxt and
         addrs = { addr | ValWord addr ∈ range dst ctxt } and
         values = range src ctxt;
         lm = { (locals, THE (mem_stores addr (flatten value) UNIV memory))
              | (locals, memory) ∈ ctxt.locals_memory ∧ addr ∈ addrs ∧
                value ∈ values} in
      (ctxt with locals_memory := lm, ws ∪ ws' ∪ addrs)) ∧
  working_set (StoreByte dst src) ctxt =
    (let ws = working_set_exp dst ctxt and
         ws' = working_set_exp src ctxt and
         addrs = { addr | ValWord addr ∈ range dst ctxt } and
         ws = { w | ValWord w ∈ range src ctxt };
         lm = { (locals, THE (mem_store_byte memory UNIV ctxt.be addr (w2w w)))
              | locals, memory, addr, w
              | (locals, memory) ∈ ctxt.locals_memory ∧ addr ∈ addrs ∧
                w ∈ ws} in
      (ctxt with locals_memory := lm, ws ∪ ws' ∪ addrs)) ∧
  working_set (Seq c1 c2) ctxt =
    (let (ctxt', ws) = working_set c1 ctxt;
        (ctxt'', ws') = working_set c2 ctxt' in
      (ctxt'', ws ∪ ws')) ∧
  working_set (If e c1 c2) ctxt =
    (let ws = working_set_exp e ctxt and
        (ctxt', ws') = working_set c1 ctxt and
        (ctxt'', ws'') = working_set c2 ctxt in
      (context_union ctxt' ctxt'', ws ∪ ws' ∪ ws'')) ∧
  (* For the purposes of defining the major theorem below, this is sound because
     the nice semantics are the same as the semantics for While. This saves us
     a huge headache, but restricts working_set to finding the bound up until
     the next While loop. *)
  working_set (While _ _) ctxt = (ctxt, {}) ∧
  working_set Break ctxt = (ctxt, {}) ∧
  working_set Continue ctxt = (ctxt, {}) ∧
  (* See the note above on the While case. *)
  working_set (Call _ _ _) ctxt = (ctxt, {}) ∧
  (* See the note above on the While case. *)
  working_set (ExtCall _ _ _ _ _) ctxt = (ctxt, {}) ∧
  working_set (Return e) ctxt = (ctxt, working_set_exp e ctxt) ∧
  working_set (Raise eid e) ctxt = (ctxt, working_set_exp e ctxt) ∧
  working_set Tick ctxt = (ctxt, {})
End


(* Prove the major theorem: that if our bound on the working set of a Pancake
   program is within the allocated heap, we may replace the semantics with the
   nicer semantics. *)

Theorem foo:
  THE (eval s e) ∈ range e (state_to_context s)
Proof
  cheat
QED

Theorem working_set_mono:
  s.locals_memory ⊆ lm ⇒ 
  SND (working_set p s) ⊆ SND (working_set p (s with locals_memory := lm))
Proof
  cheat
QED

(* Useful with DEP_PURE_ONCE_REWRITE_TAC. *)
Theorem no_out_of_bounds:
  ∀p s.
    SND (working_set p (state_to_context s)) ⊆ s.memaddrs ⇒
    evaluate (p, s) = nice_evaluate (p, s)
Proof
  recInduct panSemTheory.evaluate_ind
  >> rpt strip_tac
    >- simp[evaluate_def, nice_evaluate_def]
    >- (simp[evaluate_def, nice_evaluate_def]
      >> TOP_CASE_TAC
      >> AP_TERM_TAC
      >> first_x_assum $ match_mp_tac o MP_CANON
      >> simp[]
      >> last_x_assum mp_tac
      >> simp[working_set_def, state_to_context_def]
      >> qmatch_goalsub_abbrev_tac `SND (_ a) ⊆ _ ⇒ SND b ⊆ _`

      >> Q.SUBGOAL_THEN `SND b ⊆ SND a` assume_tac


      >> subgoal `SND b ⊆ SND a`
      >> `SND b ⊆ SND a` suffices_by (simp[SUBSET_DEF,ELIM_UNCURRY,IN_DEF])


      >> last_x_assum mp_tac
      >> simp[state_to_context_def, working_set_def]
      >> qmatch_goalsub_abbrev_tac ‘SND(_ a1) ⊆ _ ⇒ SND a2 ⊆ _’
      >> ‘SND a2 ⊆ SND a1’ suffices_by (simp[SUBSET_DEF,ELIM_UNCURRY,IN_DEF])
      >> MAP_EVERY qunabbrev_tac [‘a1’,‘a2’]


      >> simp[state_to_context_def]
      >> simp[working_set_def]
      >> ``


      >> EVAL_TAC
      >> simp[]

      >> cheat)
  >> rpt cheat
QED

(* ways of simplifying an assumption:
     >> last_x_assum $ assume_tac o SRULE[working_set_def]
fs[working_set_def]

thanks gordon *)


val _ = export_theory ();

