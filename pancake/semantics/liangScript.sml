(*
  Automate verification of the property that Pancake program does not access
  memory that is out of bounds.
*)

(* Below is a glossary of identifiers used in this file.
     * addr: Used for memory addresses.
     * m:    Stands for "memory". Pluralised as ms.
     * v:    Used for Pancake variable names.
     * ws:   Short for "working set". Here, it is usually an upper bound on the
             range of heap addresses that a Pancake program or expression will
             access. Thanks COMP3891!
   *)

open preamble panLangTheory panSemTheory;

val _ = new_theory "liang";


(* Find an upper bound on the working set of a Pancake program. *)

(* The fields are named after the fields of state in panSemTheory. *)
Datatype:
  context = <| memory    : 'a word -> 'a word_lab set ;
               locals    : varname |-> 'a v set ;
               be        : bool ;
               base_addr : 'a word |>
End

(* Find the range of an expression. *)
Definition myrange_def: (* TODO: rename to range *)
  myrange (Const w) ctxt = {Val (Word w)} ∧
  myrange (Var v) ctxt = ctxt.locals ' v ∧
  myrange BaseAddr ctxt = {Val (Word ctxt.base_addr)} ∧
  (* TODO *)
  myrange (e:'a panLang$exp) (ctxt:'a context) = (ARB:'a v set)
End

(* Find an upper bound on the working set of an expression. *)
Definition working_set_exp_def:
  working_set_exp (Const w) (ctxt:'a context) = ({}:'a word set) ∧
  working_set_exp (Var v) ctxt = {} ∧
  working_set_exp (Label fname) ctxt = {} ∧
  working_set_exp (Struct es) ctxt =
    (* XXX: If I reordered the arguments this would not need a λ-abstraction. *)
    FOLDL (λws e. ws ∪ working_set_exp e ctxt) {} es ∧
  working_set_exp (Field index e) ctxt = working_set_exp e ctxt ∧
  working_set_exp (Load shape src) ctxt =
    (let addrs = { addr | Val (Word addr) ∈ myrange src ctxt } in
      { x | (addr, x) | addr ∈ addrs ∧
                        addr ≤ x ∧ x ≤ addr + n2w (size_of_shape shape) }) ∧
  working_set_exp (LoadByte e) ctxt = working_set_exp e ctxt ∧
  working_set_exp (Op op es) ctxt =
    (* XXX: See note above on the Struct case. *)
    FOLDL (λws e. ws ∪ working_set_exp e ctxt) {} es ∧
  working_set_exp (Panop op es) ctxt =
    (* XXX: See note above on the Struct case. *)
    FOLDL (λws e. ws ∪ working_set_exp e ctxt) {} es ∧
  working_set_exp (Cmp cmp e1 e2) ctxt =
    working_set_exp e1 ctxt ∪ working_set_exp e2 ctxt ∧
  working_set_exp (Shift sh e n) ctxt = working_set_exp e ctxt ∧
  working_set_exp BaseAddr ctxt = {}
Termination
  wf_rel_tac `measure (exp_size ARB o FST)`
End

(* Named after mem_store in panSemTheory. *)
Definition mem_store_def:
  mem_store addr w m = (addr =+ {w}) m
End

(* Named after mem_stores in panSemTheory. *)
Definition mem_stores_def:
  mem_stores addr [] m = m ∧
  mem_stores addr (w::ws) m =
    mem_stores (addr + bytes_in_word) ws (mem_store addr w m)
End

(* Named after mem_store_byte in panSemTheory. *)
Definition mem_store_byte_def:
  (* TODO: Figure out set_byte and what we should replace ARB with. *)
  mem_store_byte be addr b m =
    (byte_align addr =+ {Word (set_byte addr b ARB be)}) m
End

Definition context_union_def:
  context_union ctxt1 ctxt2 =
    <| memory    := λw. ctxt1.memory w ∪ ctxt2.memory w ;
       locals    := FMERGE (UNION) ctxt1.locals ctxt2.locals ;
       be        := ctxt1.be ;
       base_addr := ctxt1.base_addr |>
End

(* Find an upper bound on the working set of a program. *)
Definition working_set_def:
  working_set Skip ctxt = (ctxt, {}) ∧
  working_set (Dec v e prog) ctxt =
    (let ws = working_set_exp e ctxt and
         ctxt' = ctxt with locals := ctxt.locals |+ (v, myrange e ctxt);
         (ctxt'', ws') = working_set prog ctxt' in
      (ctxt'', ws ∪ ws')) ∧
  working_set (Assign v src) ctxt =
    (let ws = working_set_exp src ctxt and
         ctxt' = ctxt with locals := ctxt.locals |+ (v, myrange src ctxt) in
      (ctxt', ws)) ∧
  (* XXX: Difficult to compute. *)
  working_set (Store dst src) ctxt =
    (let ws = working_set_exp dst ctxt and
         ws' = working_set_exp src ctxt and
         addrs = { addr | (Val (Word addr)) ∈ myrange dst ctxt };
         (* All possible memory states after performing this store. *)
         ms = { mem_stores addr (flatten value) ctxt.memory
              | addr ∈ addrs ∧ value ∈ myrange src ctxt } in
      (ctxt with memory := (λw. BIGUNION { m w | m ∈ ms }),
       ws ∪ ws' ∪ addrs)) ∧
  working_set (StoreByte dst src) ctxt =
    (let ws = working_set_exp dst ctxt and
         ws' = working_set_exp src ctxt and
         addrs = { addr | (Val (Word addr)) ∈ myrange dst ctxt };
         ms = { mem_store_byte ctxt.be addr (w2w w) ctxt.memory
              | addr ∈ addrs ∧ (Val (Word w)) ∈ myrange src ctxt } in
      (ctxt with memory := (λw. BIGUNION { m w | m ∈ ms }), ws ∪ ws' ∪ addrs)) ∧
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


(* A "nice" modification of the Pancake semantics that does not check for
   out-of-bounds memory accesses. *)

(* The type variables in the types of the functions we are substituting get
   instatiated, so we have to instatiate them the same way. The naming
   convention originates from spec64 in compiler64ProgTheory. *)
val specffi = inst [beta |-> Type `:'ffi`];

(* Remove the universal quanitifications in each equation of a specification.
   This is necessary because definition mechanisms expect to add the
   universal quantifiers themselves. *)
fun spec_eqn_strip_forall tm =
  list_mk_conj (map (snd o strip_forall) (strip_conj tm));

Definition nice_mem_load_def:
  (* TODO *)
  (nice_mem_load One (addr:'a word) (dm:'a word set) (m:'a word -> 'a word_lab) = SOME (Val (m addr)))
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
  (* Taken from the termination proof for eval. *)
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

(* We defined our own mem_stores and mem_store above. But here we need to
   substitute their namesakes in panSemTheory. *)
Overload mem_stores = ``panSem$mem_stores``;
Overload mem_store = ``panSem$mem_store``;

val mem_stores_ty = specffi (ty_antiq (type_of (Term `mem_stores`)));

val mem_stores_def = panSemTheory.mem_stores_def;

Definition nice_mem_stores_def:
  ^(spec_eqn_strip_forall
    (subst
      [ Term `mem_stores:^mem_stores_ty` |->
        Term `nice_mem_stores:^mem_stores_ty`,
        Term `mem_store`                 |-> Term `nice_mem_store` ]
      (concl mem_stores_def)))
End

val evaluate_ty = specffi (ty_antiq (type_of (Term `evaluate`)));

Overload mem_store_byte = ``panSem$mem_store_byte``;

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


(* The major theorem. *)

Definition from_state_def:
  from_state s = <| memory    := (λx. {x}) o s.memory ;
                    locals    := (λx. {x}) o_f s.locals ;
                    be        := s.be ;
                    base_addr := s.base_addr |>
End

(* Useful with DEP_PURE_ONCE_REWRITE_TAC. *)
Theorem no_out_of_bounds:
  SND (heap_use_bound p (from_state s)) ⊆ s.memaddrs ⇒
  evaluate (p, s) = nice_evaluate (p, s)
Proof
  cheat
QED


val _ = export_theory ();












(*


∧
  heap_use_bound (Store dst src) (ctxt:'a context) =
    (let dm = heap_use_bound_exp dst ctxt and
         dm' = heap_use_bound_exp src ctxt in
      (* A function that given
           - a source expression
           - a destination expression
           - and a memory state
          gives a new memory state *)
         memory =  { domemorystores ad (flatten v) ctxt.memory | ad ∈ range dst ctxt ∧ v ∈ range src ctxt }
         memory (x:'a word) = ({}:'a word_lab set) in

(*
('a word -> 'a word_lab set) set ->
'a word -> 'a word_lab set

λx. BIGUNION { memory x | memory ∈ allmemories }

Possible.
*)

      (ctxt with memory := memory, dm ∪ dm'))
End
         memory x = if x ∈ dm then range v ctxt else ctxt.memory x in
      ARB)
End
      (ctxt with memory))
End

Definition range_def:
  range ctxt base_addr (Const w) = Word {w} ∧
  range (ctxt: varname |-> 'a value_set) base_addr (Var v) = ctxt ' v ∧
  range ctxt base_addr (Label f) = Word {} ∧
  range ctxt base_addr (Struct es) = Struct (MAP (range ctxt base_addr) es) ∧
  range ctxt base_addr (Field index e) =
    case range ctxt base_addr e of Struct es => EL index es ∧
  (* TODO: Is this possible? *)
  range ctxt base_addr (Load One e) = Word UNIV ∧
  range ctxt base_addr (Load (Comb shs)) =
    Struct (MAP (λx. range ctxt base_addr (Load x)) shs)
End
  range ctxt base_addr BaseAddr = Word {base_addr} ∧
  (* TODO: Finish this! *)
  range (ctxt:varname |-> 'a word set) base_addr (e:'a panLang$exp) =
    Word (UNIV:'a word set)
End

(* TODO: heap_use_bound_exp_def *)

Definition heap_use_bound_def:
  heap_use_bound ctxt base_addr Skip = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr (Dec v e p) =
    heap_use_bound (ctxt |+ (v, range ctxt base_addr e)) base_addr p ∧
  heap_use_bound ctxt base_addr (Assign v e) =
    (ctxt |+ (v, range ctxt base_addr e), {}) ∧
  heap_use_bound ctxt base_addr (Store ad v) =
    case range ctxt base_addr ad of
    (* XXX: Choose better variable names. *)
    (ctxt, {y | ∃x. x ∈ range ctxt base_addr ad ∧ x ≤ y ∧ y < x + bytes_in_word}) ∧
  heap_use_bound ctxt base_addr (StoreByte ad v) =
    (ctxt, range ctxt base_addr ad) ∧
  heap_use_bound ctxt base_addr (Seq p1 p2) =
    (let (ctxt', dm) = heap_use_bound ctxt base_addr p1 in
      let (ctxt'', dm') = heap_use_bound ctxt' base_addr p2 in
        (ctxt'', dm ∪ dm')) ∧
  heap_use_bound ctxt base_addr (If e c1 c2) =
    (let (ctxt', dm) = heap_use_bound ctxt base_addr c1 in
      let (ctxt'', dm') = heap_use_bound ctxt base_addr c2 in
        (FMERGE (UNION) ctxt' ctxt'', dm ∪ dm')) ∧
  (* This is sound because nice_semantics is equivalent to semantics for
     While terms. *)
  heap_use_bound ctxt base_addr (While e c) = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr Break = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr Continue = (ctxt, {}) ∧
  (* Sound for similar reasons to the While case. *)
  heap_use_bound ctxt base_addr (Call rtyp e es) = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr (ExtCall f ptr1 len1 ptr2 len2) = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr (Raise eid e) = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr (Return e) = (ctxt, {}) ∧
  heap_use_bound ctxt base_addr Tick = (ctxt, {})
End



(* THIS IS TOO MUCH HEADACHE
(* A value_set represents the possible values of a local variable. Here the
   name Value is overloading the word value; it means a value whose size is a
   single word. In other words, its shape is one or it is not a struct. *)
Datatype:
  value_set = Value ('a word_lab set)
            | Struct (value_set list)
End *)

(* New Space - BROKEN *)

Datatype: context = <| locals : varname |-> 'a v ; base_addr : 'a word |>
End

Definition is_prog_safe_for_heap_def:
  ((is_prog_safe_for_heap
    :('a word) set -> 'a panLang$prog -> 'a context
    -> (bool # 'a context))
    dm Skip ctxt = (T, ctxt)) ∧
  (is_prog_safe_for_heap s dm (Dec v e p) ctxt = (T, ctxt)) ∧
  (is_prog_safe_for_heap s dm Tick ctxt = (T, ctxt))
End

Definition body_def:
  body s fname = SND (s.code ' fname)
End

Definition is_safe_for_heap_def:
  (is_safe_for_heap :('a, 'ffi) state -> ('a word) set -> bool) s dm =
    SND (is_prog_safe_for_heap dm (body s "main") FEMPTY)
End

(* Space *)

Type context = ``:varname |-> ('a word) set``;

Definition context_union_def:
  context_union ctxt ctxt' =
    FUN_FMAP
      (λv.
        (case FLOOKUP ctxt v of NONE => EMPTY | SOME x => x) ∪
        (case FLOOKUP ctxt' v of NONE => EMPTY | SOME x => x))
      (FDOM ctxt ∪ FDOM ctxt')
End

Definition f_exp_def:
  f_exp (ctxt:'a context) (e:'a panLang$exp) = {0w}
End

Definition f_def:
  (f (ctxt:'a context) (Skip) = (ctxt, EMPTY)) ∧
  (f ctxt (Dec v e p) =
    f (ctxt |+ (v, f_exp ctxt e)) p) ∧
  (f ctxt (Assign v e) = (ctxt |+ (v, f_exp ctxt e), EMPTY)) ∧
  (f ctxt (Store ad v)) = (ctxt, f_exp ctxt ad) ∧
  (f ctxt (StoreByte dest src) = (ctxt, f_exp ctxt dest)) ∧
  (f ctxt (Seq p p') =
    let (ctxt', dm') = f ctxt p in
      let (ctxt'', dm'') = f ctxt' p' in
        (ctxt'', dm' ∪ dm'')) ∧
  (f ctxt (If e p p') =
    let (ctxt', dm) = f ctxt p in
      let (ctxt'', dm') = f ctxt p' in
        (context_union ctxt' ctxt'', dm ∪ dm' ∪ f_exp ctxt e)) ∧
  (f ctxt (While e p) = (ctxt, UNIV))∧ (* TODO *)
  (f ctxt Break = (ctxt, EMPTY)) ∧
  (f ctxt Continue = (ctxt, EMPTY)) ∧
  (f ctxt (Call rtyp e es) = (ctxt, UNIV)) ∧ (* TODO *)
  (f ctxt (ExtCall f' ptr1 len1 ptr2 len2) = (ctxt, EMPTY)) ∧ (* TODO *)
  (f ctxt (Raise eid excp) = (ctxt, EMPTY)) ∧
  (f ctxt (Return rt) = (ctxt, EMPTY)) ∧
  (f ctxt Tick = (ctxt, EMPTY))
End

(* *)

Definition mem_load'_def:
  (mem_load' One addr dm m = SOME (Val (m addr))) ∧
  (mem_load' sh addr dm m = mem_load sh addr dm m)
End

Definition mem_load_byte'_def:
  mem_load_byte' (m:'a word -> 'a word_lab) (dm:('a word) set) be w =
    case m (byte_align w) of
      (* I wonder if we can also eliminate this check. *)
      | Label _ => NONE
      | Word v => SOME (get_byte w v be)
End

val instffi = inst [``:'b`` |-> ``:'ffi``];

val eval'_def =
  let
    val ty = instffi (ty_antiq (type_of ``eval``))
    val tm = subst
        [ ``eval :^ty``     |-> ``eval' :^ty``,
          ``mem_load``      |-> ``mem_load'``,
          ``mem_load_byte`` |-> ``mem_load_byte'`` ]
        (concl eval_def)
  in
    mk_thm ([], tm)
  end;

val evaluate'_def =
  let
    val ty1 = instffi (ty_antiq (type_of ``eval``))
    val ty2 = instffi (ty_antiq (type_of ``evaluate``))
    val tm = subst
        [ ``eval :^ty1``     |-> ``eval' :^ty1``,
          ``evaluate :^ty2`` |-> ``evaluate' :^ty2`` ]
        (concl evaluate_def)
  in
    mk_thm ([], tm)
  end;

val semantics'_def =
  let
    val ty = instffi (ty_antiq (type_of ``evaluate``))
    val tm = subst
        [ ``evaluate :^ty`` |-> ``evaluate' :^ty`` ]
        (concl semantics_def)
  in
    mk_thm ([], tm)
  end;

(* *)

Theorem x:
  snd (f FEMPTY (panLang$Call NONE (Label start) [])) ⊆ s.memaddrs ⇒
  semantics s start = semantics' s start
Proof
  simp[f_def, semantics'_def]
QED
*)

