(*
  Automate verification of the property that Pancake program does not access
  memory that is out of bounds.
*)

(* Below is a glossary of identifiers used in this file.
     * addr:  Used for memory addresses.
     * addrs: Plural of addr.
     * m:     Stands for "memory".
     * ms:    Plural of m.
     * v:     Used for Pancake variable names.
     * ws:    1. Short for "working set". Here, it is usually an upper bound on
              the range of heap addresses that a Pancake program or expression
              will access. Thanks COMP3891! 2. Plural of w.
   *)

open preamble panLangTheory panSemTheory;

val _ = new_theory "liang";


(* Find an upper bound on the working set of a Pancake program. *)

Type memory = (Type `:'a word -> 'a word_lab`)
Type locals = (Type `:varname |-> 'a v`)

(* The fields are named after the fields of state in panSemTheory. *)
Datatype:
  (* XXX: Can I do away with the phantom field ffi? *)
  context = <| memory_locals : ('a memory # 'a locals) set ;
               be            : bool ;
               base_addr     : 'a word ;
               ffi           : 'ffi |>
End

Definition from_state_def:
  from_state s = <| memory_locals := {(s.memory, s.locals)} ;
                    be        := s.be ;
                    base_addr := s.base_addr ;
                    ffi       := ARB |>
End

Definition myrange_def:
 myrange (e:'a panLang$exp) (ctxt:('a, 'ffi) context) =
    { ARB:('a, 'ffi) state | (memory, locals) ∈ ctxt.memory_locals}
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
  working_set_exp (LoadByte e) ctxt =
    (let addrs = { addr | Val (Word addr) ∈ myrange src ctxt } in
      working_set_exp e ctxt ∪ addrs) ∧
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

(* Useful with DEP_PURE_ONCE_REWRITE_TAC. *)
Theorem no_out_of_bounds:
  SND (heap_use_bound p (from_state s)) ⊆ s.memaddrs ⇒
  evaluate (p, s) = nice_evaluate (p, s)
Proof
  cheat
QED


val _ = export_theory ();

