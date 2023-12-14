(*
  Scope checking for Pancake.
*)
open preamble panLangTheory

val _ = new_theory "panScope"

Datatype:
  context =
  <| vars  : varname list ;
     funcs : funname list |>
End

Definition scope_check_exp_def:
  (scope_check_exp ctxt (Const c) = T) ∧
  (scope_check_exp ctxt (Var vname) = MEM vname ctxt.vars) ∧
  (scope_check_exp ctxt (Label fname) = MEM fname ctxt.funcs) ∧
  (scope_check_exp ctxt (Struct es) = EVERY (scope_check_exp ctxt) es) ∧
  (scope_check_exp ctxt (Field index e) = scope_check_exp ctxt e) ∧
  (scope_check_exp ctxt (Load sh e) = scope_check_exp ctxt e) ∧
  (scope_check_exp ctxt (LoadByte e) = scope_check_exp ctxt e) ∧
  (scope_check_exp ctxt (Op bop es) = EVERY (scope_check_exp ctxt) es) ∧
  (scope_check_exp ctxt (Panop pop es) =
    EVERY (scope_check_exp ctxt) es) ∧
  (scope_check_exp ctxt (Cmp cmp e e') =
    (scope_check_exp ctxt e ∧ scope_check_exp ctxt e')) ∧
  (scope_check_exp ctxt (Shift sh e n) = scope_check_exp ctxt e) ∧
  (scope_check_exp ctxt BaseAddr = T)
Termination
  wf_rel_tac `measure (λe. exp_size ARB (SND e))`
End

Definition scope_check_def:
  (scope_check ctxt Skip = T) ∧
  (scope_check ctxt (Dec v e p) = (scope_check_exp ctxt e ∧
    scope_check (ctxt with vars := v :: ctxt.vars) p)) ∧
  (scope_check ctxt (Assign v e) =
    (MEM v ctxt.vars ∧ scope_check_exp ctxt e)) ∧
  (scope_check ctxt (Store ad v) =
    (scope_check_exp ctxt ad ∧ scope_check_exp ctxt v)) ∧
  (scope_check ctxt (StoreByte dest src) =
    (scope_check_exp ctxt dest ∧ scope_check_exp ctxt src)) ∧
  (scope_check ctxt (Seq p p') =
    (scope_check ctxt p ∧ scope_check ctxt p')) ∧
  (scope_check ctxt (If e p p') =
    (scope_check_exp ctxt e ∧
      scope_check ctxt p ∧
      scope_check ctxt p')) ∧
  (scope_check ctxt (While e p) =
    (scope_check_exp ctxt e ∧ scope_check ctxt p)) ∧
  (scope_check ctxt Break = T) ∧
  (scope_check ctxt Continue = T) ∧
  (scope_check ctxt (Call rtyp e es) =
    (case rtyp of NONE => T | SOME (rt, hdl) => MEM rt ctxt.funcs ∧
      scope_check_exp ctxt e ∧
      EVERY (scope_check_exp ctxt) es)) ∧
  (scope_check ctxt (ExtCall f ptr1 len1 ptr2 len2) =
    (scope_check_exp ctxt ptr1 ∧
      scope_check_exp ctxt len1 ∧
      scope_check_exp ctxt ptr2 ∧
      scope_check_exp ctxt len2)) ∧
  (scope_check ctxt (Raise eid excp) = scope_check_exp ctxt excp) ∧
  (scope_check ctxt (Return rt) = scope_check_exp ctxt rt) ∧
  (scope_check ctxt Tick = T)
End

Definition scope_check_prog_def:
  scope_check_prog prog =
  let fnames = MAP FST prog;
      bodies = MAP (SND o SND) prog in
    EVERY
      (scope_check <| vars := [] ; funcs := fnames |>)
      bodies
End

val _ = export_theory()
