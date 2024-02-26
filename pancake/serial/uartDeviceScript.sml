(*
  Tiana's Proofs
*)
open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory ffiTheory;
open serialPanDrvTheory panSemTheory;

val _ = new_theory "uartDevice"

Datatype:
  reg32=
  <| byte1 : word8
   ; byte2 : word8
   ; byte3 : word8
   ; byte4 : word8
   |>
End

Datatype:
  mmin_dev_state=
  <| err     : bool
   (* ; utrstat : reg32 *)
   ; rxrdy   : bool
   ; txrdy   : bool
   (* ; utxh    : reg32 *)
   (* ; urxh    : reg32 *)
   |>
End

(* (state, action) -> state *)
Definition uart_dev_transition_def:
  (uart_dev_transition [] (s :mmin_dev_state) = s) ∧
  (uart_dev_transition (h::t) (s :mmin_dev_state) =
    case s.err of
      T => s
    | F =>
      (case h of
         IO_event port _ _ =>
         if port = "read_reg_UTRSTAT" then
           uart_dev_transition t s
         else if port = "read_reg_URXH" then
           case s.rxrdy of
             F => s with err := T
           | T => uart_dev_transition t (s with rxrdy := F)
      else if port = "write_reg_UTXH" then
        case s.txrdy of
          F => s with err := T
        | T => uart_dev_transition t s
      else
        (s with err := T)))
End

(* Modified definition:
   (state, action) -> state -> bool
   describes allowed transitions

   implicit assumption that there are no external alterations to state while an
   internal transition is being taken
*)

Definition uart_dev_transition_valid_def:
  uart_dev_transitiion_valid (s :mmin_dev_state) (d ::min_dev_state) a =
    let errs = s.err;
        errd = d.err;
        rxs  = s.txrdy;
        rxd  = d.txrdy;
        txs  = s.rxrdy;
        txd  = s.rxrdy
    in
      case a of
        (IO_event "read_reg_UTRSTAT" _ _) =>
          (errs = errd ∧ rxs = rxd ∧ txs = txd)
      | (IO_event "read_reg_URXH" _ _) => (
          case rxs of
            T => (errs = errd ∧ rxd = F ∧ txs = txd)
          | F => (errd = F ∧ rxd = F ∧ txs = txd))
      | (IO_event "write_reg_UTXH" _ _) => (
          case txs of
            T => (errs = errd ∧ rxs = rxd ∧ txd = F)
          | F => (errd = F ∧ rxs = rxd ∧ txd = F))
      | _ => F
End

(* Yet another definition, only encoding allowed paths which do not result
   in the error state.
   This can probably be adjusted even more to not include err field in state record. *)
Datatype:
  mmmin_dev_state=
   <| rxrdy : bool
    ; txrdy : bool
    |>
End

Definition uart_dev_correct_transition:
  uart_dev_correct_transition (s :mmmin_dev_state) (d :mmmin_dev_state) a =
    let rxs  = s.txrdy;
        rxd  = d.txrdy;
        txs  = s.rxrdy;
        txd  = d.rxrdy
    in
      case a of
        (IO_event "read_reg_UTRSTAT" _ _) =>
          (rxs = rxd ∧ txs = txd)
      | (IO_event "read_reg_URXH" _ _) => (
          case rxs of
            T => (rxd = F ∧ txs = txd)
          | F => F)
      | (IO_event "write_reg_UTXH" _ _) => (
          case txs of
            T => (rxs = rxd ∧ txd = F)
          | F => F)
      | _ => F
End

val _ = EVAL “(λn. REPLICATE n (IO_event "read_reg_UTRSTAT" cb1 (ZIP (rb1,rb1)))
                            ++ [IO_event "read_reg_UTXH" cb2 (ZIP (rb2, rb2))]) 3”;

val _ = EVAL “(λn. REPLICATE n (IO_event "read_reg_UTRSTAT" cb1 (ZIP (rb1,rb2)))) 3”;

Definition n_read_status_def:
  n_read_status_def n cb rb= REPLICATE n (IO_event "read_reg_UTRSTAT" cb (ZIP (rb,rb)))
End

(* *)
Definition mmin_start_state_def:
  mmin_start_state =
    <| err   := F
     ; rxrdy := F
     ; txrdy := T
     |>
End

(*
(* Why isn't this consistent with the definition above? *)
Definition mmmin_start_state_def:
  mmmin_start_state =
    <| rxrdy := F
     ; txrdy := F
     |>
End
*)

(* This is now inconsistent with the definition in the driver proof script. *)
(* Fix later, the driver proofs don't rely on anything here anyway. *)
Definition finite_stat_events_map_def:
  finite_stat_events_map byteps = MAP (λ(c,b). IO_event "read_reg_UTRSTAT" c (ZIP (c,b))) byteps
End

Theorem read_stat_preserve:
  ∀s conf bytes.
    case
      uart_dev_transition [IO_event "read_reg_UTRSTAT" conf (ZIP (conf, bytes))] s
    of
      s' => (s.err = s'.err)
Proof
  simp [uart_dev_transition_def]
QED

Theorem err_no_trans:
  ∀s l. s.err ⇒ s = uart_dev_transition l s
Proof
  strip_tac >> Induct >> rw[uart_dev_transition_def]
QED

Theorem concat_dev_transition_trace:
  ∀h l s. uart_dev_transition (h::l) s = uart_dev_transition l (uart_dev_transition [h] s)
Proof
  rpt strip_tac >>
  simp [uart_dev_transition_def] >>
  rw[err_no_trans] >>
  TOP_CASE_TAC >> rw[] >>
  match_mp_tac err_no_trans >> rw[]
QED

Theorem append_dev_transition_trace:
  ∀l1 l2 s. uart_dev_transition (l1 ++ l2) s = uart_dev_transition l2 (uart_dev_transition l1 s)
Proof
  Induct_on ‘l1’ >> rw[uart_dev_transition_def] >>
  rw [err_no_trans] >>
  TOP_CASE_TAC >> rw[] >>
  match_mp_tac err_no_trans >> rw[]
QED

(* More or less the same as the above. *)
Theorem split_trace_run:
  ∀s s' sf l l1 l2.
    l = l1 ++ l2 ∧ uart_dev_transition l1 s = s' ∧ uart_dev_transition l2 s' = sf ⇒
    uart_dev_transition l s = sf
Proof (* Above proof steps work too. *)
  rw [append_dev_transition_trace]
QED

Theorem read_stat_run_err:
  ∀ls s s'.
    ¬s.err ∧ uart_dev_transition (finite_stat_events_map ls) s = s'
    ⇒ ¬s'.err
Proof
  simp [] >>
  rpt strip_tac >>
  Induct_on ‘LENGTH ls’
  >- (strip_tac >>
      simp [LENGTH_NIL] >>
      simp [finite_stat_events_map_def] >>
      simp [uart_dev_transition_def]) >>
  strip_tac >> fs [] >>
  Cases_on ‘ls’ >- simp [] >>
  rw [finite_stat_events_map_def] >>
  pairarg_tac >> simp [] >>
  simp [Once uart_dev_transition_def] >>
  fs [finite_stat_events_map_def]
QED

(* Renders the above theorem redundant. *)
Theorem uart_stat_run_preserve:
  ∀ls s s'.
    uart_dev_transition (finite_stat_events_map ls) s = s
Proof
  simp [] >>
  rpt strip_tac >>
  Induct_on ‘LENGTH ls’
  >- (strip_tac >>
      simp [LENGTH_NIL] >>
      simp [finite_stat_events_map_def] >>
      simp [uart_dev_transition_def]) >>
  strip_tac >> fs [] >>
  Cases_on ‘ls’ >- simp [] >>
  rw [finite_stat_events_map_def] >>
  pairarg_tac >> simp [] >>
  simp [Once uart_dev_transition_def] >>
  fs [finite_stat_events_map_def]
QED

Theorem drv_getchar_if_events_no_fail:
  ∀conf1 bytes1 conf2 bytes2.
    ¬(uart_dev_transition [IO_event "read_reg_UTRSTAT" conf1 bytes1] mmin_start_state).err
Proof
  rpt strip_tac >>
  fs [uart_dev_transition_def, mmin_start_state_def]
QED


Theorem drv_getchar_get_good:
  ∀s conf1 bytes1 bytes2 conf2 bytes2.
    s = uart_dev_transition
          [IO_event "read_reg_UTRSTAT" conf1 bytes1; IO_event "read_reg_URXH" conf2 bytes2]
          (mmin_start_state with rxrdy := T)
    ⇒
    s.err = F ∧ s.rxrdy = F
Proof
  rpt strip_tac >>
  fs [uart_dev_transition_def, mmin_start_state_def]
QED


Theorem finite_stat_events_hd:
  ∀h t l.
    h::t = finite_stat_events_map l ⇒ (∃c b. h = (IO_event "read_reg_UTRSTAT" c b))
Proof
  rpt strip_tac >>
  fs [finite_stat_events_map_def] >>
  Cases_on ‘l’
  >- fs [] >>
  fs [MAP] >>
  pairarg_tac >>
  fs []
QED

Theorem finite_stat_events_tl:
  ∀h1 h2 t1 t2.
    h1::t1 = finite_stat_events_map (h2::t2) ⇒ t1 = finite_stat_events_map t2
Proof
  rpt strip_tac >>
  simp [finite_stat_events_map_def] >>
  fs [finite_stat_events_map_def]
QED

Theorem finite_stat_events_list:
  ∀h t l.
    h::t = finite_stat_events_map l ⇒
    (∃ld lt. [h] = finite_stat_events_map ld ∧ t = finite_stat_events_map lt)
Proof
  rpt strip_tac >>
  Cases_on ‘l’ >- fs [finite_stat_events_map_def] >>
  fs [finite_stat_events_map_def] >> metis_tac []
QED

Theorem uart_dev_transition_stat_app_pre:
   ∀s l l' tl.
     l = finite_stat_events_map l' ⇒
     uart_dev_transition (l ++ tl) s = uart_dev_transition tl s
Proof
  Induct_on ‘l’ >>
  simp [] >>
  rpt strip_tac >>
  imp_res_tac finite_stat_events_hd >> fs [uart_dev_transition_def] >>
  Cases_on ‘s.err’
  >- simp [err_no_trans] >>
  imp_res_tac finite_stat_events_list >> fs[]
QED

Theorem uart_dev_transition_err_stat_app_pre:
  ∀s l l' le.
    l = finite_stat_events_map l' ⇒
    (uart_dev_transition le s).err = (uart_dev_transition (l ++ le) s).err
Proof
  rpt strip_tac >>
  imp_res_tac uart_dev_transition_stat_app_pre >>
  fs []
QED

Theorem drv_putchar_events:
  ∀conf1 bytes1 conf2 bytes2 l.
    ¬(uart_dev_transition ((finite_stat_events_map l) ++ [IO_event "write_reg_UTXH" conf2 bytes2])
        mmin_start_state).err
Proof
  rw [mmin_start_state_def] >>
  assume_tac (GSYM uart_dev_transition_err_stat_app_pre) >> fs [] >>
  simp [uart_dev_transition_def]
QED

Definition trace_included_def:
  (trace_included [] _ = T) ∧
  (trace_included (t::ts) [] = F) ∧
  (trace_included (t::ts) (x::xs) =
   ((t=x ∧ trace_included ts xs) ∨ (t≠x ∧ trace_included (t::ts) xs)))
End

(* Same as above, but the extra values in the x::xs list may only contain status
   read IO events. *)
Definition trace_status_interleaved_def:
  (trace_status_interleaved [] [] = T)  ∧
  (trace_status_interleaved [] (x::xs) = (∃l. (x::xs) = finite_stat_events_map l)) ∧
  (trace_status_interleaved (t::ts) [] = F) ∧
  (trace_status_interleaved (t::ts) (x::xs) = ((t=x ∧ trace_status_interleaved ts xs)
    ∨ (t≠x ∧ (∃c b. x = IO_event "read_reg_UTRSTAT" c (ZIP (c,b)))
     ∧ trace_status_interleaved (t::ts) xs)))
End

Theorem trace_status_interleaved_nil_cons:
  ∀h t.
    trace_status_interleaved [] (h::t) ⇒
    ∃c b l. h = IO_event "read_reg_UTRSTAT" c b ∧ t = finite_stat_events_map l
Proof
  rpt strip_tac >>
  fs [trace_status_interleaved_def] >>
  imp_res_tac finite_stat_events_hd >>
  simp [] >>
  Cases_on ‘l’ >- fs [finite_stat_events_map_def] >>
  imp_res_tac finite_stat_events_tl >>
  metis_tac []
QED

Theorem trace_status_interleaved_nil_stat_map:
  ∀l. trace_status_interleaved [] (finite_stat_events_map l)
Proof
  strip_tac >>
  Cases_on ‘l’
  >- simp [finite_stat_events_map_def, trace_status_interleaved_def] >>
  qmatch_goalsub_abbrev_tac ‘trace_status_interleaved [] casels’ >>
  Cases_on ‘casels’ >- simp [trace_status_interleaved_def] >>
  simp [trace_status_interleaved_def] >> metis_tac []
QED

(* Inserting a finite number of status reads into an existing trace does not alter
   the state at the end of a run. *)
Theorem stat_read_interleaving_preseve:
  ∀s ls ts.
    trace_status_interleaved ts ls ⇒ uart_dev_transition ts s = uart_dev_transition ls s
Proof
  CONV_TAC(RESORT_FORALL_CONV List.rev) >>
  recInduct trace_status_interleaved_ind >>
  rpt strip_tac
  >- simp []
  >- (fs [trace_status_interleaved_def] >>
      simp [uart_dev_transition_def, uart_stat_run_preserve])
  >- (fs [trace_status_interleaved_def]) >>
  fs [trace_status_interleaved_def]
  >- (once_rewrite_tac[concat_dev_transition_trace] >>
      simp[])
  >- rw[uart_dev_transition_def,err_no_trans]
QED

(* Only one additional transition - write to URXH by external device which
   sets RX to be ready for reading.
   Assume that external device is allowed to overwrite current RX buffer even if
   it is full. *)
Definition extended_dev_transition_def:
  (extended_dev_transition [] (s :mmin_dev_state) = s) ∧
  (extended_dev_transition (h::t) (s :mmin_dev_state) =
   case s.err of
      T => s
    | F =>
        (case h of
           IO_event port _ _ =>
             if port = "read_reg_UTRSTAT" then
               extended_dev_transition t s
             else if port = "read_reg_URXH" then
               case s.rxrdy of
                 F => s with err := T
               | T => extended_dev_transition t (s with rxrdy := F)
             else if port = "write_reg_UTXH" then
               case s.txrdy of
                 F => s with err := T
               | T => extended_dev_transition t s
             else if port = "ext_write_reg_URXH" then
               extended_dev_transition t (s with rxrdy := T)
             else
               (s with err := T)))
End

Theorem err_no_ext_trans:
  ∀s l. s.err ⇒ s = extended_dev_transition l s
Proof
  strip_tac >> Induct >> rw[extended_dev_transition_def]
QED

Definition is_ext_write_def:
  is_ext_write e = (∃c1 b1. e = IO_event "ext_write_reg_URXH" c1 b1)
End

(* ts is the sublist of ls obtained by removing external blue transitions *)
Definition events_ext_writes_interleaved_def:
  events_ext_writes_interleaved ts ls = (ts = FILTER is_ext_write ls)
End

(*
Theorem pancake_uart_driver's_hopefully_last_theorem:
 ∀io_trace ts s l conf bytes.
   io_trace = (finite_stat_events_map l) ++ [IO_event "write_reg_UTXH" conf bytes] ∧
   events_ext_writes_interleaved io_trace ts ∧
   ¬(uart_dev_transition io_trace mmin_start_state).err ⇒
   ¬(extended_dev_transition ts mmin_start_state).err
Proof
  Induct_on ‘ts’
  >- fs [events_ext_writes_interleaved_def] >>
  rpt strip_tac >>
  fs [events_ext_writes_interleaved_def, is_ext_write_def] >>
QED
*)

(* Intuitively this should be true, because external writes only change the RX buffer status from
   F -> T, which should not cause any additional errors [you would hope.] *)
(* io_trace is a trace obtained by removing the external transitions from ts, so here io_trace is the minimised
   trace without interference.  *)
(* If executing the original trace from the start state does not end in an error state, intefering with this trace
   will not cause any errors either. *)
Theorem pancake_uart_driver's_hopefully_second_last_theorem:
 ∀ts io_trace .
   events_ext_writes_interleaved io_trace ts ∧
   ¬(uart_dev_transition io_trace mmin_start_state).err ⇒
   ¬(extended_dev_transition ts mmin_start_state).err
Proof
  Induct_on ‘ts’
  >- rw [events_ext_writes_interleaved_def, extended_dev_transition_def, mmin_start_state_def] >>
  strip_tac >> strip_tac >> strip_tac >>
  fs [events_ext_writes_interleaved_def] >>
  FULL_CASE_TAC
  >- (
    gvs [FILTER] >>


  )



     Induct_on ‘io_trace’
     >- (
       Cases_on ‘ts’
       >- (
         rw [events_ext_writes_interleaved_def, uart_dev_transition_def, mmin_start_state_def,
             extended_dev_transition_def]
       ) >>
       rw [] >>

     )
QED

Theorem rx_truer_no_more_err:
  ∀ts s.
    ¬(uart_dev_transition ts s).err ⇒ ¬(uart_dev_transition ts (s with rxrdy := T)).err
Proof
  Induct_on ‘ts’
  >- simp [uart_dev_transition_def] >>
  ntac 2 strip_tac >>
  rw [Once concat_dev_transition_trace] >>


QED

val _ = export_theory();


(* Desired proof list:

*)

(*
Datatype:
  dev_state=
  <| descript : string
   ; ulcon    : reg32
   ; ucon     : reg32
   ; ufcon    : reg32
   ; utrstat  : reg32
   ; uerstat  : reg32
   ; ufstat   : reg32
   ; utxh     : reg32
   ; urxh     : reg32
   ; ubrdiv   : reg32
   ; ufracval : reg32
   ; uintp    : reg32
   ; uintsp   : reg32
   ; uintm    : reg32
   |>
End
*)
