(*
  Tiana's Proofs
*)
open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory;
(* labPropsTheory; *)
open serialPanDrvTheory panSemTheory;

val _ = new_theory "serialPanDrvProof"


(*
spose_not_then (fn thm => all_tac) >>

K, C, W;

Notes:

  - device oracle is annoying in itself
      * can use ugly assumptions to rule out unintended branches
      * more readable (and somewhat more valuable) assumptions can be stated, but these
          are annoying in proofs
  - theorems for clearer connection between heap state & ffi bytes returned
      [this is probably clear to HOL anyway, just hard to read as an inexperienced user]
*)

(* Copy-pasted from labProps. *)
val good_dimindex_def = Define `
  good_dimindex (:'a) <=> dimindex (:'a) = 32 \/ dimindex (:'a) = 64`;

Theorem good_dimindex_get_byte_set_byte:
  good_dimindex (:'a) ==>
    (get_byte a (set_byte (a:'a word) b w be) be = b)
Proof
  strip_tac \\
  match_mp_tac byteTheory.get_byte_set_byte \\
  fs[good_dimindex_def]
QED

Datatype:
  reg32=
  <| byte1 : word8
   ; byte2 : word8
   ; byte3 : word8
   ; byte4 : word8
   |>
End

(* :'ffi *)
Datatype:
  uart_ffi=
  <| utrstat : reg32 llist
   ; rxbuf   : reg32 llist
   |>
End

Definition uart_ffi_oracle_def:
  (uart_ffi_oracle :uart_ffi oracle) port st conf bytes=
  case port of
    "write_reg_UTXH" => (if LENGTH conf >= 0 then Oracle_return st bytes
                         else Oracle_final FFI_failed)
  | "read_reg_UTRSTAT" => (
      if LENGTH bytes >= 4 then
        case st.utrstat of
          [||] => Oracle_final FFI_failed
        | hd:::tl =>
            Oracle_return (st with utrstat := tl)
              [hd.byte1; hd.byte2; hd.byte3; hd.byte4]
      else Oracle_final FFI_failed)
  | "read_reg_URXH" => (
      if LENGTH bytes >= 4 then
        case st.rxbuf of
          [||] => Oracle_final FFI_failed
        | hd:::tl =>
                Oracle_return (st with rxbuf := tl)
                  [hd.byte1; hd.byte2; hd.byte3; hd.byte4]
      else Oracle_final FFI_failed)
  | _ => Oracle_final FFI_failed
End

(* Results in less string-matching case expr. mess. *)
Definition uart_ffi_oracle_alt_def:
  (uart_ffi_oracle_alt :uart_ffi oracle) port st conf bytes =
  if port = "write_reg_UTXH" then
    (if LENGTH conf >= 0 then Oracle_return st bytes
     else Oracle_final FFI_failed)
  else if port = "read_reg_UTRSTAT" then
    (if LENGTH bytes >= 4 then
       case st.utrstat of
         [||] => Oracle_final FFI_failed
       | hd:::tl =>
           Oracle_return (st with utrstat := tl)
                         [hd.byte1; hd.byte2; hd.byte3; hd.byte4]
     else Oracle_final FFI_failed)
  else if port = "read_reg_URXH" then
    (if LENGTH bytes >= 4 then
       case st.rxbuf of
         [||] => Oracle_final FFI_failed
       | hd:::tl =>
           Oracle_return (st with rxbuf := tl)
                         [hd.byte1; hd.byte2; hd.byte3; hd.byte4]
     else Oracle_final FFI_failed)
  else
    Oracle_final FFI_failed
End

(*
(* W.T.P. conf preserved & connect contents of bytes w/ ll in ffi state. *)
(* Most useful level to state this might be at call_FFI. *)
Theorem call_utrstat_ffi_conf:
  ∀s.
    statll = hs:::tls ∧ rxt = hm:::tlm ∧
    s = uart_altffi_state statll rxt ⇒
    callFFI s "read_reg_URXH" conf bytes = FFI return s'

Proof
QED

Theorem utrstat_ffi_out:
  ∀s ffi statt rxt hs tls hm tlm.
    statt = hs:::tls ∧ rxt = hm:::tlm ⇒
    uart_ffi_oracle_alt "read_reg_URXH" stream conf bytes = Oracle_return
Proof
QED

Theorem utrstat_oracle_out:
  ∀s ffi statt rxt hs tls hm tlm.
    statt = hs:::tls ∧ rxt = hm:::tlm ⇒
    uart_ffi_oracle_alt "read_reg_URXH" hs tls =
Proof
QED
*)

(* Despite the slightly misleading name, the use of this definition isn't limited to the start
 of evaluation. *)
Definition init_uart_ffi_def:
  init_uart_ffi stat rx= <| utrstat := stat; rxbuf := rx |>
End

(* With alternative oracle. *)
(* For *initial* oracle state. *)
Definition uart_altffi_state_def:
   uart_altffi_state stat rx =
  <| oracle := uart_ffi_oracle_alt
   ; ffi_state := init_uart_ffi stat rx
   ; io_events := []
   |> :uart_ffi ffi_state
End

(* More general version of the definition above. *)
Definition uart_genffi_state_def:
   uart_genffi_state stat rx ts=
  <| oracle := uart_ffi_oracle_alt
   ; ffi_state := init_uart_ffi stat rx
   ; io_events := ts
   |> :uart_ffi ffi_state
End

(* Why isn't this using the alternative oracle ? *)
Definition init_uart_ffi_state_def:
  init_uart_ffi_state stat rx =
  <| oracle := uart_ffi_oracle
   ; ffi_state := init_uart_ffi stat rx
   ; io_events := []
   |> :uart_ffi ffi_state
End

Definition init_drv_state_def:
  init_drv_state ck be mem memaddrs ffi base_addr =
  <| locals := FEMPTY;
     code := FEMPTY |++ serialProg;
     eshapes := FEMPTY; (* TODO: should there be something here? *)
     memory := mem;
     memaddrs := memaddrs;
     clock := ck;
     be := be;
     ffi := ffi;
     base_addr := base_addr;
    |>
End

Definition init_drv_state_uffi_def:
  init_drv_state_uffi ck be mem memaddrs stat rx base_addr =
  <| locals := FEMPTY;
     code := FEMPTY |++ serialProg;
     eshapes := FEMPTY; (* TODO: should there be something here? *)
     memory := mem;
     memaddrs := memaddrs;
     clock := ck;
     be := be;
     ffi := uart_altffi_state stat rx;
     base_addr := base_addr;
    |>
End

Definition gen_drv_state_uffi_def:
  gen_drv_state_uffi loc es ck be mem memaddrs stat rx ts base_addr =
  <| locals := loc;
     code := FEMPTY |++ serialProg;
     eshapes := es; (* Shape of exception related variables ? *)
     memory := mem;
     memaddrs := memaddrs;
     clock := ck;
     be := be;
     ffi := uart_genffi_state stat rx ts;
     base_addr := base_addr;
    |>
End

(* Has data. *)
Definition utrstat_rxbuf_ready_def:
  utrstat_rxbuf_ready r = if (r.byte4 && 1w ≠ 0w) then T else F
End

Definition state_rxbuf_ready_def:
  state_rxbuf_ready s = utrstat_rxbuf_ready (THE (LHD (s.ffi.ffi_state.utrstat)))
End

val RXBUF_READY_const= “(Shift Lsl (Const 1w) 0) :64 panLang$exp”;

val TXBUF_EMPTY_const= “(Shift Lsl (Const 1w) 1) :64 panLang$exp”;

(* Has empty buffer for transmit. *)
Definition utrstat_txbuf_empty_def:
  utrstat_txbuf_empty r= if (r.byte4 && (1w << 1) ≠ 0w) then T else F
End

Definition ll_txbuf_empty_def:
  ll_txbuf_empty statll = utrstat_txbuf_empty (THE (LHD statll))
End

Definition state_txbuf_empty_def:
  state_txbuf_empty s = utrstat_txbuf_empty (THE (LHD (s.ffi.ffi_state.utrstat)))
End

Theorem state_iff_ll_txbuf_empty:
  ∀s ll. s.ffi.ffi_state.utrstat = ll
         ⇒
         state_txbuf_empty s = ll_txbuf_empty ll
Proof
  rw [ll_txbuf_empty_def, state_txbuf_empty_def]
QED

Definition eventually_state_txbuf_empty_def:
  eventually_state_txbuf_empty s = eventually ll_txbuf_empty s.ffi.ffi_state.utrstat
End

Definition finite_stat_IO_map_def:
  finite_stat_IO_map byteps = MAP (λ(c,ib,rb). IO_event "read_reg_UTRSTAT" c (ZIP (ib,rb))) byteps
End

Theorem llist_hd_drop:
  lls ≠ [||] ⇒
  lls = (THE $ LHD lls) ::: (THE $ LTL lls)
Proof
  Cases_on ‘lls’ >- simp [] >>
  rw [LHD_THM, LTL_THM]
QED

Theorem llist_convoluted_tail:
  lls = lhd:::ltl ∧ ltl ≠ [||] ⇒
  THE (LTL lls) = (HD $ THE $ LTAKE 1 ltl) ::: (THE $ LDROP 1 ltl)
Proof
  Cases_on ‘ltl’ >- simp [] >>
  rw [CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV LTAKE, LHD_THM, LTL_THM]
QED

Theorem llist_convoluted_tail_q:
  ∀ lls lhd ltl.
    lls = lhd:::ltl ∧ ltl ≠ [||] ⇒
    THE (LTL lls) = (HD $ THE $ LTAKE 1 ltl) ::: (THE $ LDROP 1 ltl)
Proof
  Cases_on ‘ltl’ >- simp [] >>
  rw [CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV LTAKE, LHD_THM, LTL_THM]
QED

Theorem llist_another_convoluted_tail:
  lls = lhd:::ltl ∧ ltl ≠ [||] ⇒
  THE (LTL lls) = (HD $ DROP 1 $ THE $ LTAKE 2 lls) ::: (THE $ LDROP 2 lls)
Proof
  Cases_on ‘lls’ >- simp [] >>
  rw [LTL, THE_DEF] >>
  Cases_on ‘ltl’ >- fs [] >>
  rw [DROP,CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV LTAKE,
      CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV LDROP]
QED

Theorem unit_mask_get_byte:
  (1w && w:word64) = w2w(1w && get_byte 7w w T)
Proof
  EVAL_TAC >>
  blastLib.FULL_BBLAST_TAC
QED

Theorem two_mask_get_byte:
  (2w && w:word64) = w2w(2w && get_byte 7w w T)
Proof
  EVAL_TAC >>
  blastLib.FULL_BBLAST_TAC
QED

Theorem unit_mask_get_byte_le:
  (1w && w:word64) = w2w(1w && get_byte 0w w F)
Proof
  EVAL_TAC >>
  blastLib.FULL_BBLAST_TAC
QED

Theorem mem_store_byte_SOME_read_not_label:
  ∀mem memaddrs be addr byte mem'.
    SOME mem' = mem_store_byte mem memaddrs be addr byte ∧
    byte_aligned addr
    ⇒ ∃x. mem' addr = Word x
Proof
  rpt strip_tac >>
  gvs [mem_store_byte_def,AllCaseEqs(),byte_align_aligned,APPLY_UPDATE_THM]
QED

Theorem bytes_in_word_ge_zero:
  good_dimindex (:α) ⇒ bytes_in_word > (0w :α word)
Proof
  simp [bytes_in_word_def,good_dimindex_def] >>
  rw[] >>
  blastLib.BBLAST_TAC >>
  rw [dimword_def,INT_MIN_def] >>
  EVAL_TAC >>
  rw [dimword_def]
QED

Theorem add_words_greater_zero:
  w1 ≥ 0w ∧ w2 > 0w ⇒ w1 + w2 > 0w
Proof
  rw [] >>
  blastLib.BBLAST_TAC >>
  rw [dimword_def,INT_MIN_def] >>
  (* Similar to below .. require assumption to proceed. *)

QED

Theorem not_zero_add_bytes_in_word:
  good_dimindex (:α) ∧ (w :α word) ≥ 0w ⇒ w + bytes_in_word > 0w
Proof
  rw [bytes_in_word_def,good_dimindex_def]>>
  rw [dimword_def] >>
  blastLib.BBLAST_TAC >>
  rw [dimword_def,INT_MIN_def] >> (* w + 4w doesn't exceed (?) the maximum allowed value for
  a machine word - this needs to be assumed .. *)

  rw [WORD_ADD_LEFT_LO] >>
  rw [WORD_LOWER_TRANS] >>

QED

(* Why did I ever need this ?*)
Theorem mem_stores_words_read_word:
  ∀addr words memaddrs mem mem' x.
    (mem_stores addr words memaddrs mem = SOME mem') ∧ words ≠ [] ∧ (HD words = Word x) ⇒
    (mem' addr = Word x)
Proof
  (* Are case splits enough ? *)
  rpt strip_tac >>
  Cases_on ‘words’ >- fs [] >>
  gvs [HD,mem_stores_def,AllCaseEqs(),mem_store_def] >>

QED


Theorem mem_stores_after:
  ∀x addr words memaddrs wlen mem mem' mem''.
    (mem_store addr (Word x) memaddrs mem = SOME mem') ∧
    (mem_stores (addr + wlen) words memaddrs mem' = SOME mem'') ∧
    wlen + bytes_in_word > addr + bytes_in_word ∨ wlen + bytes_in_word < addr - (bytes_in_word - 1) ? . [something something dimindex] ⇒
    (mem'' addr = Word x)

Proof


Theorem mem_stores_after:
  ∀x addr words memaddrs wlen mem mem' mem''.
    (mem_store addr (Word x) memaddrs mem = SOME mem') ∧
    (mem_stores (addr + wlen) words memaddrs mem' = SOME mem'') ∧
    wlen ≥ 0w ∧ wlen + bytes_in_word > INT_MIN ... [something something dimindex] ⇒
    (mem'' addr = Word x)

Proof
  (* Necessary assumptions. *)


  (* For the old goal statement. *)
  ntac 4 strip_tac >>
  gvs [mem_store_def] >>
  Induct_on ‘words’ >> rw []
  >- (fs [mem_stores_def] >> rw [APPLY_UPDATE_THM]) >>
  fs [mem_stores_def,AllCaseEqs(),mem_store_def] >>
  qmatch_asmsub_abbrev_tac ‘mem_stores _ _ _ intmem = SOME mem''’ >>
  last_x_assum $ qspecl_then [‘wlen + bytes_in_word’,‘intmem’,‘mem''’] assume_tac >>
  gvs [markerTheory.Abbrev_def,APPLY_UPDATE_THM] >>
  pop_assum irule >>
  rw []
  >- ((* This one probably requires additional assumptions "no wraparound" ..
         Wraparound may actually be fine ... if wraparound occurs, the closest possible
         location might still be one from the existing data ? I don't believe this yet.
         Actually this may be true even if this is the case - ! TRY LATER !.
         You may want to drop the wlen ≠ 0w assumption too ? *)

  cheat )
  >- (rw [UPDATE_COMMUTES] >>
      ‘addr' ≠ addr' + wlen’ by cheat >>
      fs [UPDATE_COMMUTES])
QED






  rpt strip_tac >>
  Induct_on ‘words’ >> rw[]

  (* Probably this one. *)
  Induct_on ‘words’ >> rw [] >>
  gvs[mem_stores_def,mem_store_def,AllCaseEqs()] >>
  last_assum drule >>
  Ho_Rewrite.PURE_REWRITE_TAC [GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  rw [] >>
  Cases_on ‘words’
  >- (
    gvs [mem_stores_def] >>
    rw [APPLY_UPDATE_THM]
  ) >>
  gvs [] >>
  last_assum drule >>
  rw [] >>
  g
  gvs [mem_stores_def]

  gvs [] >>


  Cases_on ‘words’ >> simp []
  >- fs [] >>
  gvs [HD] >>
  gvs[mem_stores_def,mem_store_def,AllCaseEqs()] >>
  rename1 ‘mem_stores _ vs _ _ = _’ >>
  Cases_on ‘vs’ >> fs [mem_stores_def]
  >- rw [APPLY_UPDATE_THM] >>
  gvs []


QED


(* Store byte won't successfully store a label. *)
Theorem mem_store_byte_label:
  ∀mem memaddrs be addr byte mem' raddr l.
    (mem_store_byte mem memaddrs be addr byte = SOME mem') ∧ (mem' raddr = Label l)
    ⇒ (mem raddr = Label l)
Proof
cheat
QED

Theorem get_byte_set_byte2:
  8 ≤ dimindex (:α) ∧ w2n a MOD 8 ≠ w2n a' MOD 8 ⇒
  get_byte (a:α word) (set_byte a' b w be) be = get_byte a w be
Proof
  cheat
QED


Theorem set_byte_add_aligned:
     w2n a MOD (dimindex (:α) DIV 8) = 0 ∧ 8 ≤ dimindex(:'a) ⇒
     set_byte ((a:'a word) + a') b w be = set_byte a' b w be
Proof
  strip_tac >> match_mp_tac set_byte_change_a >>
  simp[word_add_def] >>
  ‘∃k. dimword(:α) = (dimindex (:α) DIV 8)*k ∧ 0 < k’ by cheat >>
  ASM_SIMP_TAC std_ss [] >>
  dep_rewrite.DEP_REWRITE_TAC[MOD_MULT_MOD] >>
  simp[] >>
  conj_tac >- (qpat_x_assum ‘8 ≤ _’ mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC) >>
  qpat_x_assum ‘dimword (:α) = _’ kall_tac >>
  qpat_x_assum ‘_ = _’ mp_tac >> dep_rewrite.DEP_REWRITE_TAC[MOD_EQ_0_DIVISOR] >>
  rw[] >- (pop_assum mp_tac >> intLib.COOPER_TAC) >>
  ASM_SIMP_TAC std_ss [] >>
  dep_rewrite.DEP_REWRITE_TAC[MOD_TIMES] >>
  intLib.COOPER_TAC
QED

Theorem set_byte_MOD_aligned:
  set_byte (a) b w be = set_byte (n2w(w2n a MOD 8)) b w be
Proof
  cheat
QED

Theorem gen_to_init_drv_state:
  ∀ ck be mem memaddrs statt rxt base_addr.
    init_drv_state_uffi ck be mem memaddrs statt rxt base_addr
    = gen_drv_state_uffi FEMPTY FEMPTY ck be mem memaddrs statt rxt [] base_addr
Proof
  rw [init_drv_state_uffi_def, gen_drv_state_uffi_def,uart_altffi_state_def,uart_genffi_state_def]
QED

Theorem gen_to_init_drv_state_mp:
  ∀ loc es ck be mem memaddrs statt rxt ts base_addr.
    loc = FEMPTY ∧ es = FEMPTY ∧ ts = [] ⇒
    init_drv_state_uffi ck be mem memaddrs statt rxt base_addr
    = gen_drv_state_uffi loc es ck be mem memaddrs statt rxt ts base_addr
Proof
  rw [init_drv_state_uffi_def, gen_drv_state_uffi_def,uart_altffi_state_def,uart_genffi_state_def]
QED


Theorem gen_drv_putChar_evaluate_all_univ:
  ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c ck.
      eventually_state_txbuf_empty s ∧ s = gen_drv_state_uffi loc es ck T mem memaddrs statt rxt ts base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = ts ++ finite_stat_IO_map bytels
             ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T

Proof
  rewrite_tac [eventually_state_txbuf_empty_def] >>
  Ho_Rewrite.PURE_REWRITE_TAC [GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ntac 2 strip_tac >>
  qmatch_asmsub_abbrev_tac ‘eventually _ ll’ >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qid_spec_tac ‘s’ >>
  Ho_Rewrite.PURE_REWRITE_TAC[AND_IMP_INTRO,PULL_FORALL] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘ll’ >>
  ho_match_mp_tac eventually_ind >>

  cheat
QED

Theorem gen_state_putChar_assm:
  ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c.
    mess_of_assums ⇒
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') => T
      | _ => F
Proof
  rewrite_tac [eventually_state_txbuf_empty_def] >>
  Ho_Rewrite.PURE_REWRITE_TAC [RIGHT_EXISTS_IMP_THM,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ntac 3 strip_tac >>
  qmatch_asmsub_abbrev_tac ‘eventually _ ll’ >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qid_spec_tac ‘s’ >>
  Ho_Rewrite.PURE_REWRITE_TAC[AND_IMP_INTRO,PULL_FORALL] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘ll’ >>
  ho_match_mp_tac eventually_ind >> rw []
  >- (
QED

(* Work out necessary assumptions here. *)


Theorem gen_state_base_case:
  ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c.
    byte_aligned base_addr ∧
    read_bytearray base_addr 8 (mem_load_byte mem memaddrs T) = SOME rm1 ∧
    read_bytearray (base_addr + 8w) 4 (mem_load_byte mem memaddrs T) = SOME rm2 ∧
    mem_load_byte m1 memaddrs T (base_addr + 8w) = SOME b1 ∧
    mem_load_byte m2 memaddrs T (base_addr + 9w) = SOME b2 ∧
    mem_load_byte m3 memaddrs T (base_addr + 10w) = SOME b3 ∧
    mem_load_byte m4 memaddrs T (base_addr + 11w) = SOME b4 ∧
    mem_stores (base_addr + 16w) [Word 0w] memaddrs
      (write_bytearray (base_addr + 8w) [hs.byte1; hs.byte2; hs.byte3; hs.byte4] mem memaddrs T) = SOME m1 ∧
    mem_store_byte m1 memaddrs T (base_addr + 20w) (w2w ((w2w :word8 -> word64) b1)) = SOME m2 ∧
    mem_store_byte m2 memaddrs T (base_addr + 21w) (w2w ((w2w :word8 -> word64) b2)) = SOME m3 ∧
    mem_store_byte m3 memaddrs T (base_addr + 22w) (w2w ((w2w :word8 -> word64) b3)) = SOME m4 ∧
    mem_store_byte m4 memaddrs T (base_addr + 23w) (w2w ((w2w :word8 -> word64) b4)) = SOME m5 ∧
    base_addr + 8w ∈ memaddrs ∧
    base_addr + 16w ∈ memaddrs
    ⇒
    ∃ck.
     ll_txbuf_empty s.ffi.ffi_state.utrstat ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') => T
      | _ => F
Proof
  rpt strip_tac >>
  qexists_tac ‘3’ >>
  rw [ll_txbuf_empty_def, init_drv_state_uffi_def,utrstat_txbuf_empty_def] >>
  rw [serialProg_def,uart_drv_putcharFun_def,uart_drv_getcharFun_def, Once evaluate_def,dec_clock_def,
      init_drv_state_uffi_def,eval_def,OPT_MMAP_def,lookup_code_def,flookup_fupdate_list]
  >- ( (* ___ modifying the code changed up the ‘evaluate’s here. *)
    simp [Once evaluate_def] >> (* For ‘Seq’ *)
    qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def] >>
    qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>

    (* Two more definitions for ‘Op’ *)
    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
    qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def] >>
    qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def] >>
    qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,dec_clock_def] >>
    qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    (* For ‘ExtCall’ *)
    simp [Once evaluate_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM] >>

    (* ‘call_FFI’ for this specific FFI oracle. *)
    simp [ffiTheory.call_FFI_def,uart_altffi_state_def,init_uart_ffi_def,
         uart_ffi_oracle_alt_def] >>
    imp_res_tac read_bytearray_LENGTH >> rw[] >>

    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,flatten_def] >>
    simp [Abbr ‘a9’] >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    simp [Abbr ‘a9’] >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    simp [Abbr ‘a9’] >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    simp [Abbr ‘a9’] >>

    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    simp [Abbr ‘a9’] >>

    simp [Once evaluate_def] >>
    simp [Abbr ‘a8’] >>

    (* This part is ugly due to the mem_load from memory with lots of historically stored bytes. *)
    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
          wordLangTheory.word_sh_def,asmTheory.word_cmp_def] >>
    simp [mem_load_def] >>
    gvs [THE_DEF, LHD,uart_altffi_state_def,init_uart_ffi_def,llist_rep_LCONS] >>
    IF_CASES_TAC    (* ___ *)
    >- (
      Cases_on ‘m5 (base_addr + 16w)’ >> gvs []

      >- (
      rpt $ dxrule_all_then assume_tac mem_store_byte_label >> (* No effect. Should it have one ? *)
      rw [AllCaseEqs()] >> (* This produces a split. *)
      simp [Once evaluate_def] >>
      simp [Abbr ‘a7’] >>
      (* Should find a contradiction in assumptions here. *)
      spose_not_then kall_tac >>
      rpt (qhdtm_x_assum ‘Abbrev’ kall_tac) >> (* Where did the two subgoals come from ?*)


      gvs [mem_store_byte_def,byte_align_def,byte_aligned_def,
           mem_stores_def,mem_stores_def,mem_store_def] >>
      gvs[align_add_aligned_gen] >>
      gvs[align_def,APPLY_UPDATE_THM] >>
      gvs[align_def,AllCaseEqs(),mem_load_def,APPLY_UPDATE_THM] >>
      gvs[align_add_aligned_gen] >>
      gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>
      (* Not great ... lost necessary info on where hs.byte4 was stored. *)

      gvs [write_bytearray_def] >>

      gvs [set_byte_def] >>

      blastLib.FULL_BBLAST_TAC >>

      gvs [byte_index_def,word_slice_alt_def] >>
      rw []





      qpat_x_assum ‘mem_store _’ mp_tac


      gvs [mem_store_def, write_bytearray_def,mem_store_byte_def]

      imp_res_tac mem_store_byte_label >>
      pop_assum $ qspecl_then [‘memaddrs’,‘mem'’] mp_tac


    ) >>

    (* Can we try to collapse the memory-related assumptions now ? *)


    gvs [mem_store_byte_def,byte_align_def,byte_aligned_def,
         mem_stores_def,mem_stores_def] >>
    gvs[align_add_aligned_gen] >>
    gvs[align_def,AllCaseEqs(),mem_load_def,APPLY_UPDATE_THM] >>
    gvs[align_add_aligned_gen] >>
    gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>



(*
 rveq >>
 fs [byte_align_aligned] >>
 simp [APPLY_UPDATE_THM]

 dep_rewrite.DEP_ONCE_REWRITE_TAC [byte_align_aligned]

 fs [byte_align_def,APPLY_UPDATE_THM,align_add_aligned_gen,align_def] >>
 fs [set_byte_def,word_slice_alt_def,byte_index_def] >>
*)

(* Doesn't quite work - write_bytearray still returns, but doesn't modify memory if a store fails.
   In any case, it doesn't seem like we need this theorem.
Theorem write_bytearray_SOME_read_no_labels:
  ∀mem memaddrs be addr bytesls mem' n.
    SOME mem' = write_bytearray addr bytesls mem memaddrs be ∧
    byte_aligned addr ∧ LENGTH bytesls = n
    ⇒ (0 <= m ∧ m < n ⇒ ∃x. mem' (addr + n2w m) = Word x)
Proof
QED
*)


                          qpat_x_assum ‘_ = Word v’ mp_tac >>
                          qpat_x_assum ‘_ = SOME m1’ mp_tac >>
                          rw[mem_store_def] >>
                          rw[APPLY_UPDATE_THM] >>
                          spose_not_then strip_assume_tac >>
                          gvs[] >>
                          pop_assum mp_tac >>
                          simp[] >>
                          imp_res_tac aligned_w2n >>
                          gvs[] >>
                          dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned] >>
                          conj_tac >- simp[] >>
                          simp[Once two_mask_get_byte] >>
                          simp[Once set_byte_MOD_aligned] >>
                          simp[get_byte_set_byte] >>
                          rw [Once unit_mask_get_byte, Once set_byte_MOD_aligned,get_byte_set_byte] >>
                          blastLib.FULL_BBLAST_TAC >>
                          strip_tac >>
                          qhdtm_x_assum ‘aligned’ mp_tac >>
                          simp[aligned_def,align_def] >>
                          blastLib.FULL_BBLAST_TAC)) >>


    simp [set_byte_def] >>


    rw [APPLY_UPDATE_THM] (* Makes progress, but maybe not where I want it to. *)

    >- (

    )
    >- (
    )





  )
  >- fs [shape_of_def]

  (* for Seq (spawns a λ.)
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘_ (evaluate _)’ >>

  *)
  (* simp for ‘evaluate (Store ..)’
     simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def]
   *)

  (* for ‘evaluate (StoreByte ..)’
     simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>

     (* What's below isn't actually necessary when the right assumption is already given, only for
        the assumptionless case. *)

     (* Need new name here *)
     qmatch_goalsub_abbrev_tac ‘m1 = mem_store_byte _ _ _ _ _’ >>
     Cases_on ‘m1’ >> simp []
     >- (unabbrev_all_tac >> simp []) >>
     simp [Abbr ‘_’] >>
     (* Need innermost abbreviated term *)

   *)


QED

(* Work out the intended composition first. Using the thrm. about the init_drv_state. *)
Theorem drv_putChar_evaluate_all_univ:
    ∀s s' res mem memaddrs statt hs tls hm tlm rxt base_addr c ck.
      eventually_state_txbuf_empty s ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = finite_stat_IO_map bytels
             ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof
  rewrite_tac [gen_to_init_drv_state] >>
  mp_tac gen_drv_putChar_evaluate_all_univ >> rw[] >>
  res_tac >>
  pop_assum $ qspec_then ‘c’ assume_tac >> fs []
QED

Theorem init_state_putChar_assm:
  ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c.
    mess_of_assums ⇒
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') => T
      | _ => F
Proof
  rewrite_tac [gen_to_init_drv_state] >>
  mp_tac gen_state_putChar_assm >> rw[] >>
  pop_assum $ qspecl_then [‘s’,‘mem'’,‘memaddrs’,
                           ‘statt’,‘hs’,‘tls’,‘hm’,‘tlm’,‘rxt’,‘base_addr’,‘c’] assume_tac >>
  fs[] >> qexists_tac ‘ck’ >> rw [] >>
  gvs [gen_to_init_drv_state]
QED

(* Desired top-level proof goal. *)
(* Provable given the 2*2 theorems above. *)
Theorem init_state_putChar_comp:
  ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c.
    mess_of_assums s mem memaddrs ⇒
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = finite_stat_IO_map bytels
                                   ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => F
Proof
  rpt strip_tac >>
  mp_tac drv_putChar_evaluate_all_univ >>
  rw [] >>
  mp_tac init_state_putChar_assm >>
  rw [] >>
  last_x_assum $ qspecl_then
               [‘mem'’,‘memaddrs’, ‘hs’,‘tls’,‘hm’,‘tlm’,‘base_addr’,‘c’] assume_tac >>
  last_x_assum $ qspecl_then [‘s’,‘mem'’,‘memaddrs’,‘statt’,‘hs’,‘tls’,‘hm’,‘tlm’,
                              ‘rxt’,‘base_addr’,‘c’] assume_tac >>
  gvs [] >>
  qexists_tac ‘ck’ >>
  first_x_assum $ qspec_then ‘ck’ assume_tac >>
  res_tac >>
  rw [] >>
  every_case_tac >> gvs [] >>
  metis_tac []
QED


(* Abandon this proof and its generalisation.
Theorem drv_putChar_evaluate_alt_proof_attempt:
    ∀s s' res mem memaddrs statt hs tls hm tlm rxt base_addr c.
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = finite_stat_IO_map bytels
             ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof
  rewrite_tac [gen_to_init_drv_state] >>
  mp_tac gen_state_drv_putChar_evaluate >> rw [] >>
  pop_assum $ qspecl_then [‘s’,‘FEMPTY’,‘FEMPTY’,‘mem'’,‘memaddrs’,
                           ‘statt’,‘hs’,‘tls’,‘hm’,‘tlm’,‘rxt’,‘[]’,‘base_addr’,‘c’] assume_tac >>
  rw [] >> metis_tac []
QED

(* Duplicate of below : for testing purposes. *)
Theorem gen_state_drv_putChar_evaluate:
    ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c.
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = gen_drv_state_uffi loc es ck T mem memaddrs statt rxt ts base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = ts ++ finite_stat_IO_map bytels
             ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof
  cheat
QED
*)

(* See if this more general statement works with the induction beginning immediately,
   which didn't quite work below. *)
Theorem gen_state_drv_putChar_evaluate:
    ∀s s' res loc es mem memaddrs statt hs tls hm tlm rxt ts base_addr c.
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = gen_drv_state_uffi loc es ck T mem memaddrs statt rxt ts base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = ts ++ finite_stat_IO_map bytels
             ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof
  rewrite_tac [eventually_state_txbuf_empty_def] >>
  Ho_Rewrite.PURE_REWRITE_TAC [RIGHT_EXISTS_IMP_THM,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ntac 2 strip_tac >>
  qmatch_asmsub_abbrev_tac ‘eventually _ ll’ >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qid_spec_tac ‘s’ >>
  Ho_Rewrite.PURE_REWRITE_TAC[AND_IMP_INTRO,PULL_FORALL] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘ll’ >>
  ho_match_mp_tac eventually_ind >>
  rw []
  >- (fs [ll_txbuf_empty_def] >>
      assume_tac gen_state_ll_txbuf_empty_putchar_evaluate >>
      gvs [state_txbuf_empty_def] >>
      pop_assum $ qspecl_then [‘s’,‘loc’,‘es’,‘mem'’,‘memaddrs’,‘hs’,‘tls’, ‘hm’, ‘tlm’,
                               ‘ts’,‘base_addr’,‘c’] assume_tac >>
      res_tac >>
      qexists_tac ‘ck’ >> rw []) >>
  Q.REFINE_EXISTS_TAC ‘ck+3’ >>
  simp [Once evaluate_def,eval_def,serialProg_def,gen_drv_state_uffi_def,uart_drv_putcharFun_def,
        uart_drv_getcharFun_def,uart_altffi_state_def,init_uart_ffi_def,uart_ffi_oracle_alt_def,
        AllCaseEqs()] >>
  simp [FLOOKUP_DEF, dec_clock_def] >>
  IF_CASES_TAC >> simp []
  >- (
    simp [OPT_MMAP_def, eval_def,lookup_code_def,flookup_fupdate_list, shape_of_def, size_of_shape_def] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
    simp [Once evaluate_def,eval_def] >>
    ntac 4 $ simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
    qmatch_goalsub_abbrev_tac ‘a2 (a3 (a4 (a5 (a6 (evaluate _)))))’ >>
    simp [Once evaluate_def,eval_def] >>
    qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
    simp [dec_clock_def,Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
    simp [Once evaluate_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘ad1 = read_bytearray _ 8 _’ >>
    Cases_on ‘ad1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    qpat_abbrev_tac ‘ad2 = read_bytearray _ 4 _’ >>
    Cases_on ‘ad2’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [ffiTheory.call_FFI_def,uart_ffi_oracle_alt_def,uart_genffi_state_def] >>
    fs [] >>
    imp_res_tac read_bytearray_LENGTH >>
    simp [init_uart_ffi_def] >>
    simp [Abbr ‘a9’] >>
    simp[Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,flatten_def] >>
    qpat_abbrev_tac ‘mst1 = mem_stores _ _ _ _’ >>
    Cases_on ‘mst1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb1 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb2 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb2’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb3 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb3’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb4 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb4’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    simp [Abbr ‘a8’] >>

    (* ___ *)
    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
          wordLangTheory.word_sh_def] >>
    qpat_abbrev_tac ‘ml1 = mem_load _ _ _ _’ >>
    Cases_on ‘ml1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    IF_CASES_TAC >> simp []
    >- (
      simp [Once evaluate_def, asmTheory.word_cmp_def] >>
      CASE_TAC >> simp []
      >- (
        CASE_TAC >> simp []
        >- (
          IF_CASES_TAC >> simp []
          >- (
            simp [Once evaluate_def] >>
            simp [Abbr ‘a7’] >>
            qmatch_goalsub_abbrev_tac ‘goal’ >>
            last_x_assum mp_tac >>
            simp [Once evaluate_def,eval_def,serialProg_def,gen_drv_state_uffi_def,uart_drv_putcharFun_def,
                  uart_drv_getcharFun_def,uart_genffi_state_def,init_uart_ffi_def,uart_ffi_oracle_alt_def] >>
            simp [FLOOKUP_DEF, dec_clock_def] >>
            simp[OPT_MMAP_def, eval_def,lookup_code_def,flookup_fupdate_list] >>
            simp[shape_of_def] >>
            simp[empty_locals_def] >>
            simp [Once evaluate_def] >>
            simp [Once evaluate_def,eval_def] >>
            CONV_TAC $ PAT_CONV “λp. p ⇒ goal” $ RESORT_FORALL_CONV List.rev >>
            disch_then (qspec_then ‘c’ mp_tac) >>
            simp [] >> (* a2 is finally back :')) *)

            simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
            disch_then (qspec_then ‘base_addr’ mp_tac) >>
            simp [] >>

            (* It's easier now that we have the abbrevs in place. *)
            ntac 2 $ simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
            simp [Once evaluate_def] >>
            rw [Abbr ‘goal’] >>
            pop_assum $ qspec_then ‘ts ++ [IO_event "read_reg_UTRSTAT" x
                   (ZIP (x', [hs.byte1; hs.byte2; hs.byte3; hs.byte4]))]’ assume_tac >>
            fs $ map SYM [uart_drv_putcharFun_def, uart_drv_getcharFun_def] >> (* Reduce eyesore. *)
            pop_assum mp_tac >>
            CONV_TAC $ PAT_CONV “λp. p ⇒ goal” $ RESORT_FORALL_CONV List.rev >>
            rw [] >>

            qmatch_goalsub_abbrev_tac ‘(_:64 panLang$prog, iterst)’ >>



            (* Probably don't do this. *)
            pop_assum (qspec_then ‘<|locals :=
                                       (FEMPTY |++ [(«c» ,ValWord c)]) |+
                                       («a1» ,ValWord base_addr) |+
                                       («a2» ,ValWord (base_addr + 8w)) |+
                                       («l1» ,ValWord 8w) |+
                                       («l2» ,ValWord 4w);
                                     code :=
                                       FEMPTY |++
                                       [uart_drv_putcharFun;
                                        uart_drv_getcharFun]; eshapes := es;
                                     memory := x'⁶'; memaddrs := memaddrs;
                                     clock := ck + 1; be := T;
                                     ffi :=
                                       <|oracle := uart_ffi_oracle_alt;
                                         ffi_state :=
                                           <|utrstat := tls;
                                             rxbuf := hm:::tlm|>;
                                         io_events :=
                                           ts ++
                                           [IO_event "read_reg_UTRSTAT" x
                                              (ZIP
                                                 (x',
                                                  [hs.byte1; hs.byte2;
                                                   hs.byte3; hs.byte4]))]|>;
                                     base_addr := base_addr|>’
                                     assume_tac) >>

            (* Want to reverse quantifier order in I.H. then abbrev evaluate state in goal,
               then instantiate the I.H. with this abbreviation. *)

            pop_assum (qspecl_then [‘(FEMPTY |++ [(«c» ,ValWord c)]) |+ («a1» ,ValWord base_addr) |+
                                     («a2» ,ValWord (base_addr + 8w)) |+ («l1» ,ValWord 8w) |+ («l2» ,ValWord 4w)’,
                                    ‘es’, ‘x'⁶'’, ‘memaddrs’, ‘(HD $ THE $ LTAKE 1 tls) ::: (THE $ LDROP 2 tls)’,
                                    ‘HD $ THE $ LTAKE 1 tls’, ‘THE $ LDROP 2 tls’,‘hm’,‘tlm’,‘rxt’] assume_tac)


‘rxt’,‘tlm’,‘hm’,‘THE $ LDROP 2 tls’,‘THE $ LTAKE 1 tls’,
                                    ‘statt’,‘memaddrs’,‘mem'’,‘es’,‘loc’] assume_tac) >>
QED

Theorem drv_putChar_evaluate:
    ∀s s' res mem memaddrs statt hs tls hm tlm rxt base_addr c.
    ∃ck.
      eventually_state_txbuf_empty s ∧ s = init_drv_state_uffi ck T mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧ byte_aligned base_addr
      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const c], s)
      of
        (SOME (Return res), s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events = finite_stat_IO_map bytels
             ++ [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof (* As opposed to re-writing the goal to be something which immediately matches the form
         of the induction rule .. PURE_REWRITE_TAC w/ PULL__ moves quantifiers in/out-wards with GSYM [SYM
         which works with equalities under quantifiers] *)
  rewrite_tac [eventually_state_txbuf_empty_def] >>
  Ho_Rewrite.PURE_REWRITE_TAC [RIGHT_EXISTS_IMP_THM,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ntac 2 strip_tac >>
  qmatch_asmsub_abbrev_tac ‘eventually _ ll’ >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  Ho_Rewrite.PURE_REWRITE_TAC[AND_IMP_INTRO,PULL_FORALL] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘ll’ >>
  ho_match_mp_tac eventually_ind >>
  rw []
  >- (fs [ll_txbuf_empty_def] >>
      assume_tac ll_txbuf_empty_putchar_evaluate >>
      gvs [state_txbuf_empty_def] >>
      pop_assum $ qspecl_then [‘s’,‘mem'’,‘memaddrs’,‘hs’,‘tls’, ‘hm’, ‘tlm’,‘base_addr’,‘c’] assume_tac >>
      res_tac >>
      qexists_tac ‘ck’ >> rw []) >>
  Q.REFINE_EXISTS_TAC ‘ck+3’ >>
  simp [Once evaluate_def,eval_def,serialProg_def,init_drv_state_uffi_def,uart_drv_putcharFun_def,
        uart_drv_getcharFun_def,uart_altffi_state_def,init_uart_ffi_def,uart_ffi_oracle_alt_def,AllCaseEqs()] >>
  simp [FLOOKUP_DEF, dec_clock_def] >>
  IF_CASES_TAC
  >- (
    simp [OPT_MMAP_def, eval_def,lookup_code_def,flookup_fupdate_list, shape_of_def, size_of_shape_def] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
    simp [Once evaluate_def,eval_def] >>
    ntac 4 $ simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
    qmatch_goalsub_abbrev_tac ‘a2 (a3 (a4 (a5 (a6 (evaluate _)))))’ >>
    simp [Once evaluate_def,eval_def] >>
    qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
    simp [dec_clock_def,Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
    simp [Once evaluate_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘ad1 = read_bytearray _ 8 _’ >>
    Cases_on ‘ad1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    qpat_abbrev_tac ‘ad2 = read_bytearray _ 4 _’ >>
    Cases_on ‘ad2’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [ffiTheory.call_FFI_def,uart_ffi_oracle_alt_def] >>
    fs [] >>
    imp_res_tac read_bytearray_LENGTH >>
    simp [Abbr ‘a9’] >>
    simp[Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,flatten_def] >>
    qpat_abbrev_tac ‘mst1 = mem_stores _ _ _ _’ >>
    Cases_on ‘mst1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb1 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb2 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb2’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb3 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb3’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
    qpat_abbrev_tac ‘mb4 = mem_store_byte _ _ _ _ _’ >>
    Cases_on ‘mb4’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    simp [Abbr ‘a9’] >>
    simp [Once evaluate_def] >>
    simp [Abbr ‘a8’] >>

    simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
          wordLangTheory.word_sh_def] >>
    qpat_abbrev_tac ‘ml1 = mem_load _ _ _ _’ >>
    Cases_on ‘ml1’ >> simp []
    >- (unabbrev_all_tac >> simp []) >>
    IF_CASES_TAC >> simp []
    >- (
      simp [Once evaluate_def, asmTheory.word_cmp_def] >>
      CASE_TAC >> simp []
      >- (
        CASE_TAC >> simp []
        >- (
          IF_CASES_TAC >> simp []
          >- (
            simp [Once evaluate_def] >>
            simp [Abbr ‘a7’] >>

            qmatch_goalsub_abbrev_tac ‘goal’ >>
            last_x_assum mp_tac >>

            simp [Once evaluate_def,eval_def,serialProg_def,init_drv_state_uffi_def,uart_drv_putcharFun_def,
                  uart_drv_getcharFun_def,uart_altffi_state_def,init_uart_ffi_def,uart_ffi_oracle_alt_def] >>
            simp [FLOOKUP_DEF, dec_clock_def] >>
            simp[OPT_MMAP_def, eval_def,lookup_code_def,flookup_fupdate_list] >>
            simp[shape_of_def] >>
            simp[empty_locals_def] >>
            simp [Once evaluate_def] >>
            simp [Once evaluate_def,eval_def] >>
            CONV_TAC $ PAT_CONV “λp. p ⇒ goal” $ RESORT_FORALL_CONV List.rev >>
            disch_then (qspec_then ‘c’ mp_tac) >>
            simp [] >> (* a2 is finally back :')) *)

            simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
            disch_then (qspec_then ‘base_addr’ mp_tac) >>
            simp [] >>

            ntac 2 $ simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
            simp [Once evaluate_def] >>
            (* This isn't good enough because we need to be able to substitute in the new IO_event trace following
               the first iteration of the loop. The induction from earlier produced an I.H. re init_drv_state. *)
  (* for Seq (spawns a λ.)
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘_ (evaluate _)’ >>

  *)
  (* simp for ‘evaluate (Store ..)’
     simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def]
   *)

  (* for ‘evaluate (StoreByte ..)’
     simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>


     (* Need new name here *)
     qmatch_goalsub_abbrev_tac ‘m1 = mem_store_byte _ _ _ _ _’ >>
     Cases_on ‘m1’ >> simp []
     >- (unabbrev_all_tac >> simp []) >>
     simp [Abbr ‘_’] >>
     (* Need innermost abbreviated term *)

   *)

  (* 24 Aug ^ FIX THIS! *)

  rpt strip_tac >>
  simp [Once evaluate_def,eval_def,serialProg_def,init_drv_state_uffi_def,uart_drv_putcharFun_def,
        uart_drv_getcharFun_def,uart_altffi_state_def,init_uart_ffi_def,uart_ffi_oracle_alt_def,
        AllCaseEqs()] >>
  simp [FLOOKUP_DEF, dec_clock_def] >>

  IF_CASES_TAC
  >- (
    simp [OPT_MMAP_def, eval_def,lookup_code_def,flookup_fupdate_list, shape_of_def, size_of_shape_def] >>
    simp [Once evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
    simp [Once evaluate_def,eval_def] >>
    ntac 4 $ simp [Once evaluate_def,eval_def,res_var_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
    qmatch_goalsub_abbrev_tac ‘a2 (a3 (a4 (a5 (a6 (evaluate _)))))’ >>


  (* Fit this now with new pre-induct state. *)
  rewrite_tac [eventually_state_txbuf_empty_def] >>
  Ho_Rewrite.PURE_REWRITE_TAC [RIGHT_EXISTS_IMP_THM,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ntac 2 strip_tac >>
  qmatch_asmsub_abbrev_tac ‘eventually _ ll’ >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  Ho_Rewrite.PURE_REWRITE_TAC[AND_IMP_INTRO,PULL_FORALL] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘ll’ >>
  ho_match_mp_tac eventually_ind >>



QED

(* Generalised base case. *)
Theorem gen_state_ll_txbuf_empty_putchar_evaluate:
  ∀s s' res loc es mem memaddrs hs tls hm tlm ts base_addr c.
    state_txbuf_empty s ⇒
    ∃ck.
      s = gen_drv_state_uffi loc es ck T mem memaddrs (hs:::tls) (hm:::tlm) ts base_addr
      ∧ byte_aligned base_addr ⇒
      case
      evaluate (TailCall (Label «uart_drv_putchar») [Const c], s)
      of
        (SOME (Return res),s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events =
             ts ++ finite_stat_IO_map bytels ++
             [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof
  rw [gen_drv_state_uffi_def,Once evaluate_def,serialProg_def,
      uart_drv_getcharFun_def,uart_drv_putcharFun_def,state_txbuf_empty_def,utrstat_txbuf_empty_def,
      uart_genffi_state_def,init_uart_ffi_def] >>
  qexists_tac ‘3’ >>
  rw [AllCaseEqs()] >>
  rw [eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  rw [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def,dec_clock_def] >>
  rw [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  ntac 3 $ rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (a3 (a4 (a5 (a6 (evaluate _)))))’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def,dec_clock_def,FLOOKUP_UPDATE] >>
  qpat_abbrev_tac ‘ad1 = read_bytearray _ 8 _’ >>
  Cases_on ‘ad1’ >> simp []
  >- (unabbrev_all_tac >> simp []) >>
  qpat_abbrev_tac ‘ad2 = read_bytearray _ 4 _’ >>
  Cases_on ‘ad2’ >> simp []
  >- (unabbrev_all_tac >> simp []) >>
  simp [ffiTheory.call_FFI_def,uart_ffi_oracle_alt_def] >>
  FULL_CASE_TAC >> simp []
  >- (FULL_CASE_TAC >> simp []
      >- (simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          simp [Abbr ‘a8’] >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
                wordLangTheory.word_sh_def] >>
          FULL_CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          FULL_CASE_TAC >> simp []
          >- (FULL_CASE_TAC >> simp [] (* Now we want a contradiction here. *)
              >- (gvs [llist_rep_LCONS,THE_DEF,LHD,flatten_def,asmTheory.word_cmp_def,AllCaseEqs()] >>
                  Cases_on ‘h’
                  >- (Cases_on ‘w’ >> fs []
                      >- (spose_not_then kall_tac >>
                          rpt (qhdtm_x_assum ‘Abbrev’ kall_tac) >>
                          gvs [mem_store_byte_def,byte_align_def,byte_aligned_def,
                               mem_stores_def,mem_stores_def] >>
                          gvs[align_add_aligned_gen] >>
                          gvs[align_def,AllCaseEqs(),mem_load_def,APPLY_UPDATE_THM] >>
                          gvs[align_add_aligned_gen] >>
                          gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>
                          qpat_x_assum ‘_ = Word v’ mp_tac >>
                          qpat_x_assum ‘_ = SOME x''’ mp_tac >>
                          rw[mem_store_def] >>
                          rw[APPLY_UPDATE_THM] >>
                          spose_not_then strip_assume_tac >>
                          gvs[] >>
                          pop_assum mp_tac >>
                          simp[] >>
                          imp_res_tac aligned_w2n >>
                          gvs[] >>
                          dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned] >>
                          conj_tac >- simp[] >>
                          simp[Once two_mask_get_byte] >>
                          simp[Once set_byte_MOD_aligned] >>
                          simp[get_byte_set_byte] >>
                          rw [Once unit_mask_get_byte, Once set_byte_MOD_aligned,get_byte_set_byte] >>
                          blastLib.FULL_BBLAST_TAC >>
                          strip_tac >>
                          qhdtm_x_assum ‘aligned’ mp_tac >>
                          simp[aligned_def,align_def] >>
                          blastLib.FULL_BBLAST_TAC)) >>
                  spose_not_then kall_tac >>
                  rpt (qhdtm_x_assum ‘Abbrev’ kall_tac) >>
                  gvs [mem_store_byte_def,byte_align_def,byte_aligned_def,
                       mem_stores_def,mem_stores_def] >>
                  gvs[align_add_aligned_gen] >>
                  gvs[align_def,AllCaseEqs(),mem_load_def,APPLY_UPDATE_THM] >>
                  gvs[align_add_aligned_gen] >>
                  gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>
                  qpat_x_assum ‘_ = Word v’ mp_tac >>
                  qpat_x_assum ‘_ = SOME x''’ mp_tac >>
                  rw[mem_store_def] >>
                  rw[APPLY_UPDATE_THM] >>
                  spose_not_then strip_assume_tac >>
                  gvs[] >>
                  pop_assum mp_tac >>
                  simp[] >>
                  imp_res_tac aligned_w2n >>
                  gvs[] >>
                  dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned]) >>
              simp [Once evaluate_def] >>
              simp [Abbr ‘a7’] >>
              simp [Abbr ‘a6’] >>
              simp [Once evaluate_def,eval_def] >>
              qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
              simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
                    FLOOKUP_UPDATE,flookup_fupdate_list] >>
              qpat_abbrev_tac ‘mb1 = mem_store_byte _ _ _ _ (w2w _)’ >>
              Cases_on ‘mb1’ >> simp []
              >- (unabbrev_all_tac >> simp []) >>
              simp [Abbr ‘a6’] >>
              simp [Once evaluate_def, FLOOKUP_UPDATE] >>
              qpat_abbrev_tac ‘rba1 = read_bytearray _ 8 _’ >>
              Cases_on ‘rba1’ >> simp []
              >- (unabbrev_all_tac >> simp []) >>
              qpat_abbrev_tac ‘rba2 = read_bytearray _ 4 _’ >>
              Cases_on ‘rba2’ >> simp []
              >- (unabbrev_all_tac >> simp []) >>
              simp [ffiTheory.call_FFI_def, uart_ffi_oracle_alt_def] >>
              unabbrev_all_tac >> simp [] >>
              simp [evaluate_def,eval_def,
                    res_var_def,size_of_shape_def,shape_of_def,empty_locals_def] >>
              simp [finite_stat_IO_map_def] >>
              Ho_Rewrite.PURE_REWRITE_TAC[PULL_EXISTS] >>
              rw [] >>
              rename1 ‘ZIP _ = ZIP (p1,p2)’ >>
              qexists_tac ‘p1’ >>
              rw [] >>
              rename1 ‘ZIP (x1,hsls)’ >>
              qexists_tac ‘(x,x1,hsls)’ >>
              simp []) >>
          unabbrev_all_tac >> simp []) >>
      fs [] >>
      imp_res_tac read_bytearray_LENGTH) >>
  fs [] >>
  imp_res_tac read_bytearray_LENGTH >>
  gvs []
QED



(* Prove this one first - delays stating of messy assumptions.
   Then separately prove that with the required assumptions, we only satisfy the guard of the desired
   evaluation output. *)
(* Here the transmit buffer is immediately ready to be written to, so only one loop should occur. *)
(* Like the proof below, this probably depends on endianness.
   We probably want to rule out the trivial timeout cases, so make ck large enough. *)
Theorem ll_txbuf_empty_putchar_evaluate:
  ∀s s' res be mem memaddrs hs tls hm tlm base_addr c.
    state_txbuf_empty s ⇒
    ∃ck.
      s = init_drv_state_uffi ck T mem memaddrs (hs:::tls) (hm:::tlm) base_addr
      ∧ byte_aligned base_addr ⇒
      case
      evaluate (TailCall (Label «uart_drv_putchar») [Const c], s)
      of
        (SOME (Return res),s') =>
          (∃conf bytes1 bytels.
             s'.ffi.io_events =
             finite_stat_IO_map bytels ++
             [IO_event "write_reg_UTXH" conf (ZIP (bytes1,bytes1))])
      | _ => T
Proof
  rw [init_drv_state_uffi_def,Once evaluate_def,serialProg_def,
      uart_drv_getcharFun_def,uart_drv_putcharFun_def,state_txbuf_empty_def,utrstat_txbuf_empty_def,
      uart_altffi_state_def,init_uart_ffi_def] >>
  qexists_tac ‘3’ >>
  rw [AllCaseEqs()] >>
  rw [eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  rw [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def,dec_clock_def] >>
  rw [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  ntac 3 $ rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (a3 (a4 (a5 (a6 (evaluate _)))))’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def,dec_clock_def,FLOOKUP_UPDATE] >>
  qpat_abbrev_tac ‘ad1 = read_bytearray _ 8 _’ >>
  Cases_on ‘ad1’ >> simp []
  >- (unabbrev_all_tac >> simp []) >>
  qpat_abbrev_tac ‘ad2 = read_bytearray _ 4 _’ >>
  Cases_on ‘ad2’ >> simp []
  >- (unabbrev_all_tac >> simp []) >>
  simp [ffiTheory.call_FFI_def,uart_ffi_oracle_alt_def] >>
  FULL_CASE_TAC >> simp []
  >- (FULL_CASE_TAC >> simp []
      >- (simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,FLOOKUP_UPDATE] >>
          CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          simp [Abbr ‘a9’] >>
          simp [Once evaluate_def] >>
          simp [Abbr ‘a8’] >>
          simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
                wordLangTheory.word_sh_def] >>
          FULL_CASE_TAC >> simp []
          >- (unabbrev_all_tac >> simp []) >>
          FULL_CASE_TAC >> simp [] (*___*)
          >- (FULL_CASE_TAC >> simp [] (* Now we want a contradiction here. *)
              >- (gvs [llist_rep_LCONS,THE_DEF,LHD,flatten_def,asmTheory.word_cmp_def,AllCaseEqs()] >>
                  Cases_on ‘h’
                  >- (Cases_on ‘w’ >> fs []
                      >- (spose_not_then kall_tac >>
                          rpt (qhdtm_x_assum ‘Abbrev’ kall_tac) >>
                          gvs [mem_store_byte_def,byte_align_def,byte_aligned_def,
                               mem_stores_def,mem_stores_def] >>
                          gvs[align_add_aligned_gen] >>
                          gvs[align_def,AllCaseEqs(),mem_load_def,APPLY_UPDATE_THM] >>
                          gvs[align_add_aligned_gen] >>
                          gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>
                          qpat_x_assum ‘_ = Word v’ mp_tac >>
                          qpat_x_assum ‘_ = SOME x''’ mp_tac >>
                          rw[mem_store_def] >>
                          rw[APPLY_UPDATE_THM] >>
                          spose_not_then strip_assume_tac >>
                          gvs[] >>
                          pop_assum mp_tac >>
                          simp[] >>
                          imp_res_tac aligned_w2n >>
                          gvs[] >>
                          dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned] >>
                          conj_tac >- simp[] >>
                          simp[Once two_mask_get_byte] >>
                          simp[Once set_byte_MOD_aligned] >>
                          simp[get_byte_set_byte] >>
                          rw [Once unit_mask_get_byte, Once set_byte_MOD_aligned,get_byte_set_byte] >>
                          blastLib.FULL_BBLAST_TAC >>
                          strip_tac >>
                          qhdtm_x_assum ‘aligned’ mp_tac >>
                          simp[aligned_def,align_def] >>
                          blastLib.FULL_BBLAST_TAC)) >>
                  spose_not_then kall_tac >>
                  rpt (qhdtm_x_assum ‘Abbrev’ kall_tac) >>
                  gvs [mem_store_byte_def,byte_align_def,byte_aligned_def,
                       mem_stores_def,mem_stores_def] >>
                  gvs[align_add_aligned_gen] >>
                  gvs[align_def,AllCaseEqs(),mem_load_def,APPLY_UPDATE_THM] >>
                  gvs[align_add_aligned_gen] >>
                  gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>
                  qpat_x_assum ‘_ = Word v’ mp_tac >>
                  qpat_x_assum ‘_ = SOME x''’ mp_tac >>
                  rw[mem_store_def] >>
                  rw[APPLY_UPDATE_THM] >>
                  spose_not_then strip_assume_tac >>
                  gvs[] >>
                  pop_assum mp_tac >>
                  simp[] >>
                  imp_res_tac aligned_w2n >>
                  gvs[] >>
                  dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned]) >>
              simp [Once evaluate_def] >>
              simp [Abbr ‘a7’] >>
              simp [Abbr ‘a6’] >>
              simp [Once evaluate_def,eval_def] >>
              qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
              simp [Once evaluate_def,eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
                    FLOOKUP_UPDATE,flookup_fupdate_list] >>
              qpat_abbrev_tac ‘mb1 = mem_store_byte _ _ _ _ (w2w _)’ >>
              Cases_on ‘mb1’ >> simp []
              >- (unabbrev_all_tac >> simp []) >>
              simp [Abbr ‘a6’] >>
              simp [Once evaluate_def, FLOOKUP_UPDATE] >>
              qpat_abbrev_tac ‘rba1 = read_bytearray _ 8 _’ >>
              Cases_on ‘rba1’ >> simp []
              >- (unabbrev_all_tac >> simp []) >>
              qpat_abbrev_tac ‘rba2 = read_bytearray _ 4 _’ >>
              Cases_on ‘rba2’ >> simp []
              >- (unabbrev_all_tac >> simp []) >>
              simp [ffiTheory.call_FFI_def, uart_ffi_oracle_alt_def] >>
              unabbrev_all_tac >> simp [] >>
              simp [evaluate_def,eval_def,
                    res_var_def,size_of_shape_def,shape_of_def,empty_locals_def] >>
              simp [finite_stat_IO_map_def] >>
              Ho_Rewrite.PURE_REWRITE_TAC[PULL_EXISTS] >>
              rw [] >>
              rename1 ‘ZIP _ = ZIP (p1,p2)’ >>
              qexists_tac ‘p1’ >>
              rw [] >>
              rename1 ‘ZIP (x1,hsls)’ >>
              qexists_tac ‘(x,x1,hsls)’ >>
              simp []) >>
          unabbrev_all_tac >> simp []) >>
      fs [] >>
      imp_res_tac read_bytearray_LENGTH) >>
  fs [] >>
  imp_res_tac read_bytearray_LENGTH >>
  gvs []
QED
  (* Re-strucutre 27th Jul ^*)

(*
It wasn't enough to have LENGTH rds_bytes ≥ 4, we needed exactly LENGTH rds_bytes = 4 (at the point where FFI call result was being determined.) Why?

write_bytearray - unpacks into many mem_store_byte applications - would be nice to have something which
allows us to determine whether one write_bytearray call will produce the desired result without so many
simplification steps

having trouble connecting FFI output w/ registers in statt ll, write lemmas to do this? Is there a
simpler way?
*)

Theorem drv_getChar_evaluate:
  ∃ck.
    ∀s s' res be mem memaddrs statt hs tls hm tlm rxt base_addr
       rds_conf rds_bytes m1 m2 m3 m4 m5 m6
       rm1 rm2 rm3 rm4 rm5 rds_post_store rds1 v6 rd1 rd2 rd3 w.
      SOME rds_conf = read_bytearray base_addr 8 (mem_load_byte mem memaddrs be) ∧
      SOME rds_bytes = read_bytearray (base_addr + 8w) 4 (mem_load_byte mem memaddrs be) ∧
      LENGTH rds_bytes = 4 ∧
      LENGTH rds1 = 4 ∧
      state_rxbuf_ready s ∧ be = T ∧
      s = init_drv_state_uffi ck be mem memaddrs statt rxt base_addr ∧
      statt = hs:::tls ∧ rxt = hm:::tlm ∧
      SOME rds_post_store = read_bytearray base_addr 8 (mem_load_byte m5 memaddrs be) ∧
      SOME rds1 = read_bytearray (base_addr + 8w) 4 (mem_load_byte m5 memaddrs be) ∧
      SOME m6 = mem_load_byte (write_bytearray (base_addr + 8w)
                               [hm.byte1; hm.byte2; hm.byte3; hm.byte4] m5
                               memaddrs be) memaddrs be (base_addr + 8w) ∧
      SOME rm1 = mem_stores (base_addr + 16w) [Word 0w] memaddrs
                          (write_bytearray (base_addr + 8w)
                           [hs.byte1; hs.byte2; hs.byte3; hs.byte4] mem memaddrs be) ∧
      SOME rm2 = mem_store_byte rm1 memaddrs be (base_addr + 20w) (w2w (base_addr + 8w)) ∧
      SOME rm3 = mem_store_byte rm2 memaddrs be (base_addr + 21w) (w2w (base_addr + 9w)) ∧
      SOME rm4 = mem_store_byte rm3 memaddrs be (base_addr + 22w) (w2w (base_addr + 10w)) ∧
      SOME rm5 = mem_store_byte rm4 memaddrs be (base_addr + 23w) (w2w (base_addr + 11w)) ∧
      rm5 (base_addr + 16w) = Word v6 ∧
      SOME rd1 = read_bytearray base_addr 8 (mem_load_byte rm5 memaddrs be) ∧
      SOME rd2 = read_bytearray (base_addr + 8w) 4 (mem_load_byte rm5 memaddrs be) ∧
      SOME rd3 = read_bytearray base_addr 8 (mem_load_byte rm5 memaddrs be) ∧
      LENGTH rd2 = 4 ∧
      SOME w =
      mem_load_byte
      (write_bytearray (base_addr + 8w) [hm.byte1; hm.byte2; hm.byte3; hm.byte4] rm5 memaddrs be)
      memaddrs be (base_addr + 8w) ∧
      byte_aligned base_addr

      ⇒
      case
      evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],s)
      of
        (SOME (Return res), s') =>
          (∃conf1 conf2 bytes1a bytes1b bytes2a bytes2b.
             s'.ffi.io_events = [IO_event "read_reg_UTRSTAT" conf1 (ZIP (bytes1a,bytes1b))
                                 ;IO_event "read_reg_URXH" conf2 (ZIP (bytes2a,bytes2b))])
      | (SOME otherRes, s'') => T
      | _ => T
Proof (* mem' *)
  qexists_tac ‘30’ >>
  rpt strip_tac >>
  rw [uart_drv_getcharFun_def,
      init_drv_state_uffi_def, serialProg_def] >>
  fs [state_rxbuf_ready_def, utrstat_rxbuf_ready_def,THE_DEF, LHD] >>
  rw [Once evaluate_def, uart_drv_getcharFun_def,
      uart_altffi_state_def, serialProg_def] >>
  rw [eval_def, flookup_fupdate_list,OPT_MMAP_def,FUPDATE_LIST,lookup_code_def,
      FLOOKUP_DEF,dec_clock_def] >>
  rw [Once evaluate_def,eval_def] >>
  rw [Once evaluate_def,eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def] >>
  ntac 3 (rw [Once evaluate_def,eval_def]) >>
  qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (a6 (evaluate _))))))’ >>
  rw [Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def,eval_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM] >>
  qpat_abbrev_tac ‘ad1 = read_bytearray _ 8 _’ >>
  qpat_abbrev_tac ‘ad2 = read_bytearray _ 4 _’ >>
  Cases_on ‘ad1’ >- fs [] >>
  simp [] >>
  Cases_on ‘ad2’ >- fs [] >>
  simp [] >>
  rw [ffiTheory.call_FFI_def, init_uart_ffi_state_def, uart_ffi_oracle_alt_def, init_uart_ffi_def] >>
  fs [] >>
  simp [Abbr ‘a7’] >>
  rw [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def, eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def] >>
  simp[flatten_def,empty_locals_def] >>
  qpat_abbrev_tac ‘store1 = mem_stores _ _ _ _’ >>
  Cases_on ‘store1’ >> simp []
  >- (unabbrev_all_tac >> fs []) >>
  simp [Abbr ‘a7’] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def, eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def] >>
  rw [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] >>
  qpat_abbrev_tac ‘store2 = mem_store_byte _ _ _ _ _’ >>
  Cases_on ‘store2’ >> simp []
  >- (unabbrev_all_tac >> fs []) >>
  simp [Abbr ‘a7’] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def, eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def,
      FLOOKUP_DEF,OPTION_BIND_def,FAPPLY_FUPDATE_THM] >>
  qpat_abbrev_tac ‘store3 = mem_store_byte _ _ _ _ _’ >>
  Cases_on ‘store3’ >> simp []
  >- (unabbrev_all_tac >> fs []) >>
  simp [Abbr ‘a7’] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def, eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def,
      FLOOKUP_DEF,OPTION_BIND_def,FAPPLY_FUPDATE_THM] >>
  qpat_abbrev_tac ‘store4 = mem_store_byte _ _ _ _ _’ >>
  Cases_on ‘store4’ >> simp []
  >- (unabbrev_all_tac >> fs []) >>
  simp [Abbr ‘a7’] >>
  rw [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  rw [Once evaluate_def, eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def,
      FLOOKUP_DEF,OPTION_BIND_def,FAPPLY_FUPDATE_THM] >>
  qpat_abbrev_tac ‘store5 = mem_store_byte _ _ _ _ _’ >>
  Cases_on ‘store5’ >> simp []
  >- (unabbrev_all_tac >> fs []) >>
  simp [Abbr ‘a7’] >>
  simp [Once evaluate_def] >>
  simp [Abbr ‘a6’] >>
  rw [Once evaluate_def, eval_def,OPT_MMAP_def,OPTION_MAP_DEF,wordLangTheory.word_op_def,
      FLOOKUP_DEF,OPTION_BIND_def,FAPPLY_FUPDATE_THM] >>
  rw [mem_load_def,wordLangTheory.word_sh_def]
  >- (IF_CASES_TAC
      >- (simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
          simp [Once evaluate_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM] >>
          CASE_TAC >- fs [] >>
          CASE_TAC >- fs [] >>
          gvs [] >>
          simp [ffiTheory.call_FFI_def, init_uart_ffi_state_def,
                uart_ffi_oracle_alt_def, init_uart_ffi_def] >>
          simp [Abbr ‘a6’, Once evaluate_def, eval_def, FLOOKUP_DEF, FAPPLY_FUPDATE_THM] >>
          CASE_TAC >- fs [] >>
          simp [size_of_shape_def, shape_of_def, Abbr ‘a5’] >>
          unabbrev_all_tac >> simp [empty_locals_def] >>
          metis_tac []) >>
      simp [Once evaluate_def,eval_def,size_of_shape_def,shape_of_def] >>
      unabbrev_all_tac >> simp [empty_locals_def] >>
      fs [init_drv_state_uffi_def, uart_altffi_state_def, init_uart_ffi_def, llist_rep_LCONS] >>
      rename1 ‘1w && hs' = 0w’ >>
      gvs [mem_store_byte_def,byte_align_def,
           byte_aligned_def,
           mem_stores_def,mem_stores_def] >>
      gvs[align_add_aligned_gen] >>
      gvs[align_def,AllCaseEqs(),APPLY_UPDATE_THM] >>
      qpat_x_assum ‘_ = Word v’ mp_tac >>
      qpat_x_assum ‘_ = SOME rm1’ mp_tac >>
      rw[mem_store_def] >>
      rw[APPLY_UPDATE_THM] >>
      spose_not_then strip_assume_tac >>
      gvs[] >>
      pop_assum mp_tac >>
      simp[] >>
      imp_res_tac aligned_w2n >>
      gvs[] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned] >>
      conj_tac >- simp[] >>
      simp[Once unit_mask_get_byte] >>
      simp[Once set_byte_MOD_aligned] >>
      simp[get_byte_set_byte] >>
      blastLib.FULL_BBLAST_TAC >>
      strip_tac >>
      qhdtm_x_assum ‘aligned’ mp_tac >>
      simp[aligned_def,align_def] >>
      blastLib.FULL_BBLAST_TAC) >>
  unabbrev_all_tac >> simp []
QED

Theorem proof's_no_longer_broken:
  ∀bytels addr n mem memaddrs be.
    read_bytearray addr n (mem_load_byte mem memaddrs be) = SOME bytels ∧
    LENGTH bytels ≠ n ⇒ F
Proof
  rw [] >>
  imp_res_tac read_bytearray_LENGTH
QED



(* Without endianness assumption ‘be = T’, we end up with the following case splits & an unprovable
   subgoal in the ‘be = F’ case.

      Cases_on ‘be’
      >- (pop_assum mp_tac >>
          simp[] >>
          imp_res_tac aligned_w2n >>
          gvs[] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned] >>
          conj_tac >- simp[] >>
          simp[Once unit_mask_get_byte] >>
          simp[Once set_byte_MOD_aligned] >>
          simp[get_byte_set_byte] >>
          blastLib.FULL_BBLAST_TAC >>
          strip_tac >>
          qhdtm_x_assum ‘aligned’ mp_tac >>
          simp[aligned_def,align_def] >>
          blastLib.FULL_BBLAST_TAC)

      >- (pop_assum mp_tac >>
          simp[] >>
          imp_res_tac aligned_w2n >>
          gvs[] >>

          ntac 4
               (dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_add_aligned] >>
                conj_tac >- simp[] >>
                simp[Once unit_mask_get_byte_le] >>
                simp[Once set_byte_MOD_aligned] >>
                simp[get_byte_set_byte2]) >>
          simp[get_byte_def]
          blastLib.FULL_BBLAST_TAC >>
          strip_tac >>
          qhdtm_x_assum ‘aligned’ mp_tac >>
          simp[aligned_def,align_def] >>
          blastLib.FULL_BBLAST_TAC
          )
          (* And here we find that correctness of this driver is
            not independent of endianness ! *)

          dep_rewrite.DEP_ONCE_REWRITE_TAC[set_byte_change_a] >>
          simp[set_byte_add_aligned]

          simp[WORD_w2w_OVER_ADD] >>
          ‘w2w base_addr = 0w:word8’

         )

*)

(* Helpful (?) common Pancake props. *)
Theorem evaluate_memaddrs_invariant:
  ∀p t res st.
    evaluate (p,t) = (res,st) ⇒ st.memaddrs = t.memaddrs
Proof
  recInduct evaluate_ind >>
  rw[Once evaluate_def]
  >~ [‘While’]
  >- (qpat_x_assum ‘evaluate _ = _’ (strip_assume_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
      gvs[AllCaseEqs(),empty_locals_def,ELIM_UNCURRY,dec_clock_def] >>
      metis_tac[PAIR,FST,SND]) >>
  gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,dec_clock_def,set_var_def] >>
  metis_tac[PAIR,FST,SND]
QED

(*
simp [eval_def, wordLangTheory.word_op_def]
simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE]
simp [OPT_MMAP_def]
simp [wordLangTheory.word_op_def]
simp [eval_def, OPTION_BIND_def]
simp[eval_def, FLOOKUP_UPDATE] >>
simp [OPTION_MAP_DEF]
simp [fcpTheory.dimindex_def, wordLangTheory.word_sh_def]
  panSem$evaluate (ExtCall (strlit $ "write_reg_UTXH") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"),s) = (NONE,s') ∧
  s.ffi = uart_ffi_state ⇒
  ∃conf bytes. s'.ffi.io_events = [IO_event "write_reg_UTXH" conf (ZIP (bytes,bytes))] ∧
                s'.ffi.ffi_state = s.ffi.ffi_state

Assumptions: (from current UART perspective)

assumed start state:
  - transmit buffer empty and ready for writing
  - recieve buffer empty and not ready for reading

environment:
  - device will eventually recieve a message (and thus there will be a point in the future where
      recieve buffer will become ready for writing)
  - device will eventually transmit a message written to TX (a full transmit buffer will eventually empty)
   [currently we don't even assume that a transmit requires an observable amount of ‘steps’ to empty,
    so it is always legal to write a message to the transmit buffer.]
*)

(* Warm-up proofs on result of calling panSem$evaluate. *)
Theorem extCall_no_break:
  ∀p a1 l1 a2 l2 s s'.
    evaluate (ExtCall p a1 l1 a2 l2, s) = (res,s') ⇒ res ≠ SOME Break
Proof
  simp [evaluate_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem storeByte_no_break:
  ∀dst src s s'.
    evaluate (StoreByte dst src, s) = (res,s') ⇒ res ≠ SOME Break
Proof
  simp [evaluate_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem while_no_break:
  ∀e res s1 c s.
    evaluate (While e c, s) = (res,s1) ⇒ res ≠ SOME Break
Proof
  completeInduct_on ‘s.clock’ >>
  simp[Once evaluate_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  pairarg_tac >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum ‘evaluate _ = (SOME Break,_)’ mp_tac >> (* Move relevant assumption to antecendent of conclusion, *)
  simp[] >> (* so that the conclusion matches the structure of the inductive hypothesis. *)
  first_x_assum (match_mp_tac o MP_CANON) >> (* first_x_assum irule seems to work identically here. *)
  irule_at (Pos last) EQ_REFL >>
  imp_res_tac evaluate_clock >>
  gvs[dec_clock_def]
QED

Theorem uart_drv_putcharFun_no_break:
  ∀ck be mem memaddrs ffi base_addr c.
    case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const $ n2w c],
                  init_drv_state ck be mem memaddrs ffi base_addr)
    of
      (SOME Break, s') => F
    | _ => T
Proof (* Restart - with new while loop thrm. *)
  rpt strip_tac >>
  simp[init_drv_state_def,serialProg_def,
    uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,FLOOKUP_UPDATE,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  simp[Once evaluate_def, eval_def] >>
  simp[FLOOKUP_UPDATE, flookup_fupdate_list, OPT_MMAP_def] >>
  simp [eval_def, OPTION_BIND_def] >>
  simp[FLOOKUP_UPDATE, flookup_fupdate_list, OPT_MMAP_def, lookup_code_def] >>
  simp [size_of_shape_def, shape_of_def] >>
  IF_CASES_TAC
  >- simp [] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp [Once evaluate_def, eval_def, FLOOKUP_UPDATE, flookup_fupdate_list] >>
  simp [Once evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        FLOOKUP_UPDATE, flookup_fupdate_list] >>
  simp [Once evaluate_def, eval_def, FLOOKUP_UPDATE, flookup_fupdate_list] >>
  simp [Once evaluate_def, eval_def, FLOOKUP_UPDATE, flookup_fupdate_list] >>
  simp [Once evaluate_def, dec_clock_def, FLOOKUP_UPDATE, flookup_fupdate_list] >>
  qmatch_goalsub_abbrev_tac ‘a2 (a3 (a4 (a5 (_ (evaluate _)))))’ >>
  pairarg_tac >> simp [] >>
  IF_CASES_TAC
  >- (simp [Abbr ‘a5’] >>
      pairarg_tac >> simp [] >>
      unabbrev_all_tac >> simp [] >>
      IF_CASES_TAC
      >- simp [Once evaluate_def, eval_def, size_of_shape_def, shape_of_def] >>
      simp [] >> every_case_tac) >>
  every_case_tac
QED

(* Example proof about events trace. *)
Theorem lkjblk:
  panSem$evaluate (ExtCall (strlit $ "write_reg_UTXH") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"),s) = (NONE,s') ∧
  s.ffi = init_uart_ffi_state rlls slls ⇒
  ∃conf bytes. s'.ffi.io_events = [IO_event "write_reg_UTXH" conf (ZIP (bytes,bytes))] ∧
                s'.ffi.ffi_state = s.ffi.ffi_state
Proof
  rw[evaluate_def] >>
  gvs[AllCaseEqs()] >>
  gvs[ffiTheory.call_FFI_def,AllCaseEqs()] >>
  gvs[uart_ffi_oracle_def,init_uart_ffi_state_def] >>
  metis_tac[]
QED

(*
  (* manual instantiation *)
  qexists_tac ‘bytes2’ >> simp[]

  (* manual instantiation *)
  qexists_tac ‘bytes2’ >> MATCH_ACCEPT_TAC EQ_REFL

  (* automation *)
  metis_tac[]

  (* pattern-based rule application *)
  irule_at (Pos hd) EQ_REFL
*)

(* Lazy list examples. *)
Theorem LFINITE_eventually_LNIL:
  LFINITE ll ⇒
  eventually ($= [||]) ll
Proof
  qspec_then ‘ll’ strip_assume_tac fromList_fromSeq >>
  rw[] >>
  Induct_on ‘l’ >>
  rw[]
QED

Theorem LFINITE_eventually_LNIL2:
  ll = LUNFOLD (λn. SOME(SUC n, n)) 0 ⇒
  eventually ($= (SOME 5) o LHD) ll
Proof
  rpt (rw[Once LUNFOLD])
QED

(* More evaluate-related theorems. *)
(* Aug 8: some of these may require slight tweaking after several fixes to the code. *)
Theorem uart_drv_getcharFun_no_break:
  ∀ck be mem memaddrs ffi base_addr res s.
    case
      evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
                  init_drv_state ck be mem memaddrs ffi base_addr)
    of
      (SOME Break, s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp [Once evaluate_def,init_drv_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp [eval_def, flookup_fupdate_list, FLOOKUP_UPDATE, OPT_MMAP_def, lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp [eval_def, dec_clock_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp[eval_def, FLOOKUP_UPDATE] >>
  simp [Once evaluate_def] >>
  simp[eval_def, FLOOKUP_UPDATE] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (a5 (a6 (evaluate _)))’ >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’
  >- (simp [] >> unabbrev_all_tac >> simp []) >>
  simp [] >>
  Cases_on ‘read_bytearray (base_addr + 64w) 32 (mem_load_byte mem' memaddrs be)’
  >- (simp [] >> unabbrev_all_tac >> simp []) >>
  simp [] >>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’
  >- (simp [] >> unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp[Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
     simp[Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
     Cases_on ‘mem_stores (base_addr + 128w) (flatten (ValWord 0w)) memaddrs
                 (write_bytearray (base_addr + 64w) l mem' memaddrs be)’
     >- (simp [] >> unabbrev_all_tac >> simp []) >>
     simp [] >> unabbrev_all_tac >> simp[] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'' memaddrs be (base_addr + 160w) (w2w (base_addr + 64w))’
     >- (simp [] >> unabbrev_all_tac >> simp []) >>
     simp [] >> unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'³' memaddrs be (base_addr + 168w) (w2w (base_addr + 72w))’
     >- (simp [] >> unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'⁴' memaddrs be (base_addr + 176w) (w2w (base_addr + 80w))’
     >- (unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'⁵' memaddrs be (base_addr + 184w) (w2w (base_addr + 88w))’
     >- (unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_load One (base_addr + 128w) memaddrs x'⁶'’
     >- (unabbrev_all_tac >> simp []) >>
     simp [wordLangTheory.word_op_def, wordLangTheory.word_sh_def] >>
     IF_CASES_TAC
     >- (simp[] >>
         IF_CASES_TAC
         >- (simp [evaluate_def, FLOOKUP_UPDATE] >>
             Cases_on ‘read_bytearray base_addr 8 (mem_load_byte x'⁶' memaddrs be)’
             >- (unabbrev_all_tac >> simp []) >>
             unabbrev_all_tac >> simp [] >>
             Cases_on ‘read_bytearray (base_addr + 64w) 32 (mem_load_byte x'⁶' memaddrs be)’
             >- simp [] >> simp [] >>
             Cases_on ‘call_FFI f "read_reg_URXH" x'⁸' x'⁹'’
             >- (simp [] >>
                 simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
                 Cases_on ‘mem_load_byte (write_bytearray (base_addr + 64w) l' x'⁶' memaddrs be)
                             memaddrs be (base_addr + 64w)’
                 >- simp [] >>
                 simp [] >>
                 simp [size_of_shape_def, shape_of_def]) >>
             simp []) >>
         simp [Once evaluate_def] >>
         simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE,
               size_of_shape_def, shape_of_def] >>
         unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp []
QED

Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi base_addr res s.
   read_bytearray base_addr 8 (mem_load_byte mem memaddrs be) = SOME x ∧
   read_bytearray (base_addr + 64w) 32 (mem_load_byte mem memaddrs be) = SOME x' ∧
   (∀f l. call_FFI ffi "read_reg_UTRSTAT" x x' = FFI_return f l ⇒
     (mem_stores (base_addr + 128w) (flatten (ValWord 0w)) memaddrs
               (write_bytearray (base_addr + 64w) l mem memaddrs be) = SOME x'' ∧
     mem_store_byte x'' memaddrs be (base_addr + 160w)
          (w2w (base_addr + 64w)) = SOME x''' ∧
     mem_store_byte x''' memaddrs be (base_addr + 168w) (w2w (base_addr + 72w)) = SOME x'''' ∧
     mem_store_byte x'⁴' memaddrs be (base_addr + 176w) (w2w (base_addr + 80w)) = SOME x''''' ∧
     mem_store_byte x'⁵' memaddrs be (base_addr + 184w) (w2w (base_addr + 88w)) = SOME x'''''' ∧
     mem_load One (base_addr + 128w) memaddrs x'⁶' = SOME x'⁷' ∧ x'⁷' = ValWord v ∧
     read_bytearray base_addr 8 (mem_load_byte x'⁶' memaddrs be) = SOME y ∧
     read_bytearray (base_addr + 64w) 32 (mem_load_byte x'⁶' memaddrs be) = SOME y' ∧
     (∀ f' l'. call_FFI f "read_reg_URXH" y y' = FFI_return f' l'
                ⇒ (mem_load_byte (write_bytearray (base_addr + 64w) l' x'⁶' memaddrs be)
       memaddrs be (base_addr + 64w) = SOME y''))))

    ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               init_drv_state ck be mem memaddrs ffi base_addr) of
      (SOME Error,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,init_drv_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[Once evaluate_def] >>
  simp[Once eval_def] >> simp[dec_clock_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,FLOOKUP_UPDATE] >>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’
  >- (last_x_assum $ qspecl_then [`f`, `l`] assume_tac >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      simp [FLOOKUP_UPDATE] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def, FLOOKUP_UPDATE, OPTION_BIND_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def, FLOOKUP_UPDATE, OPTION_BIND_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def, FLOOKUP_UPDATE, OPTION_BIND_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (evaluate _))))’ >>
      simp [Once evaluate_def] >>
      simp [eval_def, OPT_MMAP_def] >>
      simp [wordLangTheory.word_op_def, OPTION_MAP_DEF] >>
      simp [fcpTheory.dimindex_def, wordLangTheory.word_sh_def] >>
      Cases_on ‘1w && v ≠ 0w’
      >- (simp [] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
          simp [Once evaluate_def] >>
          simp[eval_def, FLOOKUP_UPDATE] >>
          Cases_on ‘call_FFI f "read_reg_URXH" y y'’
          >- (unabbrev_all_tac >> simp [] >>
              qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (evaluate _))))’ >>
              simp [Once evaluate_def] >>
              simp[eval_def, FLOOKUP_UPDATE] >>
              simp [size_of_shape_def, shape_of_def] >>
              unabbrev_all_tac >> simp []) >>
              Cases_on ‘FFI_final f'’
              >- (simp [] >>
              unabbrev_all_tac >> simp [] >>
              qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (evaluate _))))’ >>
              simp [Once evaluate_def] >>
              simp[eval_def, FLOOKUP_UPDATE] >>
              simp [size_of_shape_def, shape_of_def] >>
              unabbrev_all_tac >> simp []) >>
         simp [] >> unabbrev_all_tac >> simp []) >>
      simp [Once evaluate_def] >>
      simp[eval_def, FLOOKUP_UPDATE] >>
      simp [size_of_shape_def, shape_of_def] >>
      unabbrev_all_tac >> simp []) >>
  simp[] >> unabbrev_all_tac >> simp []
QED

(*
(* Original statement - re-stated to make proofs easier. *)
Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi res s.
    (evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               init_drv_state ck be mem memaddrs ffi) = (res,s)) ∧
    preconditions (* TODO *) ⇒
    res ≠ SOME Error
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,init_drv_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  simp[Once eval_def]
  (* TODO *)
QED
*)

Theorem uart_drv_getcharFun_no_FinalFFI:
  ∀ck be mem memaddrs ffi base_addr.
    (∀x x'. case call_FFI ffi "read_reg_UTRSTAT" x x' of
                FFI_final _ => F
              | FFI_return f _ =>
                  (∀f' x x'. call_FFI f "read_reg_URXH" x x' ≠ FFI_final f')) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               init_drv_state ck be mem memaddrs ffi base_addr) of
      (SOME (FinalFFI _),s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,init_drv_state_def,serialProg_def,
       uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,
       lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  simp[Once eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,FLOOKUP_UPDATE] >>
  CASE_TAC
  >- (CASE_TAC >> unabbrev_all_tac >> fs[])
  >> CASE_TAC >-(unabbrev_all_tac >> fs[]) >>
  fs[] >> CASE_TAC
  >- (simp[]>>unabbrev_all_tac >> fs[]>>
      fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
         wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
         OPT_MMAP_def, eval_def, evaluate_def]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      qpat_abbrev_tac ‘case_term = mem_load One (_ + _) _ _’>>
      Cases_on ‘case_term’>>fs[]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      fs[evaluate_def,eval_def,FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]
      >-(CASE_TAC>>fs[shape_of_def, size_of_shape_def])>>
      rename1 ‘call_FFI _ _ x' x = FFI_return f l’>>
      first_assum(qspecl_then [‘x'’, ‘x’] assume_tac)>>
      FULL_CASE_TAC>>fs[]>>
      simp[Once evaluate_def]>>fs[eval_def, FLOOKUP_UPDATE]>>
      simp[shape_of_def, size_of_shape_def])>>
  unabbrev_all_tac >> gs[]>>
  rename1 ‘call_FFI _ _ x' x = FFI_final _’>>
  first_assum(qspecl_then [‘x'’, ‘x’] assume_tac)>> FULL_CASE_TAC>>gs[]
QED

Theorem uart_drv_getcharFun_no_None:
  ∀ck be mem memaddrs ffi base_addr res s.
    IS_SOME(read_bytearray base_addr 8 (mem_load_byte mem memaddrs be)) ∧
    IS_SOME(read_bytearray (base_addr + 64w) 32
                           (mem_load_byte mem memaddrs be)) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               init_drv_state ck be mem memaddrs ffi base_addr) of
      (NONE : 64 result option,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,init_drv_state_def,serialProg_def,
       uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,
       OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- fs[] >>
  simp[dec_clock_def] >>
  simp[evaluate_def, eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
       FLOOKUP_UPDATE] >>
  CASE_TAC >> fs[] >>
  CASE_TAC >> fs[] >>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  fs[OPTION_MAP_DEF, OPTION_BIND_def, wordLangTheory.word_sh_def]>>
  qpat_abbrev_tac ‘case_term = mem_load One (_ + _) _ _’>>
  Cases_on ‘case_term’ >>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[evaluate_def,eval_def,FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[shape_of_def, size_of_shape_def]>>
  fs[evaluate_def,eval_def,shape_of_def, size_of_shape_def]
QED

(*
Theorem unit_mask_get_byte:
  (1w && w:word64) = w2w(1w && get_byte 7w w T)
Proof
  EVAL_TAC >>
  blastLib.FULL_BBLAST_TAC
QED

Theorem unit_mask_get_byte_le:
  (1w && w:word64) = w2w(1w && get_byte 0w w F)
Proof
  EVAL_TAC >>
  blastLib.FULL_BBLAST_TAC
QED

Theorem get_byte_set_byte2:
  8 ≤ dimindex (:α) ∧ w2n a MOD 8 ≠ w2n a' MOD 8 ⇒
  get_byte (a:α word) (set_byte a' b w be) be = get_byte a w be
Proof
  cheat
QED

Theorem set_byte_add_aligned:
     w2n a MOD (dimindex (:α) DIV 8) = 0 ∧ 8 ≤ dimindex(:'a) ⇒
     set_byte ((a:'a word) + a') b w be = set_byte a' b w be
Proof
  strip_tac >> match_mp_tac set_byte_change_a >>
  simp[word_add_def] >>
  ‘∃k. dimword(:α) = (dimindex (:α) DIV 8)*k ∧ 0 < k’ by cheat >>
  ASM_SIMP_TAC std_ss [] >>
  dep_rewrite.DEP_REWRITE_TAC[MOD_MULT_MOD] >>
  simp[] >>
  conj_tac >- (qpat_x_assum ‘8 ≤ _’ mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC) >>
  qpat_x_assum ‘dimword (:α) = _’ kall_tac >>
  qpat_x_assum ‘_ = _’ mp_tac >> dep_rewrite.DEP_REWRITE_TAC[MOD_EQ_0_DIVISOR] >>
  rw[] >- (pop_assum mp_tac >> intLib.COOPER_TAC) >>
  ASM_SIMP_TAC std_ss [] >>
  dep_rewrite.DEP_REWRITE_TAC[MOD_TIMES] >>
  intLib.COOPER_TAC
QED

Theorem set_byte_MOD_aligned:
  set_byte (a) b w be = set_byte (n2w(w2n a MOD 8)) b w be
Proof
  cheat
QED

*)

Theorem make_this_simple:
  read_bytearray base_addr 8 (mem_load_byte mem' memaddrs T) = SOME rm1
  ∧ read_bytearray (base_addr + 8w) 4 (mem_load_byte mem' memaddrs T) =
    SOME rm2
  ∧ mem_stores (base_addr + 16w) [Word 0w] memaddrs (write_bytearray (base_addr + 8w)
                                                     [hs.byte1; hs.byte2; hs.byte3; hs.byte4] mem' memaddrs T) =
    SOME m1
  ∧ mem_store_byte m1 memaddrs T (base_addr + 20w) (w2w (base_addr + 8w)) =
    SOME m2
  ∧ mem_store_byte m2 memaddrs T (base_addr + 21w) (w2w (base_addr + 9w)) =
    SOME m3
  ∧ mem_store_byte m3 memaddrs T (base_addr + 22w)
                   (w2w (base_addr + 10w)) = SOME m4
  ∧  mem_store_byte m4 memaddrs T (base_addr + 23w) (w2w (base_addr + 11w)) = SOME m5
  ∧ base_addr + 16w ∈ memaddrs
  ∧ 2w && hs.byte4 ≠ 0w
  ∧ byte_aligned base_addr ⇒ goal
Proof
  rpt strip_tac >>
QED

val _ = export_theory();
