(*
  Tiana's Proofs
*)
open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory x64_configTheory compilationLib;

val _ = new_theory "serialPanDrv";

(*
Device register offsets from original driver:
https://github.com/seL4/seL4/blob/master/src/drivers/serial/exynos4210-uart.c

#define ULCON       0x0000 /* line control */
#define UCON        0x0004 /* control */
#define UFCON       0x0008 /* fifo control */
#define UMCON       0x000C /* modem control */
#define UTRSTAT     0x0010 /* TX/RX status */
#define UERSTAT     0x0014 /* RX error status */
#define UFSTAT      0x0018 /* FIFO status */
#define UMSTAT      0x001C /* modem status */
#define UTXH        0x0020 /* TX buffer */
#define URXH        0x0024 /* RX buffer */
#define UBRDIV      0x0028 /* baud rate divisor */
#define UFRACVAL    0x002C /* divisor fractional value */
#define UINTP       0x0030 /* interrupt pending */
#define UINTSP      0x0034 /* interrupt source pending */
#define UINTM       0x0038 /* interrupt mask */
*)

val RXBUF_READY_const= “(Shift Lsl (Const 1w) 0) :64 panLang$exp”;
val TXBUF_EMPTY_const= “(Shift Lsl (Const 1w) 1) :64 panLang$exp”;
val TX_EMPTY_const= “(Shift Lsl (Const 1w) 2) : 64 panLang$exp”;

val minus_one_const= “(panLang$Const $ n2w $ 2**64 - 1) :64 panLang$exp” |> EVAL |> concl |> rhs;

val uart_drv_putcharFun=
  “(strlit "uart_drv_putchar",
    [(strlit "c", One)],
    Seq
    (Dec (strlit "a1") BaseAddr (
      Dec (strlit "a2") (Op Add [BaseAddr; Const 8w]) (
        Dec (strlit "l1") (Const 8w) (
          Dec (strlit "l2") (Const 4w) (
            Seq
              (While (Const 1w) (
                Seq
                  (FOLDR Seq Skip [
                     ExtCall (strlit $ "read_reg_UTRSTAT") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2");
                     Store (Op Add [BaseAddr; Const 16w]) (Const 0w);
                     StoreByte (Op Add [BaseAddr; Const 20w]) (LoadByte $ Var $ strlit "a2");
                     StoreByte (Op Add [BaseAddr; Const 21w]) (LoadByte $ Op Add [Var $ strlit "a2"; Const 1w]);
                     StoreByte (Op Add [BaseAddr; Const 22w]) (LoadByte $ Op Add [Var $ strlit "a2"; Const 2w]);
                     StoreByte (Op Add [BaseAddr; Const 23w]) (LoadByte $ Op Add [Var $ strlit "a2"; Const 3w]);
                   ]
                  )
                  (If (Cmp Equal (Op And [Load One (Op Add [BaseAddr; Const 16w]); ^TXBUF_EMPTY_const]) (Const 0w)) Skip Break)
              ))
              (Seq
                (StoreByte BaseAddr (Var $ strlit "c"))
                (ExtCall (strlit "write_reg_UTXH") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"))
              )
    )))))
    (Return $ Const 0w) :64 panLang$prog
   )” |> EVAL |> concl |> rhs; (* Note: original function does not return a value. *)

Definition uart_drv_putcharFun_def:
  uart_drv_putcharFun = ^uart_drv_putcharFun
End

val uart_drv_getcharFun=
  “(strlit "uart_drv_getchar",
    [] :(mlstring # shape) list,
    Dec (strlit "a1") BaseAddr (
      Dec (strlit "a2") (Op Add [BaseAddr; Const 8w]) (
        Dec (strlit "l1") (Const 8w) (
          Dec (strlit "l2") (Const 4w) (
            Seq
              (FOLDR Seq Skip [
                 ExtCall (strlit $ "read_reg_UTRSTAT") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2");
                 Store (Op Add [BaseAddr; Const 16w]) (Const 0w);
                 StoreByte (Op Add [BaseAddr; Const 20w]) (LoadByte $ Var $ strlit "a2");
                 StoreByte (Op Add [BaseAddr; Const 21w]) (LoadByte $ Op Add [Var $ strlit "a2"; Const 1w]);
                 StoreByte (Op Add [BaseAddr; Const 22w]) (LoadByte $ Op Add [Var $ strlit "a2"; Const 2w]);
                 StoreByte (Op Add [BaseAddr; Const 23w]) (LoadByte $ Op Add [Var $ strlit "a2"; Const 3w]);
               ]
              )
              (If (Op And [Load One (Op Add [BaseAddr; Const 16w]); ^RXBUF_READY_const])
                (Seq
                  (ExtCall (strlit $ "read_reg_URXH") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"))
                  (Return (LoadByte (Var $ strlit "a2")))) (* Should this be a Load instead ? Modify if anything else goes wrong. *)
                (Return ^minus_one_const)
              )
    )))) :64 panLang$prog
   )” |> EVAL |> concl |> rhs;

Definition uart_drv_getcharFun_def:
  uart_drv_getcharFun = ^uart_drv_getcharFun
End

Definition serialProg_def:
  serialProg = [uart_drv_putcharFun; uart_drv_getcharFun]
End

(* Driver set-up seems to occur somewhere else. *)

val _ = export_theory();
