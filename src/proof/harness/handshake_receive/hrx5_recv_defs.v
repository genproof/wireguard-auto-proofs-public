(* law handshake_receive: the cut of receive.c's wg_receive_handshake_packet into segments and the states between
   them.

   body = peer = NULL; t'20 = skb->data; t'21 = type; if (t'21 == 3) COOKIE;
          LOAD1; LOAD2; VAL; DEC; SW; TAIL
   SW   = t'11 = skb->data; t'12 = type; switch (t'12) { case 1: C1  case 2: C2 }
   C1   = t'16 = skb->data; message = t'16;    if (packet_needs_cookie) NC1 else skip; IREST
   C2   = t'14 = skb->data; message__1 = t'14; if (packet_needs_cookie) NC2 else skip; RREST

   Segments (states below; R = the function's postcondition hrx5_rv_R):
     C    S0 (type 3)            COOKIE                          retonly R  (consume the cookie reply, return)
     LV   S0 (type not 3)        LOAD1; LOAD2; VAL; DEC          SV / R     (the load, validate, the verdict)
     N1   SN1 r                  NC1                             retonly R  (send the cookie reply, return)
     N2   SN2 r                  NC2                             retonly R
     I    SI r                   IREST                           switch_ret_assert (Qtail / R)
     RS   SR r                   RREST                           switch_ret_assert (Qtail / R)
     T    Qtail                  TAIL                            R
   r = validate's draw (the rotation).  The main proof (hrx5_body_recv.v) does the control flow and the reads of
   the type word. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Local Open Scope logic.

(* ------------------------------------------------------------------------------------------------ *)
(* the statements                                                                                    *)
(* ------------------------------------------------------------------------------------------------ *)

Definition hrx5_rv_body : statement :=
  Eval cbv beta iota delta [HRC.f_wg_receive_handshake_packet fn_body] in fn_body HRC.f_wg_receive_handshake_packet.

Definition hrx5_rv_COOKIE : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence (Ssequence _ (Ssequence _ (Sifthenelse _ s _))) _) => s | _ => Sskip end.
Definition hrx5_rv_LOAD1 : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end.
Definition hrx5_rv_LOAD2 : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _))) => s | _ => Sskip end.
Definition hrx5_rv_VAL : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _)))) => s | _ => Sskip end.
Definition hrx5_rv_DEC : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _))))) => s | _ => Sskip end.
Definition hrx5_rv_SW : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _)))))) => s
  | _ => Sskip end.
Definition hrx5_rv_TAIL : statement := Eval cbv beta iota delta [hrx5_rv_body] in
  match hrx5_rv_body with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ s)))))) => s
  | _ => Sskip end.
Definition hrx5_rv_C1 : statement := Eval cbv beta iota delta [hrx5_rv_SW] in
  match hrx5_rv_SW with
  | Ssequence _ (Ssequence _ (Sswitch _ (LScons _ s _))) => s | _ => Sskip end.
Definition hrx5_rv_C2 : statement := Eval cbv beta iota delta [hrx5_rv_SW] in
  match hrx5_rv_SW with
  | Ssequence _ (Ssequence _ (Sswitch _ (LScons _ _ (LScons _ s _)))) => s | _ => Sskip end.
Definition hrx5_rv_NC1 : statement := Eval cbv beta iota delta [hrx5_rv_C1] in
  match hrx5_rv_C1 with Ssequence _ (Ssequence (Sifthenelse _ s _) _) => s | _ => Sskip end.
Definition hrx5_rv_IREST : statement := Eval cbv beta iota delta [hrx5_rv_C1] in
  match hrx5_rv_C1 with Ssequence _ (Ssequence _ s) => s | _ => Sskip end.
Definition hrx5_rv_NC2 : statement := Eval cbv beta iota delta [hrx5_rv_C2] in
  match hrx5_rv_C2 with Ssequence _ (Ssequence (Sifthenelse _ s _) _) => s | _ => Sskip end.
Definition hrx5_rv_RREST : statement := Eval cbv beta iota delta [hrx5_rv_C2] in
  match hrx5_rv_C2 with Ssequence _ (Ssequence _ s) => s | _ => Sskip end.

(* LV's statement: the four consecutive statements, grouped *)
Definition hrx5_rv_LV : statement :=
  Ssequence hrx5_rv_LOAD1 (Ssequence hrx5_rv_LOAD2 (Ssequence hrx5_rv_VAL hrx5_rv_DEC)).

(* ------------------------------------------------------------------------------------------------ *)
(* the model's intermediate values                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)

(* the load (under_load, last_under_load after) *)
Definition hrx5_rv_ul (W: rxw) (q: int) : bool := fst (load_model q (rw_lul W) (s_boot (rw_S W))).
Definition hrx5_rv_lul (W: rxw) (q: int) : int64 := snd (load_model q (rw_lul W) (s_boot (rw_S W))).
(* validate's (verdict, checker after) with the draw r *)
Definition hrx5_rv_vm (W: rxw) (q: int) (s: skb) (msg: list byte) (r: list byte) : Z * checker :=
  validate_model (d_cc (rw_D W)) s msg (hrx5_rv_ul W q) (s_boot (rw_S W)) (s_rlallow (rw_S W)) r.
(* the world after the load and validate (= rx_packet's dropped world) *)
Definition hrx5_rv_W1 (W: rxw) (q: int) (s: skb) (msg: list byte) (r: list byte) : rxw :=
  mkRW (dev_set_cc (rw_D W) (snd (hrx5_rv_vm W q s msg r))) (rw_T W) (rw_PS W) (rw_KS W)
       (if validate_rotates (d_cc (rw_D W)) msg (hrx5_rv_ul W q) (s_boot (rw_S W)) then shim_draw (rw_S W) r
        else rw_S W)
       (rw_w W) (rw_kc W) (hrx5_rv_lul W q) (rw_rx W).
Definition hrx5_rv_cons (W: rxw) (q: int) (s: skb) (msg: list byte) (r: list byte) : bool :=
  rx_consumes (hrx5_rv_ul W q) (fst (hrx5_rv_vm W q s msg r)).
Definition hrx5_rv_nc (W: rxw) (q: int) (s: skb) (msg: list byte) (r: list byte) : bool :=
  rx_needs_cookie (hrx5_rv_ul W q) (fst (hrx5_rv_vm W q s msg r)).

(* the common tail on the world W2 with the authenticated peer a: update_rx_stats, the two timers, wg_peer_put *)
Definition hrx5_rv_tailw (W2: rxw) (a: val) (len: int) : rxw :=
  match sfind (rw_PS W2) a with
  | Some (_, P) =>
      let r := p_refs P in
      mkRW (rw_D W2) (rw_T W2) (supd (rw_PS W2) a (p_set_refs P (rc_sub1 r))) (rw_KS W2)
           (if Int.eq (rc_sub1 r) Int.zero then shim_release (rw_S W2) else rw_S W2) (rc_dec_warn r (rw_w W2))
           (rw_kc W2) (rw_lul W2) (rx_tail (rw_rx W2) a len)
  | None => W2
  end.
Definition hrx5_rv_tail_ok (W2: rxw) (a: val) : Prop :=
  a <> nullval /\ rx_peer (rw_rx W2) = a /\ exists sh P, sfind (rw_PS W2) a = Some (sh, P) /\ writable_share sh.

(* ------------------------------------------------------------------------------------------------ *)
(* the context, the hypotheses, the postcondition, the states                                        *)
(* ------------------------------------------------------------------------------------------------ *)

Definition hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) : tycontext :=
  func_tycontext HRC.f_wg_receive_handshake_packet hrx5_V
    (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) nil.

(* the precondition's pure part (and the primitives' properties) *)
Definition hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec (W: rxw) (shd: share) (wg head: val)
  (shs: share) (s: skb) (shm: share) (msg: list byte) : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec /\
  writable_share shd /\ readable_share shs /\ readable_share shm /\ hrx5_fwd msg = true /\ rx_msg_ok s msg /\
  rxw_ok wg head W.

(* the function's postcondition (as start_function states it) *)
Definition hrx5_rv_post x25519 aead_dec xaead_enc xaead_dec (CSw: compspecs) (gv: globals) (W: rxw) (q: int)
  (shd: share) (wg head: val) (shs: share) (sp: val) (s: skb) (shm: share) (msg: list byte) : environ -> mpred :=
  (EX d : rxdraw,
   PROP (rxdraw_ok (rw_T W) d) RETURN ( )
   SEP (rxw_rep CSw gv shd wg head (rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d); qlen_rep gv q;
        skb_rep shs sp s; bytes_at shm msg (sk_data s); wg_consts gv; mem_mgr gv))%argsassert.
Definition hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec (CSw: compspecs) (gv: globals) (W: rxw) (q: int)
  (shd: share) (wg head: val) (shs: share) (sp: val) (s: skb) (shm: share) (msg: list byte) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tvoid (hrx5_rv_post x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg))
    (stackframe_of HRC.f_wg_receive_handshake_packet).

(* only the return exit of R (segments that end in `return`) *)
Definition hrx5_rv_retonly (R: ret_assert) : ret_assert :=
  {| RA_normal := FF; RA_break := FF; RA_continue := FF; RA_return := RA_return R |}.

(* S0: after peer = NULL (and the first read of the type word) *)
Definition hrx5_rv_S0 (CSw: compspecs) (gv: globals) (W: rxw) (q: int) (shd: share) (wg head: val) (shs: share)
  (sp: val) (s: skb) (shm: share) (msg: list byte) : environ -> mpred :=
  PROP ()
  LOCAL (temp HRC._peer nullval; gvars gv; temp HRC._wg wg; temp HRC._skb sp)
  SEP (rxw_rep CSw gv shd wg head W; qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s);
       wg_consts gv; mem_mgr gv).

(* SV: after the verdict, the packet neither dropped nor answered by its return *)
Definition hrx5_rv_SV (CSw: compspecs) (gv: globals) (W: rxw) (q: int) (shd: share) (wg head: val) (shs: share)
  (sp: val) (s: skb) (shm: share) (msg: list byte) : environ -> mpred :=
  EX r: list byte,
  PROP (Zlength r = 32; (hrx5_rv_cons W q s msg r || hrx5_rv_nc W q s msg r)%bool = true)
  LOCAL (temp HRC._packet_needs_cookie (Val.of_bool (hrx5_rv_nc W q s msg r)); temp HRC._peer nullval; gvars gv;
         temp HRC._wg wg; temp HRC._skb sp)
  SEP (rxw_rep CSw gv shd wg head (hrx5_rv_W1 W q s msg r); qlen_rep gv q; skb_rep shs sp s;
       bytes_at shm msg (sk_data s); wg_consts gv; mem_mgr gv).

(* inside case 1 / case 2 (message = skb->data), r fixed *)
Definition hrx5_rv_SC (msgid: ident) (Pf: Prop) (CSw: compspecs) (gv: globals) (W: rxw) (q: int) (shd: share)
  (wg head: val) (shs: share) (sp: val) (s: skb) (shm: share) (msg: list byte) (r: list byte) : environ -> mpred :=
  PROP (Zlength r = 32; Pf)
  LOCAL (temp msgid (sk_data s); temp HRC._peer nullval; gvars gv; temp HRC._wg wg; temp HRC._skb sp)
  SEP (rxw_rep CSw gv shd wg head (hrx5_rv_W1 W q s msg r); qlen_rep gv q; skb_rep shs sp s;
       bytes_at shm msg (sk_data s); wg_consts gv; mem_mgr gv).

(* Qtail: before the common tail: the authenticated peer a, the world W2 whose tail is the model's result *)
Definition hrx5_rv_Qtail x25519 aead_dec xaead_enc xaead_dec (CSw: compspecs) (gv: globals) (W: rxw) (q: int)
  (shd: share) (wg head: val) (shs: share) (sp: val) (s: skb) (shm: share) (msg: list byte) : environ -> mpred :=
  EX d: rxdraw, EX W2: rxw, EX a: val,
  PROP (rxdraw_ok (rw_T W) d;
        rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d = hrx5_rv_tailw W2 a (sk_len s);
        hrx5_rv_tail_ok W2 a)
  LOCAL (temp HRC._peer a; gvars gv; temp HRC._skb sp)
  SEP (rxw_rep CSw gv shd wg head W2; qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s);
       wg_consts gv; mem_mgr gv).

(* ------------------------------------------------------------------------------------------------ *)
(* the segment statements                                                                            *)
(* ------------------------------------------------------------------------------------------------ *)

Definition hrx5_rv_C_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  Int.eq (hrx5_tw msg) (Int.repr 3) = true ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_S0 CSw gv W q shd wg head shs sp s shm msg) hrx5_rv_COOKIE
    (hrx5_rv_retonly (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg)).

Definition hrx5_rv_LV_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_S0 CSw gv W q shd wg head shs sp s shm msg) hrx5_rv_LV
    (overridePost (hrx5_rv_SV CSw gv W q shd wg head shs sp s shm msg)
       (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg)).

Definition hrx5_rv_N1_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg r,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_SC HRC._message
       (Int.eq (hrx5_tw msg) Int.one = true /\ hrx5_rv_nc W q s msg r = true)
       CSw gv W q shd wg head shs sp s shm msg r) hrx5_rv_NC1
    (hrx5_rv_retonly (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg)).

Definition hrx5_rv_N2_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg r,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_SC HRC._message__1
       (Int.eq (hrx5_tw msg) (Int.repr 2) = true /\ hrx5_rv_nc W q s msg r = true)
       CSw gv W q shd wg head shs sp s shm msg r) hrx5_rv_NC2
    (hrx5_rv_retonly (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg)).

Definition hrx5_rv_I_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg r,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_SC HRC._message
       (Int.eq (hrx5_tw msg) Int.one = true /\ hrx5_rv_cons W q s msg r = true)
       CSw gv W q shd wg head shs sp s shm msg r) hrx5_rv_IREST
    (switch_ret_assert
       (overridePost (hrx5_rv_Qtail x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg)
          (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg))).

Definition hrx5_rv_RS_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg r,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_SC HRC._message__1
       (Int.eq (hrx5_tw msg) (Int.repr 2) = true /\ hrx5_rv_cons W q s msg r = true)
       CSw gv W q shd wg head shs sp s shm msg r) hrx5_rv_RREST
    (switch_ret_assert
       (overridePost (hrx5_rv_Qtail x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg)
          (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg))).

Definition hrx5_rv_T_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) gv W q shd wg head shs
    sp s shm msg,
  hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg ->
  @semax HRX Espec (hrx5_rv_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_rv_Qtail x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg) hrx5_rv_TAIL
    (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg).
