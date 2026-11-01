(* law handshake_receive: the PURE part of main's proof:
   the run (the raw keys), D's device, the harness's model of the three consume functions (the initiation and the
   response: copies of the proved hci5 / hcr5 models, hrx5_mci.v / hrx5_mcr.v; the cookie reply: hrx5ck_tgt here)
   and its agreement with the kernel's models, the message objects of the four packet kinds, and the harness's
   `path` in terms of the receive model (hrx5_model.v). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the run: the raw keys of D and K                                       *)
(* ---------------------------------------------------------------------- *)

Record hrx5_run := mkRunR5 { rr_rawd: list byte; rr_rawk: list byte }.

Definition hrx5_run_ok (R: hrx5_run) : Prop := Zlength (rr_rawd R) = 32 /\ Zlength (rr_rawk R) = 32.

(* the message object at skb->data: kind 0 = any bytes (malloc'd buffer of their length), 1 / 2 / 3 = a struct
   message_handshake_initiation / _response / _cookie *)
Inductive hrx5_obj :=
| OBuf (b: list byte)
| OInit (M: init_msg)
| OResp (M: resp_msg)
| OCookie (M: cookie_msg).

Definition obj_bytes (o: hrx5_obj) : list byte :=
  match o with
  | OBuf b => b | OInit M => init_bytes M | OResp M => resp_bytes M | OCookie M => cookie_msg_bytes M
  end.

Definition obj_kind (o: hrx5_obj) : Z :=
  match o with OBuf _ => 0 | OInit _ => 1 | OResp _ => 2 | OCookie _ => 3 end.

(* kind 0: never of a handshake length (the harness bumps them), below 2^32 (skb->len is an unsigned int) *)
Definition obj_ok (o: hrx5_obj) : Prop :=
  match o with
  | OBuf b => Zlength b <> 148 /\ Zlength b <> 92 /\ Zlength b <> 64 /\ Zlength b <= Int.max_unsigned
  | OInit M => im_ok M
  | OResp M => rm_ok M
  | OCookie M => cm_ok M
  end.

(* the node of the peer at a (the first one), or NULL *)
Fixpoint hrx5_nfind (NS: list hnode4) (a: val) : val :=
  match NS with
  | [] => nullval
  | N :: NS' => if eq_dec (hn_p N) a then hn_addr N else hrx5_nfind NS' a
  end.

Definition hrx5_head (NS: list hnode4) : val := match NS with [] => nullval | N :: _ => hn_addr N end.
Definition hrx5_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the harness's identities (m_identity_of) and D's static identity (setup_device) *)
Definition hrx5_ID (R: hrx5_run) : mident := mident_of x25519 (rr_rawd R).
Definition hrx5_IK (R: hrx5_run) : mident := mident_of x25519 (rr_rawk R).
Definition hrx5_sid (R: hrx5_run) : identity := setup_identity x25519 (rr_rawd R).

(* D with the cookie secret sec born at birth (main overwrites setup_device's draw) *)
Definition hrx5_D (R: hrx5_run) (wd itd ptd: val) (sec: list byte) (birth: int64) : device :=
  setup_dev x25519 wd itd ptd (rr_rawd R) sec birth.

(* the harness's mac1 key of D (mk1) and K's precomputed static-static with D (ss_k) *)
Definition hrx5_mk1 (R: hrx5_run) : list byte := snd (checker_keys (hrx5_sid R)).
Definition hrx5_ssk (R: hrx5_run) : list byte := m_precomputed_model x25519 (hrx5_IK R) (mi_pub (hrx5_ID R)).

(* the harness's model of wg_cookie_message_consume: the first entry of the table's list with the receiver index,
   of a handshake or keypair type; the first node whose peer is the entry's (= sfind PS); its peer sent a mac1 and
   the cookie decrypts (the peer's cookie key, its last mac1, the nonce): (peer, its state before, plaintext) *)
Definition hrx5ck_tgt (T: tstate) (PS: list (val * share * peer)) (M: cookie_msg)
  : option (val * peer * list byte) :=
  match t_find_index T (t_L T) (cm_receiver M) with
  | None => None
  | Some (_, E) =>
    if Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero then None else
    match sfind PS (e_peer E) with
    | None => None
    | Some (_, P) =>
      let C := p_cookie P in
      if ck_sent C then
        match xaead_dec (ck_dkey C) (cm_nonce M) (ck_last_mac1 C) (cm_enc M) with
        | Some pt => Some (e_peer E, P, pt)
        | None => None
        end
      else None
    end
  end.

Definition hrx5ck_new (P: peer) (pt: list byte) (now: int64) : peer :=
  let C := p_cookie P in
  p_set_cookie P (mkCookie now true pt false (ck_last_mac1 C) (ck_dkey C) (ck_mkey C)).

Lemma hrx5ck_agree T PS M now :
  message_consume_model xaead_dec T PS M now =
  match hrx5ck_tgt T PS M with Some (a, P, pt) => Some (a, hrx5ck_new P pt now) | None => None end.
Proof.
  unfold message_consume_model, t_lookup, hrx5ck_tgt, hrx5ck_new.
  destruct (t_find_index T (t_L T) (cm_receiver M)) as [[a E]|]; [| reflexivity].
  destruct (Int.eq _ Int.zero); [reflexivity |].
  destruct (sfind PS (e_peer E)) as [[sh P]|]; [| reflexivity].
  destruct (ck_sent (p_cookie P)); cbn [negb]; [| reflexivity].
  destruct (xaead_dec _ _ _ _); reflexivity.
Qed.

(* the receive world before dispatch: no keypair in a slot, the log reset *)
Definition hrx5_W0 (D: device) (T: tstate) (PS: list (val * share * peer)) (S: shim) (w: list int64)
  (kc lul: int64) : rxw :=
  mkRW D T PS [] S w kc lul rx0.

(* the harness's `path` after dispatch: 1 = consumed (or a cookie reply), 2 = a cookie reply sent, 0 = nothing;
   ul and the verdict are the receive model's (load_model, validate_model with the rotation's draw) *)
Definition hrx5_path (W: rxw) (q: int) (s: skb) (msg: list byte) (d: rxdraw) : Z :=
  if hrx5_fwd msg then
    if Int.eq (hrx5_tw msg) (Int.repr 3) then 1 else
    let now := s_boot (rw_S W) in
    let ul := fst (load_model q (rw_lul W) now) in
    let v := fst (validate_model (d_cc (rw_D W)) s msg ul now (s_rlallow (rw_S W)) (rd_r d)) in
    if rx_consumes ul v then 1 else if rx_needs_cookie ul v then 2 else 0
  else 0.

(* what the harness's model block computes before dispatch (target, acc_init, acc_resp), on the state before the
   packet: the initiation / response model of the accepted peer's node (any node or NULL when rejected), the cookie
   reply's node or NULL *)
Definition hrx5_acc_ok (R: hrx5_run) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate)
  (o: hrx5_obj) (now: int64) (tg: val) (ai ar: Z) : Prop :=
  let fwd := hrx5_fwd (obj_bytes o) in
  match o with
  | OInit M =>
      ar = 0 /\
      (if fwd then
         match hrx5ci_tgt x25519 aead_dec (hrx5_ID R) PS M now with
         | Some (a, _, _, _, _) => ai = 1 /\ tg = hrx5_nfind NS a
         | None => ai = 0 /\ (tg = nullval \/ In tg (map hn_addr NS))
         end
       else ai = 0 /\ tg = nullval)
  | OResp M =>
      ai = 0 /\
      (if fwd then
         match hrx5cr_tgt x25519 aead_dec (hrx5_ID R) T PS M with
         | Some (a, _, _, _) => ar = 1 /\ tg = hrx5_nfind NS a
         | None => ar = 0 /\ (tg = nullval \/ In tg (map hn_addr NS))
         end
       else ar = 0 /\ tg = nullval)
  | OCookie M =>
      ai = 0 /\ ar = 0 /\
      tg = (if fwd then match hrx5ck_tgt T PS M with Some (a, _, _) => hrx5_nfind NS a | None => nullval end
            else nullval)
  | OBuf _ => ai = 0 /\ ar = 0 /\ tg = nullval
  end.

End Model.
