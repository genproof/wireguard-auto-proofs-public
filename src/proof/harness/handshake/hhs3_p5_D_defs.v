(* law handshake, phase P5, segment D (statement 108) cut further.

   Statement 108:  if (!acc2) NEG else POS
     NEG = CHECK(ret == NULL && hs_same(&snap, &pb.handshake) && pb.refcount.refcount == 1)
     POS = ck1; put; c_state; c_reph; c_hck; c_ridx; c_fin
       ck1     CHECK(ret == &pb && pb.refcount.refcount == 2)
       put     wg_peer_put(ret)
       c_state CHECK(pb.handshake.state == HANDSHAKE_CONSUMED_RESPONSE)
       c_reph  CHECK(bytes_eq(pb.handshake.remote_ephemeral, m2->unencrypted_ephemeral, 32))
       c_hck   CHECK(bytes_eq(pb.handshake.hash, st2.h, 32) && bytes_eq(pb.handshake.chaining_key, st2.ck, 32))
       c_ridx  CHECK(pb.handshake.remote_index == m2->sender_index)
       c_fin   CHECK(bytes_eq(pb.handshake.ephemeral_private, snap.ephemeral_private, 32) &&
                     bytes_eq(pb.handshake.latest_timestamp, snap.latest_timestamp, 12) &&
                     pb.handshake.last_initiation_consumption == snap.last_initiation_consumption &&
                     table_has(&ita, &pb.handshake.entry) && pb.handshake.entry.index == snap.index)
   States (all variables FIXED, no EX; the PROP of SC):
     hhs3_p5_D_N   pre/post of NEG (acc2 = false: Cre = None, pb = PB1, ret = NULL, st2 = data_at_)
     hhs3_p5_D_st  pb's item = peer_rep pb P, ret = pb (acc2 = true, mcr = Some ST2, Cre = Some (pb, new ST2),
                   st2 = hhs3_p5_st2 L true ST2);
                   P0 := st (hhs3_p5_new .. ST2)                    (pre of ck1; put)
                   Q  := st (p_set_refs (hhs3_p5_new .. ST2) Int.one) (post of put, pre/post of every c_* ) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hhs3_p5_D_neg := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D] in
  (match hhs3_p5_D with Sifthenelse _ a _ => a | _ => Sskip end) in exact x).
Definition hhs3_p5_D_pos := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D] in
  (match hhs3_p5_D with Sifthenelse _ _ b => b | _ => Sskip end) in exact x).

(* the k-th statement of POS (0 = ck1, 1 = put, 2 = c_state, ..., 6 = c_fin) *)
Fixpoint hhs3_p5_D_nth (k: nat) (s: statement) : statement :=
  match k, s with
  | O, Ssequence a _ => a
  | O, a => a
  | S k', Ssequence _ b => hhs3_p5_D_nth k' b
  | S _, _ => Sskip
  end.

Definition hhs3_p5_D_ck1 := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 0 hhs3_p5_D_pos) in exact x).
Definition hhs3_p5_D_put := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 1 hhs3_p5_D_pos) in exact x).
Definition hhs3_p5_D_cstate := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 2 hhs3_p5_D_pos) in exact x).
Definition hhs3_p5_D_creph := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 3 hhs3_p5_D_pos) in exact x).
Definition hhs3_p5_D_chck := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 4 hhs3_p5_D_pos) in exact x).
Definition hhs3_p5_D_cridx := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 5 hhs3_p5_D_pos) in exact x).
Definition hhs3_p5_D_cfin := ltac:(let x := eval cbv beta iota delta [hhs3_p5_D_nth hhs3_p5_D_pos] in (hhs3_p5_D_nth 6 hhs3_p5_D_pos) in exact x).

Lemma hhs3_p5_D_pos_eq :
  hhs3_p5_D_pos =
  Ssequence hhs3_p5_D_ck1 (Ssequence hhs3_p5_D_put (Ssequence hhs3_p5_D_cstate (Ssequence hhs3_p5_D_creph
  (Ssequence hhs3_p5_D_chck (Ssequence hhs3_p5_D_cridx hhs3_p5_D_cfin))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* NEG's pre and post *)
Definition hhs3_p5_D_N (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (a0 f0 l0: int64) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (nowb: int64) (PA1: peer) (CI1: list byte * list byte * list byte * list byte)
  (CI2: list byte * list byte * list byte)
  (Q: hhs3_rsp) (M2: resp_msg) (H2: handshake) (MR: list byte * list byte * list byte * list byte * list byte)
  (nowa: int64) : environ -> mpred :=
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         0 <= Int64.unsigned nowa < 2 ^ 62; s_boot S = nowa;
         hhs3_p5_acc x25519 aead_dec R I MI M2 = false;
         hhs3_cre x25519 aead_dec R L I M1 H1 M2 = None]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_a (Vlong nowa); temp HC._ret nullval;
            temp HC._acc2 (Vint Int.zero);
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p5_sep x25519 gv L FR R S m1 m2 I M1 H1 MI PA1 Q M2 H2 MR
           (peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1))
           (hout Tsh 92 (l_rimg L))
           (@data_at_ HCS Tsh t_mstate (l_st2 L))))).

(* POS's states: pb's item peer_rep pb P *)
Definition hhs3_p5_D_st (P: peer) (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (a0 f0 l0: int64) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (nowb: int64) (PA1: peer) (CI1: list byte * list byte * list byte * list byte)
  (CI2: list byte * list byte * list byte)
  (Q: hhs3_rsp) (M2: resp_msg) (H2: handshake) (MR: list byte * list byte * list byte * list byte * list byte)
  (nowa: int64) (ST2: list byte * list byte) : environ -> mpred :=
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         0 <= Int64.unsigned nowa < 2 ^ 62; s_boot S = nowa;
         hhs3_p5_acc x25519 aead_dec R I MI M2 = true;
         hhs3_mcr x25519 aead_dec R MI M2 = Some ST2;
         hhs3_cre x25519 aead_dec R L I M1 H1 M2 = Some (l_pb L, hhs3_p5_new x25519 R L M1 H1 M2 ST2)]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_a (Vlong nowa); temp HC._ret (l_pb L);
            temp HC._acc2 (Vint Int.one);
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p5_sep x25519 gv L FR R S m1 m2 I M1 H1 MI PA1 Q M2 H2 MR
           (peer_rep Tsh (l_pb L) P)
           (hout Tsh 92 (l_rimg L))
           (hhs3_p5_st2 L true ST2)))).

Definition hhs3_p5_D_P0 gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2
  : environ -> mpred :=
  hhs3_p5_D_st (hhs3_p5_new x25519 R L M1 H1 M2 ST2)
    gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2.
Definition hhs3_p5_D_Q gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2
  : environ -> mpred :=
  hhs3_p5_D_st (p_set_refs (hhs3_p5_new x25519 R L M1 H1 M2 ST2) Int.one)
    gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2.

End States.
