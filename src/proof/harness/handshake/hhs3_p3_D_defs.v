(* law handshake, phase P3, segment D (statement 74) cut further.

   Statement 74:  if (!acc1) NEG else POS
     NEG = CHECK(ret == NULL && hs_same(&snap, &pa.handshake) && pa.refcount.refcount == 1)
     POS = ck1; put; c_state; c_reph; c_ts; c_hck; c_ridx; c_lic; c_eph
       ck1     CHECK(ret == &pa && pa.refcount.refcount == 2)
       put     wg_peer_put(ret)
       c_state CHECK(pa.handshake.state == HANDSHAKE_CONSUMED_INITIATION)
       c_reph  CHECK(bytes_eq(pa.handshake.remote_ephemeral, m1->unencrypted_ephemeral, 32))
       c_ts    CHECK(bytes_eq(pa.handshake.latest_timestamp, ci.ts, 12) && bytes_eq(ci.ts, ts, 12))
       c_hck   CHECK(bytes_eq(pa.handshake.hash, ci.st.h, 32) && bytes_eq(pa.handshake.chaining_key, ci.st.ck, 32))
       c_ridx  CHECK(pa.handshake.remote_index == m1->sender_index)
       c_lic   CHECK(pa.handshake.last_initiation_consumption == m_last_consumption(snap.lic, now_b))
       c_eph   CHECK(bytes_eq(pa.handshake.ephemeral_private, snap.ephemeral_private, 32) &&
                     pa.handshake.entry.hashed == snap.hashed && pa.handshake.entry.index == snap.index)
   States (all variables fixed, no EX):
     hhs3_p3_D_N   pre/post of NEG (acc1 = false: Cin = None, pa = PA0, ret = NULL, ci = data_at_)
     hhs3_p3_D_st  pa's item = peer_rep pa P, ret = pa (acc1 = true, Cin = Some (pa, new));
                   P0 := st (hhs3_p3_new ..)  (pre/post of ck1, pre of put)
                   Q  := st (hhs3_PA2 (hhs3_p3_new ..))  (post of put, pre/post of every c_* ) *)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hhs3_p3_D_neg := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D] in
  (match hhs3_p3_D with Sifthenelse _ a _ => a | _ => Sskip end) in exact x).
Definition hhs3_p3_D_pos := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D] in
  (match hhs3_p3_D with Sifthenelse _ _ b => b | _ => Sskip end) in exact x).

(* the k-th statement of POS (0 = ck1, 1 = put, 2 = c_state, ..., 8 = c_eph) *)
Fixpoint hhs3_p3_D_nth (k: nat) (s: statement) : statement :=
  match k, s with
  | O, Ssequence a _ => a
  | O, a => a
  | S k', Ssequence _ b => hhs3_p3_D_nth k' b
  | S _, _ => Sskip
  end.

Definition hhs3_p3_D_ck1 := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 0 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_put := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 1 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_cstate := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 2 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_creph := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 3 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_cts := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 4 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_chck := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 5 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_cridx := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 6 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_clic := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 7 hhs3_p3_D_pos) in exact x).
Definition hhs3_p3_D_ceph := ltac:(let x := eval cbv beta iota delta [hhs3_p3_D_nth hhs3_p3_D_pos] in (hhs3_p3_D_nth 8 hhs3_p3_D_pos) in exact x).

Lemma hhs3_p3_D_pos_eq :
  hhs3_p3_D_pos =
  Ssequence hhs3_p3_D_ck1 (Ssequence hhs3_p3_D_put (Ssequence hhs3_p3_D_cstate (Ssequence hhs3_p3_D_creph
  (Ssequence hhs3_p3_D_cts (Ssequence hhs3_p3_D_chck (Ssequence hhs3_p3_D_cridx
  (Ssequence hhs3_p3_D_clic hhs3_p3_D_ceph))))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* NEG's pre and post *)
Definition hhs3_p3_D_N (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (a0 f0 l0: int64) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) (nowb: int64)
  : environ -> mpred :=
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         0 <= Int64.unsigned nowb < 2 ^ 62; s_boot S = nowb;
         hhs3_p3_acc x25519 aead_dec R L M1 nowb = false;
         hhs3_cin x25519 aead_dec R L M1 nowb = None]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_b (Vlong nowb); temp HC._ret nullval;
            temp HC._acc1 (Vint Int.zero);
            temp HC._all_ok (Vint (if hhs3_p3_ok25 x25519 R I nowb then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p3_sep x25519 gv L FR R S m1 m2 I M1 H1 MI
           (peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L))
           (@data_at_ HCS Tsh t_mcinit (l_ci L))
           (hout Tsh 148 (l_imgb L))))).

(* POS's states: pa's item peer_rep pa P *)
Definition hhs3_p3_D_st (P: peer) (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (a0 f0 l0: int64) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) (nowb: int64)
  (CI1: list byte * list byte * list byte * list byte) (CI2: list byte * list byte * list byte)
  : environ -> mpred :=
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         0 <= Int64.unsigned nowb < 2 ^ 62; s_boot S = nowb;
         hhs3_p3_acc x25519 aead_dec R L M1 nowb = true;
         hhs3_cs1 x25519 aead_dec R M1 = Some CI1;
         hhs3_p3_cs2 x25519 aead_dec R M1 CI1 = Some CI2;
         hhs3_cin x25519 aead_dec R L M1 nowb = Some (l_pa L, hhs3_p3_new x25519 R L M1 nowb CI2);
         fst (fst CI2) = hhs3_ts I]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_b (Vlong nowb); temp HC._ret (l_pa L);
            temp HC._acc1 (Vint Int.one);
            temp HC._all_ok (Vint (if hhs3_p3_ok25 x25519 R I nowb then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p3_sep x25519 gv L FR R S m1 m2 I M1 H1 MI
           (peer_rep Tsh (l_pa L) P)
           (@data_at HCS Tsh t_mcinit (hhs3_p3_civ x25519 R CI1 CI2) (l_ci L))
           (hout Tsh 148 (l_imgb L))))).

Definition hhs3_p3_D_P0 gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 : environ -> mpred :=
  hhs3_p3_D_st (hhs3_p3_new x25519 R L M1 nowb CI2) gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2.
Definition hhs3_p3_D_Q gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 : environ -> mpred :=
  hhs3_p3_D_st (hhs3_PA2 (hhs3_p3_new x25519 R L M1 nowb CI2)) gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2.

End States.
