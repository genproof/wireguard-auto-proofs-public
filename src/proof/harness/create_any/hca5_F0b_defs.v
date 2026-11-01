(* law create_any: segment F0b of main (hca5_fdefs.v: `if (ia.ok) { the harness's step-by-step
   model of create_initiation }`) cut along its nested ifs; port of v1's hca3_F0b_defs.v.

   hca5_F0b = t'49 = ia.ok; if (t'49) THEN
     THEN  = le32_store(exp, 1); m_start; 2 copies into x; eph = random_log; m_clamp; x.eph = eph; CHECK(eph != 0);
             m_dh(E, eph, M_BASEPOINT); exp+8 = E; t'14 = bytes_zero(E); if (!t'14) BODY2
     BODY2 = m_mix_hash(E); m_mix_ck(E); 2 copies into x; t'13 = m_dh(dh, eph, s.remote_static); if (t'13) BODY3
     BODY3 = m_mix_key(key, dh); m_encrypt_and_hash(exp+40, wa's static public); 2 copies into x;
             t'12 = bytes_zero(s.precomputed_static_static); if (!t'12) BODY4
     BODY4 = m_mix_key(key, ss); m_encrypt_and_hash(exp+88, ts); 2 copies into x; ok = 1;
             le32_store(exp+4, wg_shim_random_u32); x.state = CREATED_INITIATION

   The states: hca5_F0b_Q (ok, exp, x's handshake, and the five scratch objects st / key / dh / eph / E) with an
   opaque frame Fr (hca5_rest goes there); every piece ends in hca5_F0b_fin of the harness's expectation
   hca3_init_exp (with okid = true). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
Require WgNoise.harness.x_create_any.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

(* the then-branch of the last if of a sequence *)
Fixpoint hca5_F0b_inner (s: statement) : statement :=
  match s with
  | Ssequence _ b => hca5_F0b_inner b
  | Sifthenelse _ t _ => t
  | _ => Sskip
  end.

Definition hca5_F0b_THEN : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0b_inner hca5_F0b] in (hca5_F0b_inner hca5_F0b) in exact x).
Definition hca5_F0b_BODY2 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0b_inner hca5_F0b_THEN] in (hca5_F0b_inner hca5_F0b_THEN) in exact x).
Definition hca5_F0b_BODY3 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0b_inner hca5_F0b_BODY2] in (hca5_F0b_inner hca5_F0b_BODY2) in exact x).
Definition hca5_F0b_BODY4 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0b_inner hca5_F0b_BODY3] in (hca5_F0b_inner hca5_F0b_BODY3) in exact x).

Lemma hca5_F0b_eq :
  hca5_F0b = Ssequence (Sset HC._t'49 (Efield (Evar HC._ia (Tstruct HC._m_identity noattr)) HC._ok tint))
                       (Sifthenelse (Etempvar HC._t'49 tint) hca5_F0b_THEN Sskip).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable gv: globals.
Variable L: hca5_loc.
(* main's temps that the block does not touch: m, r, kes, refs0 *)
Variables (m rv kv rf: val).
(* everything the block does not touch *)
Variable Fr: mpred.
(* the snapshot's table, entry and handshake (s = the handshake before the call; x starts equal to it) *)
Variable T: tstate.
Variable E: entry.
Variable H: handshake.
(* the device (wa's static public key), the shim after the call (random_log = the ephemeral draw,
   random_u32 = the index), the message image before the call, the drawn bytes, the timestamp *)
Variable D: device.
Variable S: shim.
(* the refcount_t warnings *)
Variable w: list int64.
Variables (before rr ts: list byte).

Definition hca5_F0b_snap (Hx: handshake) : hsnap := snap_of T (hs_addr (l_p L)) E Hx.

(* the block's state: ok, exp, x's handshake Hx, and st / key / dh / eph / E *)
Definition hca5_F0b_Q (okv: val) (expb: list byte) (Hx: handshake) (Rst Rkey Rdh Reph RE: mpred)
  : environ -> mpred :=
  PROPx []
  (LOCALx ([temp HC._m m; temp HC._r rv; temp HC._ok okv; temp HC._kes kv; temp HC._refs0 rf] ++ hca5_lvars gv L)
  (SEPx [Fr; hbytes Tsh expb (l_exp L);
         @data_at HCS Tsh t_hsnap (hsnap_val (hca5_F0b_snap Hx)) (l_x L);
         @data_at HCS Tsh t_hsnap (hsnap_val (hca5_F0b_snap H)) (l_s L);
         Rst; Rkey; Rdh; Reph; RE;
         hbytes Tsh ts (l_ts L); device_rep Tsh (l_wa L) D; shim_state4 gv S w; wg_consts gv; hca5_consts gv])).

(* the end of the block: scratch back to any contents *)
Definition hca5_F0b_fin (res: bool * list byte * handshake) : environ -> mpred :=
  hca5_F0b_Q (Vint (if fst (fst res) then Int.one else Int.zero)) (snd (fst res)) (snd res)
    (@data_at_ HCS Tsh t_mstate (l_st L)) (hout Tsh 32 (l_key L)) (hout Tsh 32 (l_dh L))
    (hout Tsh 32 (l_eph L)) (hout Tsh 32 (l_E L)).

(* the expectation when ia.ok holds; u = wg_shim_random_u32 *)
Definition hca5_F0b_res : bool * list byte * handshake :=
  hca3_init_exp x25519 aead_enc true (id_pub (d_id D)) H before rr ts (s_u32 S).

(* the values along the block (as in hca3_init_exp) *)
Definition hca5_F0b_eph : list byte := clamp rr.
Definition hca5_F0b_E : list byte := x25519 hca5_F0b_eph basepoint9.
Definition hca5_F0b_h0 : list byte := mix_hash init_hash (hs_rstatic H).
Definition hca5_F0b_exp1 : list byte := hca3_put (hca3_put before 0 (le32 (Int.repr 1))) 8 hca5_F0b_E.
Definition hca5_F0b_x0 : handshake := hs_set_eph (hs_set_ckh H init_ck hca5_F0b_h0) hca5_F0b_eph.
Definition hca5_F0b_h1 : list byte := mix_hash hca5_F0b_h0 hca5_F0b_E.
Definition hca5_F0b_ck1 : list byte := kdf1 init_ck hca5_F0b_E.
Definition hca5_F0b_x1 : handshake := hs_set_ckh hca5_F0b_x0 hca5_F0b_ck1 hca5_F0b_h1.
Definition hca5_F0b_dh : list byte := x25519 hca5_F0b_eph (hs_rstatic H).
Definition hca5_F0b_ck2 : list byte := kdf1 hca5_F0b_ck1 hca5_F0b_dh.
Definition hca5_F0b_key2 : list byte := kdf2 hca5_F0b_ck1 hca5_F0b_dh.
Definition hca5_F0b_encs : list byte := aead_enc hca5_F0b_key2 0 hca5_F0b_h1 (id_pub (d_id D)).
Definition hca5_F0b_h2 : list byte := mix_hash hca5_F0b_h1 hca5_F0b_encs.
Definition hca5_F0b_exp2 : list byte := hca3_put hca5_F0b_exp1 40 hca5_F0b_encs.
Definition hca5_F0b_x2 : handshake := hs_set_ckh hca5_F0b_x1 hca5_F0b_ck2 hca5_F0b_h2.

(* the facts every piece may assume *)
Definition hca5_F0b_facts : Prop :=
  x25519_props x25519 /\ (forall k n ad m, Zlength (aead_enc k n ad m) = Zlength m + 16) /\
  hs_ok H /\ Zlength rr = 32 /\ s_log S = rr /\ Zlength ts = 12 /\ Zlength before = 148 /\
  Zlength (id_pub (d_id D)) = 32.

(* THEN starts here (ia.ok = 1): ok = 0, exp = before, x = H, scratch any *)
Definition hca5_F0b_S0 : environ -> mpred :=
  hca5_F0b_Q (Vint Int.zero) before H
    (@data_at_ HCS Tsh t_mstate (l_st L)) (hout Tsh 32 (l_key L)) (hout Tsh 32 (l_dh L))
    (hout Tsh 32 (l_eph L)) (hout Tsh 32 (l_E L)).

(* BODY2 starts here (E not zero) *)
Definition hca5_F0b_S2 : environ -> mpred :=
  hca5_F0b_Q (Vint Int.zero) hca5_F0b_exp1 hca5_F0b_x0
    (@data_at HCS Tsh t_mstate (mstate_val init_ck hca5_F0b_h0) (l_st L)) (hout Tsh 32 (l_key L))
    (hout Tsh 32 (l_dh L)) (hbytes Tsh hca5_F0b_eph (l_eph L)) (hbytes Tsh hca5_F0b_E (l_E L)).

(* BODY3 starts here (E not zero, DH(eph, rstatic) not zero) *)
Definition hca5_F0b_S3 : environ -> mpred :=
  hca5_F0b_Q (Vint Int.zero) hca5_F0b_exp1 hca5_F0b_x1
    (@data_at HCS Tsh t_mstate (mstate_val hca5_F0b_ck1 hca5_F0b_h1) (l_st L)) (hout Tsh 32 (l_key L))
    (hbytes Tsh hca5_F0b_dh (l_dh L)) (hbytes Tsh hca5_F0b_eph (l_eph L)) (hbytes Tsh hca5_F0b_E (l_E L)).

(* BODY4 starts here (and the precomputed static-static DH not zero) *)
Definition hca5_F0b_S4 : environ -> mpred :=
  hca5_F0b_Q (Vint Int.zero) hca5_F0b_exp2 hca5_F0b_x2
    (@data_at HCS Tsh t_mstate (mstate_val hca5_F0b_ck2 hca5_F0b_h2) (l_st L)) (hbytes Tsh hca5_F0b_key2 (l_key L))
    (hbytes Tsh hca5_F0b_dh (l_dh L)) (hbytes Tsh hca5_F0b_eph (l_eph L)) (hbytes Tsh hca5_F0b_E (l_E L)).

End States.
