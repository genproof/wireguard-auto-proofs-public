(* law create_any: segment F1b of main (hca5_fdefs.v: `if (s.state == CONSUMED_INITIATION) { the
   harness's step-by-step model of create_response }`) cut along its nested ifs.

   hca5_F1b = t'46 = s.state; if (t'46 == 2) THEN
     THEN  = le32_store(exp1, 2); le32_store(exp1+8, s.remote_index); st.ck = s.ck; st.h = s.hash;
             eph = random_log; m_clamp(eph); x.eph = eph; m_dh(E, eph, M_BASEPOINT); exp1+12 = E;
             t'21 = bytes_zero(E); if (!t'21) BODY2
     BODY2 = m_mix_hash(E); m_mix_ck(E); x.ck = st.ck; x.hash = st.h; t'20 = m_dh(dh, eph, s.reph); if (t'20) BODY3
     BODY3 = m_mix_ck(dh); x.ck = st.ck; t'19 = m_dh(dh, eph, s.rstatic); if (t'19) BODY4
     BODY4 = m_mix_ck(dh); m_mix_psk(key, s.psk); m_encrypt_and_hash(exp1+44, nothing, 0, key); x.ck = st.ck;
             x.hash = st.h; ok = 1; le32_store(exp1+4, wg_shim_random_u32); x.state = CREATED_RESPONSE

   The states: hca5_F1b_Q with the two snapshots OPENED (only the fields the block touches, as byte buffers
   at their offsets: x's eph / hash / ck and state; s's reph / rstatic / psk / hash / ck and remote_index),
   the shim's random_log and random_u32, ok, exp1, the scratch st / key / dh / eph / E, and an opaque frame Fr
   (everything else).  Every piece ends in hca5_F1b_fin of the expectation hca3_resp_exp, which unfolds to the
   branch the piece's hypotheses select.  The top (hca5_F1b.v) opens/closes the snapshots and the shim. *)
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
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
Require Import WgNoise.proof.harness.create_any.hca5_conv.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_create_any.code.
Local Open Scope logic.

#[local] Instance hca5_F1b_cceH : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

(* the then-branch of the last if of a sequence *)
Fixpoint hca5_F1b_inner (s: statement) : statement :=
  match s with
  | Ssequence _ b => hca5_F1b_inner b
  | Sifthenelse _ t _ => t
  | _ => Sskip
  end.

Definition hca5_F1b_THEN : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1b_inner hca5_F1b] in (hca5_F1b_inner hca5_F1b) in exact x).
Definition hca5_F1b_BODY2 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1b_inner hca5_F1b_THEN] in (hca5_F1b_inner hca5_F1b_THEN) in exact x).
Definition hca5_F1b_BODY3 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1b_inner hca5_F1b_BODY2] in (hca5_F1b_inner hca5_F1b_BODY2) in exact x).
Definition hca5_F1b_BODY4 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1b_inner hca5_F1b_BODY3] in (hca5_F1b_inner hca5_F1b_BODY3) in exact x).

Lemma hca5_F1b_eq :
  hca5_F1b = Ssequence (Sset HC._t'46 (Efield (Evar HC._s (Tstruct HC._hs_snap noattr)) HC._state tint))
                       (Sifthenelse (Ebinop Oeq (Etempvar HC._t'46 tint) (Econst_int (Int.repr 2) tint) tint)
                          hca5_F1b_THEN Sskip).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Small helpers (v1's hca3_F0b_lib ones, under this stem)                  *)
(* ---------------------------------------------------------------------- *)

Lemma hca5_F1b_hout sh bs n p : Zlength bs = n -> hbytes sh bs p |-- hout sh n p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hca5_F1b_hin sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. rewrite if_false by auto. reflexivity. Qed.

Lemma hca5_F1b_consts gv :
  hca5_consts gv =
  hbytes Ers basepoint9 (gv HC._x_create_any__M_BASEPOINT) *
  hc_const gv HC._x_create_any__M_CONSTRUCTION construction_bytes *
  hc_const gv HC._x_create_any__M_IDENTIFIER identifier_bytes.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Lengths                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hca5_F1b_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hca5_F1b_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hca5_F1b_hash_len. Qed.
Lemma hca5_F1b_kdf2_len a b : Zlength (kdf2 a b) = 32.
Proof. unfold kdf2, hmac. cbv zeta. apply hca5_F1b_hash_len. Qed.
Lemma hca5_F1b_kdf3_len a b : Zlength (kdf3 a b) = 32.
Proof. unfold kdf3, hmac. cbv zeta. apply hca5_F1b_hash_len. Qed.
Lemma hca5_F1b_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply hca5_F1b_hash_len. Qed.
Lemma hca5_F1b_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros. unfold clamp. rewrite !Zlength_upd_Znth. auto. Qed.
Lemma hca5_F1b_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.
Lemma hca5_F1b_put_len b o w : 0 <= o -> o + Zlength w <= Zlength b -> Zlength (hca3_put b o w) = Zlength b.
Proof. intros. unfold hca3_put. rewrite !Zlength_app, !Zlength_sublist by list_solve. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* A buffer with a hole: write w (n bytes) at offset o of the image b     *)
(* ---------------------------------------------------------------------- *)

(* b at p, without the n bytes at offset o *)
Definition hca5_F1b_hole (sh: share) (b: list byte) (o n: Z) (p: val) : mpred :=
  !! (@field_compatible HCS (tarray tuchar (Zlength b)) [] p /\ 0 <= o /\ 0 <= n /\ o + n <= Zlength b) &&
  (hbytes sh (sublist 0 o b) p * hbytes sh (sublist (o + n) (Zlength b) b) (offset_val (o + n) p)).

Lemma hca5_F1b_split sh b o n p :
  0 <= o -> 0 <= n -> o + n <= Zlength b ->
  hbytes sh b p |-- hout sh n (offset_val o p) * hca5_F1b_hole sh b o n p.
Proof.
  intros Ho Hn Hb. unfold hbytes, hout, hca5_F1b_hole.
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength b)) [] p) as FC by entailer!.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength b) o (o + n) (bytes b) p)
    by (unfold bytes; rewrite ?Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  unfold bytes. rewrite !sublist_map.
  replace (o + n - o) with n by lia. unfold hbytes, bytes.
  rewrite !Zlength_sublist by lia. replace (o - 0) with o by lia.
  entailer!.
Qed.

Lemma hca5_F1b_merge sh b o w p :
  hbytes sh w (offset_val o p) * hca5_F1b_hole sh b o (Zlength w) p |-- hbytes sh (hca3_put b o w) p.
Proof.
  unfold hbytes, hca5_F1b_hole. Intros. rename H into FC.
  assert (Hl: Zlength (hca3_put b o w) = Zlength b) by (apply hca5_F1b_put_len; lia).
  rewrite Hl.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength b) o (o + Zlength w) (bytes (hca3_put b o w)) p)
    by (unfold bytes; rewrite ?Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  unfold bytes, hca3_put. rewrite !sublist_map.
  replace (o + Zlength w - o) with (Zlength w) by lia.
  unfold hbytes, bytes. rewrite !Zlength_sublist by lia.
  replace (sublist 0 o (sublist 0 o b ++ w ++ sublist (o + Zlength w) (Zlength b) b)) with (sublist 0 o b)
    by list_solve.
  replace (sublist o (o + Zlength w) (sublist 0 o b ++ w ++ sublist (o + Zlength w) (Zlength b) b)) with w
    by list_solve.
  replace (sublist (o + Zlength w) (Zlength b) (sublist 0 o b ++ w ++ sublist (o + Zlength w) (Zlength b) b))
    with (sublist (o + Zlength w) (Zlength b) b) by list_solve.
  replace (o - 0) with o by lia. cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* The m_state st: its two fields ck (offset 0) and h (offset 32)          *)
(* ---------------------------------------------------------------------- *)

Section StSplit.
#[local] Existing Instance HCS.

Lemma hca5_F1b_st_split_ sh p : @field_compatible HCS t_mstate [] p ->
  @data_at_ HCS sh t_mstate p = hout sh 32 (offset_val 0 p) * hout sh 32 (offset_val 32 p).
Proof.
  intros FC. unfold t_mstate in *. unfold hout.
  unfold_data_at (data_at_ sh (Tstruct HH._m_state noattr) p). rewrite !field_at_data_at.
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type (Tstruct HH._m_state noattr) (DOT x_handshake.code._ck)) with (tarray tuchar 32).
  change (nested_field_type (Tstruct HH._m_state noattr) (DOT x_handshake.code._h)) with (tarray tuchar 32).
  change (nested_field_offset (Tstruct HH._m_state noattr) (DOT x_handshake.code._ck)) with 0.
  change (nested_field_offset (Tstruct HH._m_state noattr) (DOT x_handshake.code._h)) with 32.
  reflexivity.
Qed.

Lemma hca5_F1b_st_split sh ck h p : @field_compatible HCS t_mstate [] p -> Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p = hbytes sh ck (offset_val 0 p) * hbytes sh h (offset_val 32 p).
Proof.
  intros FC Hck Hh. unfold t_mstate in *. unfold mstate_val, hbytes.
  unfold_data_at (data_at sh (Tstruct HH._m_state noattr) _ p). rewrite !field_at_data_at.
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type (Tstruct HH._m_state noattr) (DOT x_handshake.code._ck)) with (tarray tuchar 32).
  change (nested_field_type (Tstruct HH._m_state noattr) (DOT x_handshake.code._h)) with (tarray tuchar 32).
  change (nested_field_offset (Tstruct HH._m_state noattr) (DOT x_handshake.code._ck)) with 0.
  change (nested_field_offset (Tstruct HH._m_state noattr) (DOT x_handshake.code._h)) with 32.
  rewrite Hck, Hh. reflexivity.
Qed.

End StSplit.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable gv: globals.
Variable L: hca5_loc.
(* main's temps that the block does not touch: m__1, r, kes, refs0 *)
Variables (m rv kv r0: val).
(* everything the block does not touch *)
Variable Fr: mpred.
(* the snapshot's handshake (s = the handshake before the call; x starts equal to it) *)
Variable H: handshake.
(* the shim after the call (random_log = the ephemeral draw rr, random_u32 = the index), the message image
   before the call *)
Variable S: shim.
Variables (before rr: list byte).

(* x: the fields the block writes (ephemeral_private 48, hash 208, chaining_key 240, state 28) *)
Definition hca5_F1b_xs (Hx: handshake) : list mpred :=
  [hbytes Tsh (hs_eph Hx) (offset_val 48 (l_x L)); hbytes Tsh (hs_hash Hx) (offset_val 208 (l_x L));
   hbytes Tsh (hs_ck Hx) (offset_val 240 (l_x L));
   @field_at W_create_any Tsh t_hsnap (DOT HC._state) (Vint (hs_state Hx)) (l_x L)].

(* s: the fields the block reads (remote_static 80, remote_ephemeral 112, preshared_key 176, hash 208,
   chaining_key 240, remote_index) *)
Definition hca5_F1b_ss : list mpred :=
  [hbytes Tsh (hs_rstatic H) (offset_val 80 (l_s L)); hbytes Tsh (hs_reph H) (offset_val 112 (l_s L));
   hbytes Tsh (hs_psk H) (offset_val 176 (l_s L)); hbytes Tsh (hs_hash H) (offset_val 208 (l_s L));
   hbytes Tsh (hs_ck H) (offset_val 240 (l_s L));
   @field_at W_create_any Tsh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex H)) (l_s L)].

(* the block's state: ok, exp1, x's handshake Hx, and st / key / dh / eph / E *)
Definition hca5_F1b_Q (okv: val) (expb: list byte) (Hx: handshake) (Rst Rkey Rdh Reph RE: mpred)
  : environ -> mpred :=
  PROPx []
  (LOCALx ([temp HC._m__1 m; temp HC._r rv; temp HC._ok okv; temp HC._kes kv; temp HC._refs0 r0] ++ hca5_lvars gv L)
  (SEPx ([Fr; hbytes Tsh expb (l_exp1 L)] ++ hca5_F1b_xs Hx ++ hca5_F1b_ss ++
         [hbytes Ews (s_log S) (gv HC._wg_shim_random_log);
          @data_at W_create_any Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32);
          Rst; Rkey; Rdh; Reph; RE; wg_consts gv; hca5_consts gv]))).

(* the end of the block: scratch back to any contents *)
Definition hca5_F1b_fin (res: bool * list byte * handshake) : environ -> mpred :=
  hca5_F1b_Q (Vint (if fst (fst res) then Int.one else Int.zero)) (snd (fst res)) (snd res)
    (@data_at_ HCS Tsh t_mstate (l_st L)) (hout Tsh 32 (l_key L)) (hout Tsh 32 (l_dh L))
    (hout Tsh 32 (l_eph L)) (hout Tsh 32 (l_E L)).

(* the expectation; u = wg_shim_random_u32 *)
Definition hca5_F1b_res : bool * list byte * handshake :=
  hca3_resp_exp x25519 aead_enc H before rr (s_u32 S).

(* the values along the block (as in hca3_resp_exp) *)
Definition hca5_F1b_eph : list byte := clamp rr.
Definition hca5_F1b_E : list byte := x25519 hca5_F1b_eph basepoint9.
Definition hca5_F1b_exp0 : list byte :=
  hca3_put (hca3_put before 0 (le32 (Int.repr 2))) 8 (le32 (hs_rindex H)).
Definition hca5_F1b_exp1 : list byte := hca3_put hca5_F1b_exp0 12 hca5_F1b_E.
Definition hca5_F1b_x0 : handshake := hs_set_eph H hca5_F1b_eph.
Definition hca5_F1b_h1 : list byte := mix_hash (hs_hash H) hca5_F1b_E.
Definition hca5_F1b_ck1 : list byte := kdf1 (hs_ck H) hca5_F1b_E.
Definition hca5_F1b_x1 : handshake := hs_set_ckh hca5_F1b_x0 hca5_F1b_ck1 hca5_F1b_h1.
Definition hca5_F1b_dh1 : list byte := x25519 hca5_F1b_eph (hs_reph H).
Definition hca5_F1b_ck2 : list byte := kdf1 hca5_F1b_ck1 hca5_F1b_dh1.
Definition hca5_F1b_x2 : handshake := hs_set_ckh hca5_F1b_x1 hca5_F1b_ck2 hca5_F1b_h1.
Definition hca5_F1b_dh2 : list byte := x25519 hca5_F1b_eph (hs_rstatic H).

(* the facts every piece may assume *)
Definition hca5_F1b_facts : Prop :=
  x25519_props x25519 /\ (forall k n ad m, Zlength (aead_enc k n ad m) = Zlength m + 16) /\
  hs_ok H /\ Zlength rr = 32 /\ s_log S = rr /\ Zlength before = 92 /\
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true /\
  @field_compatible W_create_any t_hsnap [] (l_x L) /\ @field_compatible W_create_any t_hsnap [] (l_s L) /\
  @field_compatible HCS t_mstate [] (l_st L).

(* THEN starts here (s.state = CONSUMED_INITIATION): ok = 0, exp1 = before, x = H, scratch any *)
Definition hca5_F1b_S1 : environ -> mpred :=
  hca5_F1b_Q (Vint Int.zero) before H
    (@data_at_ HCS Tsh t_mstate (l_st L)) (hout Tsh 32 (l_key L)) (hout Tsh 32 (l_dh L))
    (hout Tsh 32 (l_eph L)) (hout Tsh 32 (l_E L)).

(* BODY2 starts here (E not zero) *)
Definition hca5_F1b_S2 : environ -> mpred :=
  hca5_F1b_Q (Vint Int.zero) hca5_F1b_exp1 hca5_F1b_x0
    (@data_at HCS Tsh t_mstate (mstate_val (hs_ck H) (hs_hash H)) (l_st L)) (hout Tsh 32 (l_key L))
    (hout Tsh 32 (l_dh L)) (hbytes Tsh hca5_F1b_eph (l_eph L)) (hbytes Tsh hca5_F1b_E (l_E L)).

(* BODY3 starts here (and DH(eph, remote ephemeral) not zero) *)
Definition hca5_F1b_S3 : environ -> mpred :=
  hca5_F1b_Q (Vint Int.zero) hca5_F1b_exp1 hca5_F1b_x1
    (@data_at HCS Tsh t_mstate (mstate_val hca5_F1b_ck1 hca5_F1b_h1) (l_st L)) (hout Tsh 32 (l_key L))
    (hbytes Tsh hca5_F1b_dh1 (l_dh L)) (hbytes Tsh hca5_F1b_eph (l_eph L)) (hbytes Tsh hca5_F1b_E (l_E L)).

(* BODY4 starts here (and DH(eph, remote static) not zero) *)
Definition hca5_F1b_S4 : environ -> mpred :=
  hca5_F1b_Q (Vint Int.zero) hca5_F1b_exp1 hca5_F1b_x2
    (@data_at HCS Tsh t_mstate (mstate_val hca5_F1b_ck2 hca5_F1b_h1) (l_st L)) (hout Tsh 32 (l_key L))
    (hbytes Tsh hca5_F1b_dh2 (l_dh L)) (hbytes Tsh hca5_F1b_eph (l_eph L)) (hbytes Tsh hca5_F1b_E (l_E L)).

End States.
