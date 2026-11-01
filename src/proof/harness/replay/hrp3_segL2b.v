(* law replay: the loop body, segment L2b (acc = ib.ok && m_consume_initiation_1(&ci, &ib, m->eph,
   m->enc_static) && bytes_eq(ci.spub, ia.pub, 32) && m_consume_initiation_2(&ci, ss_b, m->enc_timestamp) &&
   m_ts_newer(ci.ts, latest) && m_not_flood(last, now); then ret / pa's state rewritten with
   hrp3_model_lemmas (cin_res = hrp3_acc)).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.
Require Import WgNoise.proof.libc.libc_bytes.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

#[local] Instance hrp3_segL2b_CCE_NW : change_composite_env Noise.CS W_replay.
Proof. make_cs_preserve Noise.CS W_replay. Defined.
#[local] Instance hrp3_segL2b_CCE_HW : change_composite_env HCS W_replay.
Proof. make_cs_preserve HCS W_replay. Defined.

(* ---------------------------------------------------------------------- *)
(* The model chain, stage by stage                                         *)
(* ---------------------------------------------------------------------- *)

Section Chain.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variables (IB: mident) (IApub SS lat: list byte) (last now: int64) (M: init_msg).

Definition hrp3_segL2b_o1 : option (list byte * list byte * list byte * list byte) :=
  if mi_ok IB then m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) else None.
Definition hrp3_segL2b_s2 (o: option (list byte * list byte * list byte * list byte))
  : option (list byte * list byte * list byte * list byte) :=
  match o with
  | Some (s, key, ck, h) => if bytes_eqb s IApub then Some (s, key, ck, h) else None
  | None => None
  end.
Definition hrp3_segL2b_s3 (o: option (list byte * list byte * list byte * list byte))
  : option (list byte * list byte * list byte * list byte * list byte) :=
  match o with
  | Some (s, key, ck, h) =>
      match m_consume_init2_model aead_dec SS ck h (im_enct M) with
      | Some (t, ck2, h2) => Some (t, ck2, h2, kdf2 ck SS, s)
      | None => None
      end
  | None => None
  end.
Definition hrp3_segL2b_s4 (o: option (list byte * list byte * list byte * list byte * list byte))
  : option (list byte * list byte * list byte * list byte * list byte) :=
  match o with
  | Some (t, ck2, h2, k, s) => if ts_newer t lat then Some (t, ck2, h2, k, s) else None
  | None => None
  end.
Definition hrp3_segL2b_s5 (o: option (list byte * list byte * list byte * list byte * list byte))
  : option (list byte * list byte * list byte * list byte * list byte) :=
  match o with
  | Some (t, ck2, h2, k, s) => if not_flood last now then Some (t, ck2, h2, k, s) else None
  | None => None
  end.
Definition hrp3_segL2b_o5 := hrp3_segL2b_s5 (hrp3_segL2b_s4 (hrp3_segL2b_s3 (hrp3_segL2b_s2 hrp3_segL2b_o1))).

Lemma hrp3_segL2b_acc :
  hrp3_acc x25519 aead_dec IB IApub SS lat last now M =
  match hrp3_segL2b_o5 with Some (t, ck2, h2, _, _) => Some (t, ck2, h2) | None => None end.
Proof.
  unfold hrp3_acc, hrp3_ts, hrp3_segL2b_o5, hrp3_segL2b_s5, hrp3_segL2b_s4, hrp3_segL2b_s3, hrp3_segL2b_s2,
    hrp3_segL2b_o1.
  destruct (mi_ok IB); [| reflexivity].
  destruct (m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M)) as [[[[s key] ck] h] |];
    [| reflexivity].
  destruct (bytes_eqb s IApub); [| reflexivity].
  destruct (m_consume_init2_model aead_dec SS ck h (im_enct M)) as [[[t ck2] h2] |]; [| reflexivity].
  destruct (ts_newer t lat), (not_flood last now); reflexivity.
Qed.

Lemma hrp3_segL2b_b2s_len key m : Zlength (WgNoise.proof.blake2s.model.blake2s key 32 m) = 32.
Proof.
  unfold WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
    WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Lemma hrp3_segL2b_kdf1_len ck d : Zlength (kdf1 ck d) = 32.
Proof. unfold kdf1, hmac, HASH. apply hrp3_segL2b_b2s_len. Qed.
Lemma hrp3_segL2b_kdf2_len ck d : Zlength (kdf2 ck d) = 32.
Proof. unfold kdf2, hmac, HASH. apply hrp3_segL2b_b2s_len. Qed.
Lemma hrp3_segL2b_mix_len h d : Zlength (mix_hash h d) = 32.
Proof. unfold mix_hash, HASH. apply hrp3_segL2b_b2s_len. Qed.

Lemma hrp3_segL2b_o1_len aead_enc s key ck h : aead_props aead_enc aead_dec -> Zlength (im_encs M) = 48 ->
  hrp3_segL2b_o1 = Some (s, key, ck, h) ->
  Zlength s = 32 /\ Zlength key = 32 /\ Zlength ck = 32 /\ Zlength h = 32.
Proof.
  intros HA L E. unfold hrp3_segL2b_o1, m_consume_init1_model, consume_init_stage1 in E.
  destruct (mi_ok IB); [| discriminate]. cbn [im_eph im_encs id_priv id_pub] in E.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) eqn:D; [| discriminate]. injection E as <- <- <- <-.
  pose proof (aead_dec_length _ _ HA _ _ _ _ _ D) as D'.
  split; [rewrite D', L; reflexivity |]. split; [apply hrp3_segL2b_kdf2_len |].
  split; [apply hrp3_segL2b_kdf1_len | apply hrp3_segL2b_mix_len].
Qed.

Lemma hrp3_segL2b_s2_some o x : hrp3_segL2b_s2 o = Some x -> o = Some x.
Proof.
  unfold hrp3_segL2b_s2. destruct o as [[[[s' key'] ck'] h'] |]; [| discriminate].
  destruct (bytes_eqb s' IApub); [auto | discriminate].
Qed.
Lemma hrp3_segL2b_s4_some o x : hrp3_segL2b_s4 o = Some x -> o = Some x.
Proof.
  unfold hrp3_segL2b_s4. destruct o as [[[[[t ck2] h2] k] s'] |]; [| discriminate].
  destruct (ts_newer t lat); [auto | discriminate].
Qed.
Lemma hrp3_segL2b_s5_some o x : hrp3_segL2b_s5 o = Some x -> o = Some x.
Proof.
  unfold hrp3_segL2b_s5. destruct o as [[[[[t ck2] h2] k] s'] |]; [| discriminate].
  destruct (not_flood last now); [auto | discriminate].
Qed.

Lemma hrp3_segL2b_s3_len aead_enc s key ck h t ck2 h2 k s' : aead_props aead_enc aead_dec ->
  Zlength (im_enct M) = 28 -> Zlength s = 32 ->
  hrp3_segL2b_s3 (Some (s, key, ck, h)) = Some (t, ck2, h2, k, s') ->
  Zlength t = 12 /\ Zlength ck2 = 32 /\ Zlength h2 = 32 /\ Zlength k = 32 /\ Zlength s' = 32.
Proof.
  intros HA L2 Ls E. unfold hrp3_segL2b_s3 in E.
  unfold m_consume_init2_model, consume_init_stage2 in E. cbn [im_enct] in E.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) eqn:D; [| discriminate]. injection E as <- <- <- <- <-.
  pose proof (aead_dec_length _ _ HA _ _ _ _ _ D) as D'.
  split; [rewrite D', L2; reflexivity |]. split; [apply hrp3_segL2b_kdf1_len |].
  split; [apply hrp3_segL2b_mix_len |]. split; [apply hrp3_segL2b_kdf2_len | exact Ls].
Qed.

Lemma hrp3_segL2b_o3_len aead_enc t ck2 h2 k s' : aead_props aead_enc aead_dec ->
  Zlength (im_encs M) = 48 -> Zlength (im_enct M) = 28 ->
  hrp3_segL2b_s3 (hrp3_segL2b_s2 hrp3_segL2b_o1) = Some (t, ck2, h2, k, s') ->
  Zlength t = 12 /\ Zlength ck2 = 32 /\ Zlength h2 = 32 /\ Zlength k = 32 /\ Zlength s' = 32.
Proof.
  intros HA L1 L2 E.
  destruct (hrp3_segL2b_s2 hrp3_segL2b_o1) as [[[[s key] ck] h] |] eqn:E2; [| discriminate].
  apply hrp3_segL2b_s2_some in E2. apply (hrp3_segL2b_o1_len aead_enc) in E2; auto.
  apply (hrp3_segL2b_s3_len aead_enc s key ck h); tauto.
Qed.

End Chain.

(* ---------------------------------------------------------------------- *)
(* Field splits: the message's three byte fields, ci's spub / ts          *)
(* ---------------------------------------------------------------------- *)

Lemma hrp3_segL2b_isplit sh M m : im_ok M ->
  @data_at Noise.CS sh t_init (init_val M) m =
  (!! (@field_compatible Noise.CS t_init [] m) &&
   (@field_at Noise.CS sh t_init (DOT I._header) (Vint (im_type M)) m *
    @field_at Noise.CS sh t_init (DOT I._sender_index) (Vint (im_sender M)) m *
    hbytes sh (im_eph M) (offset_val 8 m) * hbytes sh (im_encs M) (offset_val 40 m) *
    hbytes sh (im_enct M) (offset_val 88 m) *
    @field_at Noise.CS sh t_init (DOT I._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m))%logic.
Proof.
  intros (L1 & L2 & L3 & L4 & L5). unfold hbytes. rewrite L1, L2, L3.
  rewrite <- !(@data_at_tarray_tuchar_cs Noise.CS HCS).
  apply pred_ext.
  - assert_PROP (@field_compatible Noise.CS t_init [] m) by entailer!.
    unfold_data_at (@data_at Noise.CS sh t_init (init_val M) m).
    rewrite (@field_at_data_at Noise.CS sh t_init (DOT I._unencrypted_ephemeral)).
    rewrite (@field_at_data_at Noise.CS sh t_init (DOT I._encrypted_static)).
    rewrite (@field_at_data_at Noise.CS sh t_init (DOT I._encrypted_timestamp)).
    rewrite !(@field_address_offset Noise.CS) by auto with field_compatible.
    entailer!.
  - Intros. unfold_data_at (@data_at Noise.CS sh t_init (init_val M) m).
    rewrite (@field_at_data_at Noise.CS sh t_init (DOT I._unencrypted_ephemeral)).
    rewrite (@field_at_data_at Noise.CS sh t_init (DOT I._encrypted_static)).
    rewrite (@field_at_data_at Noise.CS sh t_init (DOT I._encrypted_timestamp)).
    rewrite !(@field_address_offset Noise.CS) by auto with field_compatible.
    entailer!.
Qed.

Lemma hrp3_segL2b_csplit1 sh (ckv hv kv tv: list val) s p : Zlength s = 32 ->
  @data_at HCS sh t_mcinit ((ckv, hv), (kv, (bytes s, tv))) p =
  (!! (@field_compatible HCS t_mcinit [] p) &&
   (@field_at HCS sh t_mcinit (DOT HH._st) (ckv, hv) p * @field_at HCS sh t_mcinit (DOT HH._key) kv p *
    hbytes sh s (offset_val 96 p) * @field_at HCS sh t_mcinit (DOT HH._ts) tv p))%logic.
Proof.
  intros L. unfold hbytes. rewrite L.
  apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mcinit [] p) by entailer!.
    unfold_data_at (@data_at HCS sh t_mcinit ((ckv, hv), (kv, (bytes s, tv))) p).
    rewrite (@field_at_data_at HCS sh t_mcinit (DOT HH._spub)).
    rewrite !(@field_address_offset HCS) by auto with field_compatible.
    entailer!.
  - Intros. unfold_data_at (@data_at HCS sh t_mcinit ((ckv, hv), (kv, (bytes s, tv))) p).
    rewrite (@field_at_data_at HCS sh t_mcinit (DOT HH._spub)).
    rewrite !(@field_address_offset HCS) by auto with field_compatible.
    entailer!.
Qed.

Lemma hrp3_segL2b_csplit2 sh (ckv hv kv sv: list val) t p : Zlength t = 12 ->
  @data_at HCS sh t_mcinit ((ckv, hv), (kv, (sv, bytes t))) p =
  (!! (@field_compatible HCS t_mcinit [] p) &&
   (@field_at HCS sh t_mcinit (DOT HH._st) (ckv, hv) p * @field_at HCS sh t_mcinit (DOT HH._key) kv p *
    @field_at HCS sh t_mcinit (DOT HH._spub) sv p * hbytes sh t (offset_val 128 p)))%logic.
Proof.
  intros L. unfold hbytes. rewrite L.
  apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mcinit [] p) by entailer!.
    unfold_data_at (@data_at HCS sh t_mcinit ((ckv, hv), (kv, (sv, bytes t))) p).
    rewrite (@field_at_data_at HCS sh t_mcinit (DOT HH._ts)).
    rewrite !(@field_address_offset HCS) by auto with field_compatible.
    entailer!.
  - Intros. unfold_data_at (@data_at HCS sh t_mcinit ((ckv, hv), (kv, (sv, bytes t))) p).
    rewrite (@field_at_data_at HCS sh t_mcinit (DOT HH._ts)).
    rewrite !(@field_address_offset HCS) by auto with field_compatible.
    entailer!.
Qed.

(* ci's state after stage 1 / 2 (o: static, key, ck, h) and after stage 3 / 4 / 5 (o: ts, ck, h, key, static) *)
Definition hrp3_segL2b_ci1 (o: option (list byte * list byte * list byte * list byte)) (ci: val) : mpred :=
  match o with
  | Some (s, key, ck, h) => @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes key) (bytes s) (Zrepeat Vundef 12)) ci
  | None => @data_at_ HCS Tsh t_mcinit ci
  end.
Definition hrp3_segL2b_ci3 (o: option (list byte * list byte * list byte * list byte * list byte)) (ci: val)
  : mpred :=
  match o with
  | Some (t, ck2, h2, k, s) => @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 (bytes k) (bytes s) (bytes t)) ci
  | None => @data_at_ HCS Tsh t_mcinit ci
  end.

Lemma hrp3_segL2b_ci_final o ci :
  (forall t ck2 h2 k s, o = Some (t, ck2, h2, k, s) -> Zlength t = 12 /\ Zlength k = 32 /\ Zlength s = 32) ->
  hrp3_segL2b_ci3 o ci |--
  hrp3_ci_rep (match o with Some (t, ck2, h2, _, _) => Some (t, ck2, h2) | None => None end) ci.
Proof.
  intros HL. destruct o as [[[[[t ck2] h2] k] s] |]; unfold hrp3_segL2b_ci3, hrp3_ci_rep; [| apply derives_refl].
  destruct (HL _ _ _ _ _ eq_refl) as (L1 & L2 & L3).
  Exists (bytes k) (bytes s). unfold bytes. rewrite !Zlength_map. entailer!.
Qed.

Lemma hrp3_segL2b_fold (P: Prop) (A B: mpred) : A = (!! P && B)%logic -> P -> B |-- A.
Proof. intros E HP. rewrite E. apply andp_right; [apply prop_right; exact HP | apply derives_refl]. Qed.

Lemma hrp3_segL2b_tsplit bs p : hbytes Tsh bs p = (hbytes Ews bs p * hbytes (Share.comp Ews) bs p)%logic.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply comp_join_top. Qed.

Lemma hrp3_segL2b_peers pa PA M now (r: option (list byte * list byte * list byte)) :
  peers_rep (peers_after [(pa, Tsh, PA)]
    (match r with Some (t, ck, h) => Some (pa, hrp3_pa_after PA M t ck h now) | None => None end))
  |-- peer_rep Tsh pa (match r with Some (t, ck, h) => hrp3_pa_after PA M t ck h now | None => PA end).
Proof.
  destruct r as [[[t ck] h] |]; unfold peers_after, peers_rep; simpl.
  - destruct (EqDec_val pa pa) as [_ | n]; [| contradiction n; reflexivity]. simpl. cancel.
  - cancel.
Qed.

Lemma hrp3_segL2b_msplit sh I p : Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (!! (@field_compatible HCS t_mident [] p) &&
   (@field_at HCS sh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
    hbytes sh (mi_pub I) (offset_val 32 p) *
    @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p))%logic.
Proof.
  intros L1 L2. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mident [] p) by entailer!.
    unfold_data_at (@data_at HCS sh t_mident (mident_val I) p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite (@field_address_offset HCS) by auto with field_compatible.
    unfold hbytes. rewrite L2. entailer!.
  - Intros. unfold_data_at (@data_at HCS sh t_mident (mident_val I) p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite (@field_address_offset HCS) by auto with field_compatible.
    unfold hbytes. rewrite L2. entailer!.
Qed.

Lemma hrp3_segL2b_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) V sp ap mp steps i R :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec)
    (hrp3_PL2a x25519 aead_dec F V sp ap mp steps FR i) hrp3_segL2b
    (overridePost (hrp3_PL2b x25519 aead_dec F V sp ap mp steps FR i)
       (loop1_ret_assert (hrp3_Icont x25519 aead_dec F V sp ap mp steps FR i) R)).
Proof.
  intros HF HX HA.
  destruct F as [gv wa wb ita itb pta ptb pa pb ia ib rawa rawb psk ssb latest ci snap].
  unfold hrp3_PL2a, hrp3_Delta, hrp3_lvars, hrp3_temps, hrp3_segL2b. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  Intros Y M kind.
  destruct Y as [S TA PB PA lat last now hs Ms ha Ma].
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma] in *.
  unfold hrp3_world, hrp3_globs, app. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  abbreviate_semax.
  set (F0 := {| f_gv := gv; f_wa := wa; f_wb := wb; f_ita := ita; f_itb := itb; f_pta := pta; f_ptb := ptb;
    f_pa := pa; f_pb := pb; f_ia := ia; f_ib := ib; f_rawa := rawa; f_rawb := rawb; f_psk := psk; f_ssb := ssb;
    f_latest := latest; f_ci := ci; f_snap := snap |}) in *.
  pose proof H1 as Hinv. destruct H1 as (_ & _ & _ & Hpa & Hlat & Hlast & Hnow & _).
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma] in Hpa, Hlat, Hlast, Hnow.
  pose proof H0 as Hfix. destruct H0 as (LRA & LRB & LPSK & _ & _ & _).
  set (IA := hrp3_IA x25519 V) in *. set (IB := hrp3_IB x25519 V) in *.
  assert (LIA1: Zlength (mi_priv IA) = 32) by (unfold IA, hrp3_IA, mident_of, clamp; cbn [mi_priv]; list_solve).
  assert (LIB1: Zlength (mi_priv IB) = 32) by (unfold IB, hrp3_IB, mident_of, clamp; cbn [mi_priv]; list_solve).
  assert (LIA2: Zlength (mi_pub IA) = 32) by (apply HX).
  assert (LIB2: Zlength (mi_pub IB) = 32) by (apply HX).
  change (hrp3_mbuf true M mp) with (@malloc_token W_replay Ews t_init mp * init_rep Ews mp M)%logic.
  unfold init_rep. Intros. rename H0 into HMok.
  rewrite (@data_at_change_composite HCS W_replay hrp3_segL2b_CCE_HW Tsh t_mident (mident_val IB) (mident_val IB) (JMeq_refl _) eq_refl).
  rewrite (hrp3_segL2b_isplit Ews M mp HMok). Intros. rename H0 into FCm.
  unfold hrp3_consts, wg_consts. Intros.
  forward.
  rewrite <- (@data_at_change_composite HCS W_replay hrp3_segL2b_CCE_HW Tsh t_mident (mident_val IB) (mident_val IB) (JMeq_refl _) eq_refl).
  remember (hrp3_segL2b_o1 x25519 aead_dec IB M) as o1 eqn:E1def.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (@data_at_ HCS Tsh t_mcinit ci) in R in
    match R' with ?f _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'17 (Vint (match o1 with Some _ => Int.one | None => Int.zero end)) :: Q)
      (SEPx (f (hrp3_segL2b_ci1 o1 ci)))))
    end end.
  { assert (Hok: mi_ok IB = true).
    { unfold IB, hrp3_IB, mident_of. cbn [mi_ok]. destruct (_ && _)%bool; [reflexivity | contradiction H0; reflexivity]. }
    change (@data_at_ HCS Tsh t_mcinit ci) with
      (@data_at HCS Tsh t_mcinit ((Zrepeat Vundef 32, Zrepeat Vundef 32), (Zrepeat Vundef 32, (Zrepeat Vundef 32, Zrepeat Vundef 12))) ci).
    forward_call (gv, Tsh, ci, Zrepeat Vundef 12, Tsh, ib, IB, Ews, offset_val 8 mp, im_eph M, offset_val 40 mp, im_encs M).
    { pose proof (field_compatible_isptr _ _ _ FCm). auto. }
    { destruct HMok as (? & ? & _). auto. }
    forward.
    rewrite E1def. unfold hrp3_segL2b_o1, hrp3_segL2b_ci1. rewrite Hok.
    destruct (m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M)) as [[[[s key] ck] h] |];
      entailer!. }
  { assert (Hn: o1 = None).
    { rewrite E1def. unfold hrp3_segL2b_o1. replace (mi_ok IB) with false; [reflexivity |].
      unfold IB, hrp3_IB, mident_of. cbn [mi_ok]. destruct (_ && _)%bool; [discriminate | reflexivity]. }
    forward. entailer!; try rewrite Hn; first [reflexivity | apply derives_refl]. }
  (* stage 2: bytes_eq(ci.spub, ia.pub, 32) *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (hrp3_segL2b_ci1 o1 ci) in R in
    match R' with ?f _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'19 (Vint (match hrp3_segL2b_s2 (mi_pub IA) o1 with
                                                       Some _ => Int.one | None => Int.zero end)) :: Q)
      (SEPx (f (hrp3_segL2b_ci1 (hrp3_segL2b_s2 (mi_pub IA) o1) ci)))))
    end end.
  { destruct o1 as [[[[s key] ck] h] |] eqn:E1.
    2:{ exfalso. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    destruct (hrp3_segL2b_o1_len x25519 aead_dec IB M aead_enc s key ck h HA (proj1 (proj2 HMok)) (eq_sym E1def))
      as (Ls & Lkey & Lck & Lh).
    unfold hrp3_segL2b_ci1, mcinit_val.
    rewrite (hrp3_segL2b_csplit1 Tsh _ _ _ _ s ci Ls). Intros.
    match goal with Hf: @field_compatible HCS t_mcinit [] ci |- _ => rename Hf into FCci end.
    assert_PROP (@field_compatible HCS t_mident [] ia) as FCia by entailer!.
    rewrite (hrp3_segL2b_msplit Tsh IA ia LIA1 LIA2). Intros.
    forward_call (Tsh, offset_val 96 ci, s, Tsh, offset_val 32 ia, mi_pub IA).
    1: (entailer!; rewrite Ls; reflexivity).
    forward.
    sep_apply (hrp3_segL2b_fold _ _ _ (hrp3_segL2b_msplit Tsh IA ia LIA1 LIA2) FCia).
    sep_apply (hrp3_segL2b_fold _ _ _ (hrp3_segL2b_csplit1 Tsh (bytes ck) (bytes h) (bytes key) (Zrepeat Vundef 12) s ci Ls) FCci).
    unfold hrp3_segL2b_s2, hrp3_segL2b_ci1. destruct (bytes_eqb s (mi_pub IA)); entailer!. }
  { destruct o1 as [x |].
    { exfalso. match goal with Hc: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hc end. }
    forward. entailer!. }
  (* stage 3: m_consume_initiation_2(&ci, ss_b, m->encrypted_timestamp) *)
  remember (hrp3_segL2b_s2 (mi_pub IA) o1) as o2 eqn:E2def.
  set (SS := hrp3_SS x25519 V) in *.
  assert (LSS: Zlength SS = 32).
  { unfold SS, hrp3_SS, m_precomputed_model. destruct (_ && _)%bool; [apply HX | reflexivity]. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (hrp3_segL2b_ci1 o2 ci) in R in
    match R' with ?f _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'21 (Vint (match hrp3_segL2b_s3 aead_dec SS M o2 with
                                                       Some _ => Int.one | None => Int.zero end)) :: Q)
      (SEPx (f (hrp3_segL2b_ci3 (hrp3_segL2b_s3 aead_dec SS M o2) ci)))))
    end end.
  { destruct o2 as [[[[s key] ck] h] |] eqn:E2.
    2:{ exfalso. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    assert (E1': hrp3_segL2b_o1 x25519 aead_dec IB M = Some (s, key, ck, h)).
    { rewrite <- E1def. apply (hrp3_segL2b_s2_some (mi_pub IA)). auto. }
    destruct (hrp3_segL2b_o1_len x25519 aead_dec IB M aead_enc s key ck h HA (proj1 (proj2 HMok)) E1')
      as (Ls & Lkey & Lck & Lh).
    unfold hrp3_segL2b_ci1.
    rewrite (hrp3_segL2b_tsplit SS ssb). Intros.
    forward_call (gv, Tsh, ci, ck, h, bytes key, bytes s, Zrepeat Vundef 12, Ews, ssb, SS, offset_val 88 mp, im_enct M).
    { pose proof (field_compatible_isptr _ _ _ FCm). auto. }
    { unfold bytes. rewrite !Zlength_map. destruct HMok as (? & ? & ? & _). auto. }
    forward.
    sep_apply (derives_refl' _ _ (eq_sym (hrp3_segL2b_tsplit SS ssb))).
    unfold hrp3_segL2b_s3, hrp3_segL2b_ci3.
    destruct (m_consume_init2_model aead_dec SS ck h (im_enct M)) as [[[t ck2] h2] |]; entailer!. }
  { destruct o2 as [x |].
    { exfalso. match goal with Hc: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hc end. }
    forward. unfold hrp3_segL2b_s3, hrp3_segL2b_ci1, hrp3_segL2b_ci3. entailer!. }
  (* stage 4: m_ts_newer(ci.ts, latest) *)
  remember (hrp3_segL2b_s3 aead_dec SS M o2) as o3 eqn:E3def.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (hrp3_segL2b_ci3 o3 ci) in R in
    match R' with ?f _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'23 (Vint (match hrp3_segL2b_s4 lat o3 with
                                                       Some _ => Int.one | None => Int.zero end)) :: Q)
      (SEPx (f (hrp3_segL2b_ci3 (hrp3_segL2b_s4 lat o3) ci)))))
    end end.
  { destruct o3 as [[[[[t ck2] h2] k] s] |] eqn:E3.
    2:{ exfalso. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    assert (E3': hrp3_segL2b_s3 aead_dec SS M (hrp3_segL2b_s2 (mi_pub IA) (hrp3_segL2b_o1 x25519 aead_dec IB M)) =
                 Some (t, ck2, h2, k, s)) by (rewrite <- E1def, <- E2def; auto).
    destruct (hrp3_segL2b_o3_len x25519 aead_dec IB (mi_pub IA) SS M aead_enc t ck2 h2 k s HA
                (proj1 (proj2 HMok)) (proj1 (proj2 (proj2 HMok))) E3') as (Lt & Lck2 & Lh2 & Lk & Ls).
    unfold hrp3_segL2b_ci3, mcinit_val.
    rewrite (hrp3_segL2b_csplit2 Tsh (bytes ck2) (bytes h2) (bytes k) (bytes s) t ci Lt). Intros.
    match goal with Hf: @field_compatible HCS t_mcinit [] ci |- _ => rename Hf into FCci end.
    forward_call (Tsh, offset_val 128 ci, t, Tsh, latest, lat).
    forward.
    sep_apply (hrp3_segL2b_fold _ _ _ (hrp3_segL2b_csplit2 Tsh (bytes ck2) (bytes h2) (bytes k) (bytes s) t ci Lt) FCci).
    unfold hrp3_segL2b_s4, hrp3_segL2b_ci3. destruct (ts_newer t lat); entailer!. }
  { destruct o3 as [x |].
    { exfalso. match goal with Hc: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hc end. }
    forward. unfold hrp3_segL2b_s4, hrp3_segL2b_ci3. entailer!. }
  (* stage 5: m_not_flood(last, now) *)
  remember (hrp3_segL2b_s4 lat o3) as o4 eqn:E4def.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (hrp3_segL2b_ci3 o4 ci) in R in
    match R' with ?f _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'25 (Vint (match hrp3_segL2b_s5 last now o4 with
                                                       Some _ => Int.one | None => Int.zero end)) :: Q)
      (SEPx (f (hrp3_segL2b_ci3 (hrp3_segL2b_s5 last now o4) ci)))))
    end end.
  { destruct o4 as [[[[[t ck2] h2] k] s] |] eqn:E4.
    2:{ exfalso. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    forward_call (last, now).
    { rewrite Int64.signed_eq_unsigned; [rep_lia |].
      unfold Int64.max_signed, Int64.half_modulus, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl. lia. }
    forward.
    unfold hrp3_segL2b_s5. destruct (not_flood last now); [entailer! |].
    unfold hrp3_segL2b_ci3. entailer!. }
  { destruct o4 as [x |].
    { exfalso. match goal with Hc: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hc end. }
    forward. unfold hrp3_segL2b_s5, hrp3_segL2b_ci3. entailer!. }
  remember (hrp3_segL2b_s5 last now o4) as o5 eqn:E5def.
  forward.
  destruct HF as (HM & _ & _).
  assert (Hcin: cin_res x25519 aead_dec (hrp3_DB x25519 F0 V) [(pa, Tsh, PA)] M S =
      match hrp3_accv x25519 aead_dec V lat last now M with
      | Some (t, ck, h) => Some (pa, hrp3_pa_after PA M t ck h now) | None => None end).
  { rewrite <- H5. exact (proj1 (HM x25519 aead_enc aead_dec) (hrp3_DB x25519 F0 V) wb pa (v_RAWA V) (v_RAWB V)
        (hrp3_pskv V) (hrp3_PA0 x25519 F0 V) PA lat last S M eq_refl eq_refl Hpa). }
  assert (Hl5: forall t ck2 h2 k s, o5 = Some (t, ck2, h2, k, s) ->
                 Zlength t = 12 /\ Zlength k = 32 /\ Zlength s = 32).
  { intros t ck2 h2 k s' E. rewrite E5def in E. apply hrp3_segL2b_s5_some in E.
    rewrite E4def in E. apply hrp3_segL2b_s4_some in E. rewrite E3def, E2def, E1def in E.
    destruct (hrp3_segL2b_o3_len x25519 aead_dec IB (mi_pub IA) SS M aead_enc _ _ _ _ _ HA
                (proj1 (proj2 HMok)) (proj1 (proj2 (proj2 HMok))) E) as (? & ? & ? & ? & ?). auto. }
  assert (Hacc: hrp3_accv x25519 aead_dec V lat last now M =
                match o5 with Some (t, ck2, h2, _, _) => Some (t, ck2, h2) | None => None end).
  { unfold hrp3_accv. rewrite hrp3_segL2b_acc. rewrite E5def, E4def, E3def, E2def, E1def. reflexivity. }
  rewrite Hcin.
  sep_apply (hrp3_segL2b_fold _ _ _ (hrp3_segL2b_isplit Ews M mp HMok) FCm).
  sep_apply (hrp3_segL2b_ci_final o5 ci Hl5).
  sep_apply (hrp3_segL2b_peers pa PA M now (hrp3_accv x25519 aead_dec V lat last now M)).
  rewrite Hacc.
  destruct R as [Rn Rb Rc Rr]. cbn [loop1_ret_assert RA_normal].
  unfold hrp3_PL2b. Exists (mkRDyn S TA PB PA lat last now hs Ms ha Ma) M kind.
  unfold hrp3_world, hrp3_globs, hrp3_temps, hrp3_lvars, hrp3_mbuf, init_rep, hrp3_consts, wg_consts, app.
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma].
  rewrite Hacc.
  unfold F0. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  destruct o5 as [[[[[t ck2] h2] k] s'] |]; entailer!; apply derives_refl.
Qed.
