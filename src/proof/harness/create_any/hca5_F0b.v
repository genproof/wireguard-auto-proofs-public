(* law create_any: Segment F0b (hca5_fdefs.v) = the op == 0 branch body's statement 6 (if (ia.ok) { the harness's step-by-step model of create_initiation }), from hca5_F0S1 m to hca5_F0S2 m.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: the same C). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_defs.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_lib.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_L1.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_L2.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_L3.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_L4.
Require WgNoise.harness.x_create_any.code.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

#[local] Instance hca5_F0b_cceH' : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.

(* ia at the world, with the value typed at the world *)
Definition hca5_F0b_mivW (I: mident) : @reptype W_create_any t_mident :=
  (bytes (mi_priv I), (bytes (mi_pub I), Vint (if mi_ok I then Int.one else Int.zero))).
Lemma hca5_F0b_iaW sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_create_any sh t_mident (hca5_F0b_mivW I) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_create_any hca5_F0b_cceH' sh t_mident (mident_val I)
    (hca5_F0b_mivW I) (@JMeq_refl _ (mident_val I)) ltac:(vm_compute; reflexivity))).
Qed.

Lemma hca5_F0b_slog D S1 rr b idx : Zlength rr = 32 -> id_has (d_id D) = true ->
  s_log (hca5_ci_shim D S1 rr b idx) = rr.
Proof.
  intros Hl Hi. unfold hca5_ci_shim. rewrite Hi.
  assert (s_log (shim_draw S1 rr) = rr).
  { unfold shim_draw; cbn [s_log]. rewrite Hl. change (Z.min 32 32) with 32.
    rewrite sublist_same by lia. rewrite sublist_nil, app_nil_r. reflexivity. }
  destruct b; auto.
Qed.

Lemma hca5_F0b_init_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (A & B & C & D & F). unfold init_bytes. rewrite !Zlength_app, !prot_rep3_le32_len, A, B, C, D, F.
  reflexivity.
Qed.

Lemma hca5_F0b_tai_len a b : Zlength (tai64n a b) = 12.
Proof. intros. unfold tai64n, be64, be32. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

Lemma hca5_F0b_pub_len x25519 R L : x25519_props x25519 -> Zlength (id_pub (d_id (hca5_D x25519 R L))) = 32.
Proof.
  intros X. unfold hca5_D, setup_dev, setup_identity, identity_of; cbn [d_id id_pub].
  destruct (memneq_bool _ _); [apply X | reflexivity].
Qed.

(* the four pieces composed: THEN from S0 to the expectation *)
Lemma hca5_F0b_THEN_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv rf: val) (Fr: mpred) (T: tstate) (E: entry) (H: handshake) (D: device) (S: shim) (w: list int64)
    (before rr ts: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F0b_facts x25519 aead_enc H D S before rr ts ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0b_S0 gv L m rv kv rf Fr T E H D S w before ts)
    hca5_F0b_THEN
    (overridePost (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts))
       (hca5_R gv)).
Proof.
  intros HH HF. apply sequential'.
  apply (hca5_F0b_L1n x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m rv kv rf Fr T E H D S w before rr ts HH HF).
  intros EZ.
  apply (hca5_F0b_L2n x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m rv kv rf Fr T E H D S w before rr ts HH HF EZ).
  intros DH.
  apply (hca5_F0b_L3n x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m rv kv rf Fr T E H D S w before rr ts HH HF EZ DH).
  intros SS.
  apply (hca5_F0b_L4n x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m rv kv rf Fr T E H D S w before rr ts HH HF EZ DH SS).
Qed.

Lemma hca5_F0b_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0S1 x25519 aead_enc gv L FR w m)
    hca5_F0b
    (overridePost (hca5_F0S2 x25519 aead_enc gv L FR w m) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_F0S1, hca5_Delta, hca5_R. rewrite hca5_F0b_eq.
  simplify_func_tycontext. abbreviate_semax.
  Intros R P T KS E M S1 rr idx S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app].
  rewrite hca5_F0b_iaW.
  forward.
  match goal with |- context [temp HC._t'49 ?v] =>
    change v with (Vint (if mi_ok (hca5_I x25519 R) then Int.one else Int.zero)) end.
  rewrite <- hca5_F0b_iaW.
  destruct (mi_ok (hca5_I x25519 R)) eqn:Hmi.
  - forward_if.
    unfold POSTCONDITION, abbreviate.
    assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
      by (unfold Delta, Delta_specs, abbreviate; reflexivity).
    rewrite HD; clear HD.
    pose proof H0 as (Hdev & Hsid & Hok & _).
    assert (HF: hca5_F0b_facts x25519 aead_enc (p_hs P) (hca5_D x25519 R L)
                  (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) (init_bytes M) rr (tai64n (s_rsec S1) (s_rnsec S1))).
    { destruct HH as (X & A & _).
      split; [exact X|]. split; [exact (aead_enc_length _ _ A)|]. split; [exact Hok|]. split; [exact H5|].
      split. { unfold hca5_CIshim. apply hca5_F0b_slog; auto. }
      split; [apply hca5_F0b_tai_len|]. split; [apply hca5_F0b_init_len; auto|].
      apply hca5_F0b_pub_len; auto. }
    eapply semax_pre; [| eapply semax_post;
      [| | | | apply (hca5_F0b_THEN_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m
                 (Val.of_bool (fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)))) (kents_head KS)
                 (Vint (p_refs P))
                 (ptable Tsh (l_pta L) (l_p L) * data_at Tsh t_mident (mident_val (hca5_I x25519 R)) (l_ia L) *
                  itable Tsh (l_ita L) (if fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))
                                        then t_insert T (hs_addr (l_p L)) idx else T) *
                  peer_rep Tsh (l_p L) (p_set_hs P (snd (hca5_CI x25519 aead_enc R L P M S1 rr idx))) *
                  hca5_rest x25519 L R P T KS S0 w * hca5_tok t_init_W m *
                  init_rep Ews m (snd (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))) *
                  hbytes Tsh (init_bytes M) (l_before L) * mem_mgr gv * noise_globals gv Int64.zero * FR *
                  hout Tsh 32 (l_raw L) * hout Tsh 32 (l_pub L) * hout Tsh 32 (l_psk L) *
                  hout Tsh 1 (l_nothing L) * hout Tsh 148 (l_img L) *
                  hout Tsh 92 (l_before1 L) * hout Tsh 92 (l_exp1 L) * hout Tsh 92 (l_img1 L))
                 T E (p_hs P) (hca5_D x25519 R L) (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) w
                 (init_bytes M) rr (tai64n (s_rsec S1) (s_rnsec S1)) HH HF)]].
    + unfold hca5_F0b_S0, hca5_F0b_Q, hca5_lvars; cbn [app]. entailer!.
    + rewrite !overridePost_normal'.
      replace (hca5_F0b_res x25519 aead_enc (p_hs P) (hca5_D x25519 R L)
                 (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) (init_bytes M) rr (tai64n (s_rsec S1) (s_rnsec S1)))
        with (hca5_X x25519 aead_enc R L P M S1 rr idx)
        by (unfold hca5_X, hca5_F0b_res; rewrite Hmi; reflexivity).
      unfold hca5_F0b_fin, hca5_F0b_Q, hca5_F0S2.
      apply exp_right with R. apply exp_right with P. apply exp_right with T. apply exp_right with KS.
      apply exp_right with E. apply exp_right with M. apply exp_right with S1. apply exp_right with rr.
      apply exp_right with idx. apply exp_right with S0.
      unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app].
      forget (hca5_X x25519 aead_enc R L P M S1 rr idx) as X.
      sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L)).
      sep_apply (hca5_F0b_hout Tsh (init_bytes M) 148 (l_before L) (hca5_F0b_init_len M H4)).
      sep_apply (hca5_F0b_hout Tsh (tai64n (s_rsec S1) (s_rnsec S1)) 12 (l_ts L) (hca5_F0b_tai_len _ _)).
      entailer!.
    + unfold hca5_R. destruct (frame_ret_assert _ _). simpl. intros; apply andp_left2, derives_refl.
    + unfold hca5_R. destruct (frame_ret_assert _ _). simpl. intros; apply andp_left2, derives_refl.
    + intros vl. unfold hca5_R. destruct (frame_ret_assert _ _). simpl. intros; apply andp_left2, derives_refl.
    + exfalso; apply Int.one_not_zero; auto.
  - forward_if.
    { exfalso; auto. }
    forward.
    unfold hca5_F0S2.
    apply exp_right with R. apply exp_right with P. apply exp_right with T. apply exp_right with KS.
    apply exp_right with E. apply exp_right with M. apply exp_right with S1. apply exp_right with rr.
    apply exp_right with idx. apply exp_right with S0.
    replace (hca5_X x25519 aead_enc R L P M S1 rr idx) with (false, init_bytes M, p_hs P)
      by (unfold hca5_X; rewrite Hmi; reflexivity).
    unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app fst snd].
    sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L)).
    sep_apply (hca5_F0b_hout Tsh (init_bytes M) 148 (l_before L) (hca5_F0b_init_len M H4)).
    sep_apply (hca5_F0b_hout Tsh (tai64n (s_rsec S1) (s_rnsec S1)) 12 (l_ts L) (hca5_F0b_tai_len _ _)).
    entailer!.
Qed.
