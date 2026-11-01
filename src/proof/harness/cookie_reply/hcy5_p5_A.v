(* law cookie_reply: segment A of phase P5 (statements 36..37: the rotation CHECKs on wg_shim_random_log / _prev, the CHECK of B's checker).  hcy5_S4 -> hcy5_p5_T1.
*)
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p5_a_lemmas.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* the two statements of segment A (36: the rotation CHECKs, 37: the CHECK of B's checker) *)
Definition hcy5_p5_a_s36 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 36 1)) in exact x).
Definition hcy5_p5_a_s37 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 37 1)) in exact x).
Lemma hcy5_p5_a_eq : hcy5_p5_A = Ssequence hcy5_p5_a_s36 hcy5_p5_a_s37.
Proof. reflexivity. Qed.

(* the reply is B's reply *)
Lemma hcy5_p5_a_cm_eq x xe R L Q m nonce rr S CM :
  hcy5_pkt_ok Q -> s_boot S = q_now Q ->
  hcy5_is CM (fst (mc_res xe (hcy5_CC1 x R L) (hcy5_skb Q m) (q_index Q) nonce (q_msg Q) S rr)) ->
  hcy5_is CM (hcy5_CM x xe R L Q nonce (hcy5_CK x R L Q m rr)).
Proof.
  unfold hcy5_is. intros HQ HS ->. destruct HQ as (_ & HL & _).
  unfold mc_res, message_create_model, hcy5_CM, hcy5_CK, hcy5_CC2, hcy5_mac1. rewrite HS, HL. reflexivity.
Qed.

Lemma hcy5_p5_a_cm_nonce x xe R L Q nonce CK CM :
  hcy5_is CM (hcy5_CM x xe R L Q nonce CK) -> cm_nonce CM = nonce.
Proof. unfold hcy5_is. intros ->. reflexivity. Qed.

(* the rotation (the secret 120 s old): the log holds the new secret, the previous log starts with the nonce *)
Lemma hcy5_p5_a_rot1 x R L Q S nonce rr :
  birthdate_expired (r_birth R) (Int64.repr 120) (q_now Q) = true -> Zlength nonce = 24 -> Zlength rr = 32 ->
  s_log (hcy5_S4shim S (hcy5_CC1 x R L) Q nonce rr) = rr /\
  sublist 0 24 (s_logprev (hcy5_S4shim S (hcy5_CC1 x R L) Q nonce rr)) = nonce /\
  cc_secret (hcy5_CC2 x R L Q rr) = rr /\ cc_birth (hcy5_CC2 x R L Q rr) = q_now Q.
Proof.
  intros E HN HR. unfold hcy5_S4shim, hcy5_CC2, checker_rotate, checker_rotates.
  change (cc_birth (hcy5_CC1 x R L)) with (r_birth R). rewrite E.
  unfold shim_draw. cbn [s_log s_logprev cc_secret cc_birth]. rewrite HN, HR.
  change (Z.min 24 32) with 24. change (Z.min 32 32) with 32.
  rewrite sublist_nil, app_nil_r, sublist_same by lia.
  rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia).
  rewrite sublist_sublist by lia. rewrite sublist_same by lia. auto.
Qed.

(* no rotation: the log starts with the nonce *)
Lemma hcy5_p5_a_rot0 x R L Q S nonce rr :
  birthdate_expired (r_birth R) (Int64.repr 120) (q_now Q) = false -> Zlength nonce = 24 ->
  sublist 0 24 (s_log (hcy5_S4shim S (hcy5_CC1 x R L) Q nonce rr)) = nonce /\
  cc_secret (hcy5_CC2 x R L Q rr) = r_secret R /\ cc_birth (hcy5_CC2 x R L Q rr) = r_birth R.
Proof.
  intros E HN. unfold hcy5_S4shim, hcy5_CC2, checker_rotate, checker_rotates.
  change (cc_birth (hcy5_CC1 x R L)) with (r_birth R). rewrite E.
  unfold shim_draw. cbn [s_log s_logprev]. rewrite HN.
  change (Z.min 24 32) with 24.
  rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia).
  rewrite sublist_sublist by lia. rewrite sublist_same by lia. auto.
Qed.

Lemma hcy5_p5_a_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p5_a_A1 {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S4 x25519 xaead_enc gv L FR) hcy5_p5_a_s36
    (overridePost (hcy5_p5_T1 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S4, hcy5_Delta, hcy5_R, hcy5_p5_a_s36. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q nonce rr CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
  assert (ECM := hcy5_p5_a_cm_eq _ _ _ _ _ _ _ _ _ _ H0 H1 H4).
  pose proof (hcy5_p5_a_cm_nonce _ _ _ _ _ _ _ _ ECM) as NCM.
  clear H4.
  forward_call (r_birth R, Int64.repr 120, q_now Q).
  rewrite hcy5_p5_a_cm_open, hcy5_p5_a_shim_open. Intros.
  remember (hcy5_S4shim S (hcy5_CC1 x25519 R L) Q nonce rr) as S' eqn:ES'.
  destruct (birthdate_expired (r_birth R) (Int64.repr 120) (q_now Q)) eqn:EXP.
  - destruct (hcy5_p5_a_rot1 x25519 R L Q S nonce rr EXP H2 H3) as (SL & SP & CS & CB). rewrite <- ES' in SL, SP. clear ES'.
    forward_if.
    + sep_apply (hcy5_p5_a_hbytes_out Tsh (r_secret R) (l_secret L)).
      replace (Zlength (r_secret R)) with (Zlength (s_log S')) by (rewrite SL; destruct H as (?&?&?&?&?&?); lia).
      forward_call (Tsh, l_secret L, Ews, gv _wg_shim_random_log, s_log S').
      { entailer!. rewrite H3. reflexivity. }
      { rewrite SL, H3. rep_lia. }
      forward.
      assert_PROP (@field_compatible HCS (tarray tuchar (Zlength (s_logprev S'))) [] (gv _wg_shim_random_log_prev)) as FCP.
      { sep_apply (hcy5_p5_a_hbytes_fc Ews (s_logprev S') (gv _wg_shim_random_log_prev)). entailer!. }
      pose proof H5 as (SH1 & SH2).
      rewrite (hcy5_p5_a_split Ews (s_logprev S') 24 (gv _wg_shim_random_log_prev)) by (auto; lia).
      flatten_sepcon_in_SEP.
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      { apply ENTAIL_refl. }
      { forward_call (Ews, offset_val 8 rp, cm_nonce CM, Ews, gv _wg_shim_random_log_prev, sublist 0 24 (s_logprev S')).
        { destruct rp; try (simpl in H30; contradiction); exact I. }
        { entailer!. rewrite H2. destruct rp; try (simpl in H30; contradiction). simpl. reflexivity. }
        { rewrite NCM, H2; rep_lia. }
        replace (bytes_eqb (cm_nonce CM) (sublist 0 24 (s_logprev S'))) with true
          by (rewrite NCM, SP; symmetry; apply hcy5_p5_a_eqb_refl).
        forward_if.
        { exfalso. exact (Int.one_not_zero H7). }
        forward. entailer!. }
      { forward. entailer!. }
      unfold POSTCONDITION, abbreviate.
      match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
      assert (RO: hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr (hcy5_CK x25519 R L Q m rr) CM)
        by exact (conj H (conj H0 (conj H2 (conj H3 (conj eq_refl ECM))))).
      unfold hcy5_p5_T1. Exists R S' m c rp. Exists Q nonce rr (hcy5_CK x25519 R L Q m rr) CM.
      unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
      rewrite hcy5_p5_a_cm_open, hcy5_p5_a_shim_open.
      rewrite (hcy5_p5_a_split Ews (s_logprev S') 24 (gv _wg_shim_random_log_prev)) by (auto; lia).
      rewrite CB, CS, SL.
      entailer!.
    + exfalso. exact (Int.one_not_zero H6).
  - destruct (hcy5_p5_a_rot0 x25519 R L Q S nonce rr EXP H2) as (SL & CS & CB). rewrite <- ES' in SL. clear ES'.
    forward_if.
    + exfalso. apply H6. reflexivity.
    + assert_PROP (@field_compatible HCS (tarray tuchar (Zlength (s_log S'))) [] (gv _wg_shim_random_log)) as FCP.
      { sep_apply (hcy5_p5_a_hbytes_fc Ews (s_log S') (gv _wg_shim_random_log)). entailer!. }
      pose proof H5 as (SH1 & SH2).
      rewrite (hcy5_p5_a_split Ews (s_log S') 24 (gv _wg_shim_random_log)) by (auto; lia).
      flatten_sepcon_in_SEP.
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      { apply ENTAIL_refl. }
      { forward_call (Ews, offset_val 8 rp, cm_nonce CM, Ews, gv _wg_shim_random_log, sublist 0 24 (s_log S')).
        { destruct rp; try (simpl in H30; contradiction); exact I. }
        { entailer!. rewrite H2. destruct rp; try (simpl in H30; contradiction). simpl. reflexivity. }
        { rewrite NCM, H2; rep_lia. }
        replace (bytes_eqb (cm_nonce CM) (sublist 0 24 (s_log S'))) with true
          by (rewrite NCM, SL; symmetry; apply hcy5_p5_a_eqb_refl).
        forward_if.
        { exfalso. exact (Int.one_not_zero H7). }
        forward. entailer!. }
      { forward. entailer!. }
      unfold POSTCONDITION, abbreviate.
      match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
      assert (RO: hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr (hcy5_CK x25519 R L Q m rr) CM)
        by exact (conj H (conj H0 (conj H2 (conj H3 (conj eq_refl ECM))))).
      unfold hcy5_p5_T1. Exists R S' m c rp. Exists Q nonce rr (hcy5_CK x25519 R L Q m rr) CM.
      unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
      rewrite hcy5_p5_a_cm_open, hcy5_p5_a_shim_open.
      rewrite (hcy5_p5_a_split Ews (s_log S') 24 (gv _wg_shim_random_log)) by (auto; lia).
      rewrite CB, CS.
      entailer!.
Qed.

Lemma hcy5_p5_a_A2 {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p5_T1 x25519 xaead_enc gv L FR)
    hcy5_p5_a_s37 (overridePost (hcy5_p5_T1 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p5_T1, hcy5_Delta, hcy5_R, hcy5_p5_a_s37. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp. Intros Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wb L)) as FCwb by (unfold hcy5_drest; entailer!).
  rewrite hcy5_p5_a_cc_open by exact FCwb. Intros. pose proof H0 as (L1 & L2 & L3).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if (temp HY._t'23 (Vint Int.one)).
    { forward_call (Tsh, cc_addr (l_wb L), cc_secret (hcy5_CC2 x25519 R L Q rr), Tsh, l_secret L,
                    cc_secret (hcy5_CC2 x25519 R L Q rr)).
      { entailer!. rewrite L1. destruct (l_wb L); try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
      rewrite hcy5_p5_a_eqb_refl. forward. entailer!. }
    { exfalso. match goal with Hf: ?x <> ?x |- _ => exact (Hf eq_refl) end. }
    forward_if. { exfalso. exact (Int.one_not_zero H1). } forward. entailer!. }
  { forward. entailer!. }
  unfold POSTCONDITION, abbreviate.
  match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
  unfold hcy5_p5_T1. Exists R S m c rp. Exists Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
  rewrite hcy5_p5_a_cc_open by exact FCwb. entailer!.
Qed.

Lemma hcy5_p5_A_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S4 x25519 xaead_enc gv L FR) hcy5_p5_A
    (overridePost (hcy5_p5_T1 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. rewrite hcy5_p5_a_eq. eapply semax_seq.
  - rewrite hcy5_overridePost2. apply hcy5_p5_a_A1; exact HH.
  - apply hcy5_p5_a_A2; exact HH.
Qed.

End Seg.
