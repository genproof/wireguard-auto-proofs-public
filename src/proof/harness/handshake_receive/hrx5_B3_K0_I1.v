(* law handshake_receive, phase B3, branch kind 0, segment I1:
   the initiation block of stmt 6 (guard nk <> NULL, len > 148 given by hrx5_K0_M1): fill_init(&t); k_initiation(&t, &ik, &id, ss_k); t.header.type = 1; init_img(buf, &t) (buf's bytes split at 148; t back to data_at_).
   States and statements: hrx5_B3_K0_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Local Open Scope logic.

#[local] Instance hrx5_ki1_cce : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_ki1_init_cs sh (a b: val) (c d e f g: list val) p :
  @data_at Noise.CS sh t_init (a, (b, (c, (d, (e, (f, g)))))) p =
  @data_at W_handshake_receive sh t_init (a, (b, (c, (d, (e, (f, g)))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Noise.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_ki1_hbytes sh bs p : bytes_at sh bs p = hbytes sh bs p.
Proof. unfold bytes_at, hbytes. apply data_at_tarray_tuchar_cs. Qed.

Lemma hrx5_ki1_fc (B: list byte) (dp: val) : 0 <= Zlength B -> malloc_compatible (Zlength B) dp ->
  @field_compatible Noise.CS (tarray tuchar (Zlength B)) [] dp.
Proof.
  intros N MC. apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
  replace (@sizeof Noise.CS (tarray tuchar (Zlength B))) with (Zlength B) by (simpl; lia). exact MC.
Qed.

Lemma hrx5_ki1_eqB (B: list byte) : 148 <= Zlength B ->
  B = sublist 0 148 B ++ sublist 148 (Zlength B) B.
Proof. intros. rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. Qed.

Lemma hrx5_ki1_split (B: list byte) (dp: val) : 148 <= Zlength B -> malloc_compatible (Zlength B) dp ->
  bytes_at Ews B dp |-- hout Ews 148 dp * bytes_at Ews (sublist 148 (Zlength B) B) (offset_val 148 dp).
Proof.
  intros N MC. pose proof (hrx5_ki1_fc B dp ltac:(lia) MC) as FC.
  rewrite (hrx5_ki1_eqB B N) at 1. rewrite prot_rep3_bytes_app.
  2: { rewrite <- Zlength_app, <- hrx5_ki1_eqB by lia. exact FC. }
  rewrite Zlength_sublist by lia. replace (148 - 0) with 148 by lia. cancel.
  unfold bytes_at, hout. rewrite Zlength_sublist by lia. replace (148 - 0) with 148 by lia.
  rewrite (@data_at__tarray_tuchar_cs HCS Noise.CS). apply data_at_data_at_.
Qed.

Lemma hrx5_ki1_join (B X: list byte) (dp: val) : Zlength X = 148 -> 148 <= Zlength B -> malloc_compatible (Zlength B) dp ->
  hbytes Ews X dp * bytes_at Ews (sublist 148 (Zlength B) B) (offset_val 148 dp) |--
  bytes_at Ews (X ++ sublist 148 (Zlength B) B) dp.
Proof.
  intros LX N MC. pose proof (hrx5_ki1_fc B dp ltac:(lia) MC) as FC.
  rewrite prot_rep3_bytes_app.
  2: { rewrite Zlength_sublist, LX by lia. replace (148 + (Zlength B - 148)) with (Zlength B) by lia. exact FC. }
  rewrite LX. cancel. rewrite hrx5_ki1_hbytes. apply derives_refl.
Qed.

Section K0I1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K0_I1_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M1 x25519 gv L FR) hrx5_K0_I1
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K0_M1, hrx5_K0_Mc. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port B dp.
  unfold hrx5_K0_I1, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  forward_call (Tsh, l_t L). Intros M0.
  assert (HX: x25519_props x25519) by (destruct HY; auto).
  assert (HRK: hrx5_run_ok R) by (destruct H; auto).
  assert (LK1: Zlength (mi_priv (hrx5_IK x25519 R)) = 32).
  { unfold hrx5_IK, mident_of, clamp; simpl. destruct HRK. rewrite !Zlength_upd_Znth; auto. }
  assert (LK2: Zlength (mi_pub (hrx5_IK x25519 R)) = 32) by (apply HX).
  assert (LD1: Zlength (mi_priv (hrx5_ID x25519 R)) = 32).
  { unfold hrx5_ID, mident_of, clamp; simpl. destruct HRK. rewrite !Zlength_upd_Znth; auto. }
  assert (LD2: Zlength (mi_pub (hrx5_ID x25519 R)) = 32) by (apply HX).
  assert (LS: Zlength (hrx5_ssk x25519 R) = 32).
  { unfold hrx5_ssk, m_precomputed_model.
    match goal with |- context [if ?b then _ else _] => destruct b end; [apply HX | reflexivity]. }
  forward_call (gv, S, w, Tsh, l_t L, M0, Tsh, l_ik L, hrx5_IK x25519 R, l_id L, hrx5_ID x25519 R, Tsh,
                l_ssk L, hrx5_ssk x25519 R).
  Intros vret. destruct vret as [[M1 sec1] ns]. cbn [fst snd] in *.
  unfold init_rep at 1. Intros. unfold init_val. rewrite hrx5_ki1_init_cs.
  forward.
  set (M2 := mkIM (Int.repr 1) (im_sender M1) (im_eph M1) (im_encs M1) (im_enct M1) (im_mac1 M1) (im_mac2 M1)).
  assert (OK2: im_ok M2) by exact H8.
  assert (LM2: Zlength (init_bytes M2) = 148).
  { destruct OK2 as (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4, L5. reflexivity. }
  replace_SEP 0 (init_rep Tsh (l_t L) M2).
  { unfold init_rep, init_val. subst M2; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
    rewrite hrx5_ki1_init_cs. entailer!. }
  unfold obj_rep. sep_apply (hrx5_ki1_split B dp ltac:(lia) H4).
  forward_call (Ews, dp, Tsh, l_t L, M2). { cancel. }
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K0_M x25519 gv L FR) end.
  set (B' := init_bytes M2 ++ sublist 148 (Zlength B) B).
  assert (LB: Zlength B' = Zlength B).
  { subst B'. rewrite Zlength_app, LM2, Zlength_sublist by lia. lia. }
  assert (OKB: obj_ok (OBuf B')) by (unfold obj_ok in *; rewrite LB; exact H3).
  assert (MCB: malloc_compatible (Zlength B') dp) by (rewrite LB; exact H4).
  assert (HB: hrx5_base_ok R sec birth (shim_set_real S sec1 (Int64.repr ns))) by (apply HLEM; exact H).
  sep_apply (hrx5_ki1_join B (init_bytes M2) dp LM2 ltac:(lia) H4). fold B'.
  unfold hrx5_K0_M, hrx5_K0_Mc.
  Exists R sec birth (shim_set_real S sec1 (Int64.repr ns)) w NS PS T.
  Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port B' dp.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  change (s_boot (shim_set_real S sec1 (Int64.repr ns))) with (s_boot S).
  unfold obj_rep. rewrite LB. unfold init_rep. Intros.
  sep_apply (data_at_data_at_ Tsh t_init (init_val M2) (l_t L)).
  go_lower. apply andp_right.
  { apply prop_right. refine (conj HB (conj H0 (conj H1 (conj H2 (conj OKB (conj H4 (conj I _))))))).
    repeat split; auto. }
  cancel.
Qed.

End K0I1.
