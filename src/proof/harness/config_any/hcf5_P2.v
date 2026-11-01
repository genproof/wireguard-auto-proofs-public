(* law config_any: main's phase P2, statements 32..34: step 2: wg_noise_precompute_static_static(&p), m_precomputed(dh, &id, pub), bytes_copy(hs0.precomputed_static_static, dh, 32).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require Import WgNoise.proof.harness.config_any.hcf5_p2_lem.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

Section P2.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P2_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_P2
    (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HX. unfold hcf5_SX1, hcf5_F, hcf5_Fx.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW.
  unfold hcf5_P2.
  pose proof H as [HRAW [ID0 [HID0 HDID]]].
  pose proof H0 as (Hrun & Hboot & Hw & Hdok & Hpok & Hslots & HTok & Hks).
  unfold hcf5_core, hcf5_globs, hcf5_X1. cbn [app].
  rewrite hcf5_p2_peer_split, hcf5_p2_dev_split.
  assert (Hsid: hs_sid (p_hs P) = id_addr (l_w L)) by apply Hpok.
  rewrite <- Hsid.
  repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_p L)) as Hfcp by (go_lowerx; unfold hcf5_p2_prest; normalize).
  eapply semax_seq'; [prove_call_setup (@nil Type) funspec_sub_refl (gv, Tsh, l_p L, p_hs P, Tsh, d_id D) | ].
  { apply prop_right. reflexivity. }
  { clear_Delta_specs; clear_MORE_POST.
    forward_call_id00_wow.
  }
  apply extract_exists_pre; intros _. cbn [app].
  assert (Hrs: hs_rstatic (p_hs P) = r_pub R) by apply Hpok.
  pose proof Hrun as (_ & _ & _ & Hpub).
  set (A := m_precomputed_model x25519 (mident_of x25519 RAW) (r_pub R)).
  assert (Hss: precomputed x25519 (d_id D) (hs_rstatic (p_hs P)) = A)
    by (rewrite HDID, Hrs; apply hcf5_p2_pre).
  assert (HlenA: Zlength A = 32) by (apply hcf5_p2_mpre_len; exact HX).
  assert (Hcl: Zlength (mi_priv (mident_of x25519 RAW)) = 32) by (apply hcf5_p2_clamp_len; exact HRAW).
  rewrite Hss.
  (* m_precomputed(dh, &id, pub) *)
  eapply semax_seq'; [prove_call_setup (@nil Type) funspec_sub_refl
    (Tsh, l_dh L, Tsh, l_id L, mident_of x25519 RAW, Tsh, l_pub L, r_pub R) | ].
  { apply prop_right. reflexivity. }
  { clear_Delta_specs; clear_MORE_POST.
    forward_call_id00_wow.
  }
  apply extract_exists_pre; intros _. cbn [app].
  (* bytes_copy(hs0.precomputed_static_static, dh, 32) *)
  assert_PROP (@field_compatible HCS t_hsnap [] (l_hs0 L)) as Hfch
    by (go_lowerx; saturate_local; apply prop_right; assumption).
  pose proof (hcf5_p2_hs0 Tsh sn0 (l_hs0 L) A) as Hx.
  match type of Hx with _ |-- ?r => replace_SEP 12 r end.
  { go_lowerx. rewrite sepcon_emp. apply Hx. }
  clear Hx.
  set (fa := @field_address HCS t_hsnap (DOT HF._precomputed_static_static) (l_hs0 L)).
  replace (@data_at_ HCS Tsh (tarray tuchar 32) fa) with (hout Tsh (Zlength A) fa) by (rewrite HlenA; reflexivity).
  change (m_precomputed_model x25519 (mident_of x25519 RAW) (r_pub R)) with A.
  flatten_sepcon_in_SEP.
  rewrite semax_seq_skip.
  eapply semax_seq'; [prove_call_setup (@nil Type) funspec_sub_refl (Tsh, fa, Tsh, l_dh L, A) | ].
  { apply prop_right. rewrite HlenA. unfold fa, field_address.
    rewrite if_true by (apply field_compatible_cons; split; auto; cbv; tauto).
    destruct (l_hs0 L) eqn:E; try (destruct Hfch; contradiction). reflexivity. }
  { clear_Delta_specs; clear_MORE_POST.
    forward_call_id00_wow.
  }
  apply extract_exists_pre; intros _. cbn [app].
  replace (hbytes Tsh A fa) with (@data_at HCS Tsh (tarray tuchar 32) (bytes A) fa)
    by (unfold hbytes; rewrite HlenA; reflexivity).
  gather_SEP 0 13.
  replace_SEP 0 (@data_at HCS Tsh t_hsnap (hsnap_val (hcf5_p2_snss sn0 A)) (l_hs0 L)).
  { go_lowerx. rewrite sepcon_emp, sepcon_comm. apply wand_sepcon_adjoint; apply derives_refl. }
  gather_SEP 4 10.
  rewrite hcf5_p2_peer_join.
  gather_SEP 5 7.
  rewrite Hsid, <- hcf5_p2_dev_split.
  replace_SEP 3 (hout Tsh 32 (l_dh L)).
  { go_lowerx. rewrite sepcon_emp. unfold hbytes, hout. rewrite HlenA. apply data_at_data_at_. }
  apply hcf5_p2_skip.
  Exists R S w D. Exists (p_set_hs P (hs_set_ss (p_hs P) A)) T KE D0.
  Exists (hcf5_p2_snss sn0 A) P0 r0 S0. Exists w0 h0 RAW.
  apply andp_right.
  { apply prop_right. split; [exact H |]. split; [apply (hcf5_p2_inv x25519); exact H0 |].
    split; [exact (hcf5_p2_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 A H1) | exact I]. }
  apply andp_left2. unfold PROPx at 1. apply andp_left2. unfold LOCALx.
  apply andp_derives; [apply derives_refl |]. intro rho. unfold SEPx. cbv beta. cbn [fold_right_sepcon].
  cancel.
Qed.

End P2.
