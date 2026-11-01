(* law keypairs: segment LC of the loop body (CHECK(check_all(&p, &t, &w)); CHECK(wg_shim_frees - frees0 == m_frees)). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_segLC_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5_segLC_fold x25519 F V Y (A B: mpred) :
  fold_right_sepcon (hkp5_SEP x25519 F V Y (A * B)) = fold_right_sepcon (hkp5_SEP x25519 F V Y A) * B.
Proof.
  unfold hkp5_SEP. rewrite !app_assoc, !fold_right_sepcon_app. cbn [fold_right_sepcon].
  rewrite !sepcon_emp. symmetry. apply sepcon_assoc.
Qed.

Lemma hkp5_segLC_SEPx {A0: Type} x25519 F V Y (A B: mpred) :
  @SEPx A0 (hkp5_SEP x25519 F V Y (A * B)) = SEPx [fold_right_sepcon (hkp5_SEP x25519 F V Y A); B].
Proof.
  unfold SEPx. extensionality rho. rewrite hkp5_segLC_fold. cbn [fold_right_sepcon]. rewrite sepcon_emp.
  reflexivity.
Qed.

Lemma hkp5_segLC_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) FR i R :
  hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_LC x25519)) (hkp5_Icont x25519 F V steps (hkp5_othR x25519 F V O * FR) i) hkp5_segLC
    (loop1_ret_assert (hkp5_Icont x25519 F V steps (hkp5_othR x25519 F V O * FR) i) R).
Proof.
  intros HO.
  unfold hkp5_Icont, hkp5_St, hkp5_Delta, hkp5_segLC.
  Intros Y.
  abbreviate_semax.
  destruct R as [Rn Rb Rc Rr]. unfold POSTCONDITION, abbreviate. cbn [loop1_ret_assert]. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + rewrite hkp5_segLC_SEPx. unfold hkp5_temps, hkp5_lvars; cbn [app]. forward_call (F, V, Y, O).
    forward_if.
    { exfalso. exact (Int.one_not_zero H3). }
    forward. rewrite hkp5_segLC_SEPx. unfold hkp5_temps, hkp5_lvars; cbn [app]. entailer!.
  + forward. apply ENTAIL_refl.
  + pose proof H1 as Hinv. destruct H1 as (_ & _ & _ & _ & _ & Hfr & _).
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars; cbn [app].
    unfold shim_state4 at 1, shim_core at 1. Intros. rename H1 into HSok.
    rewrite (@hkp5_segLC_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_frees)).
    change _wg_shim_frees with KC._wg_shim_frees.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    * apply ENTAIL_refl.
    * forward. forward. forward_if.
      { forward_call tt. all: first [match goal with Hc: _ = Int.zero |- _ =>
          rewrite Hfr, Int64.eq_true in Hc; exact (Int.one_not_zero Hc) end | entailer!]. }
      forward. entailer!.
    * forward. apply ENTAIL_refl.
    * rewrite (@hkp5_segLC_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_frees)).
      change KC._wg_shim_frees with _wg_shim_frees.
      unfold POSTCONDITION, abbreviate. cbn [RA_normal].
      Exists Y.
      unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars; cbn [app].
      unfold shim_state4, shim_core. entailer!.
Qed.
