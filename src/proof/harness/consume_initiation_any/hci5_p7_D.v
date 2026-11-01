(* law consume_initiation_any, phase P7, segment D: if (p != NULL) x else skip (x given as a hypothesis).  Port of v1's hci3_p7_D.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p7_D_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M s key ck1 h1 :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
  (forall a P, pk_find PS s = Some (a, P) ->
     semax (hci5_Delta x25519 aead_enc aead_dec)
       (hci5_p7_Qf x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a) hci5_p7_x
       (overridePost (hci5_S7 x25519 aead_dec gv L FR) (hci5_R gv))) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Qb x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1) hci5_p7_ifp
    (overridePost (hci5_S7 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH Hc1 HX.
  destruct (hci5_p7_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  unfold hci5_p7_Qb, hci5_p7_st, hci5_p7_ifp, hci5_p7_ci1, hci5_lvars, hci5_world, hci5_globs. cbn [app].
  Intros.
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H1)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  pose proof (hci5_p7_pure_nodup PS KE T Hwf (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H0))))))) as Hnd.
  destruct (hci5_p7_after_ok x25519 aead_dec R L NS PS KE T head na (hci5_DB x25519 R L) M S H0 Hnd)
    as (Hpe & Hsh & Hnone & Hsome).
  destruct (pk_find PS s) as [[a P]|] eqn:Hpk.
  2: {
    rewrite (Hnone s Hpk). cbn [hci5_p7_fmv].
    unfold hci5_Delta. simplify_func_tycontext.
    forward_if. 1: { hci5_p7_absurd. }
    forward.
    sep_apply (@data_at_data_at_ HCS Tsh t_mcinit (mcinit_val ck1 h1 (bytes key) (bytes s) (Zrepeat Vundef 12)) (l_ci L)).
    unfold hci5_S7. Exists R S w NS PS T head na KE m M.
    rewrite (hci5_p7_tgt_none2 x25519 aead_dec _ _ _ _ _ _ _ _ Hc1 Hpk).
    unfold hci5_lvars, hci5_world, hci5_globs. cbn [hci5_tnode hci5_ci_rep app].
    entailer!. }
  destruct (Hsome s a P Hpk) as (NS1 & N & NS2 & P' & sn & Hfm & HNS & HinP & Hnf & HpN & Hrs & Hsn & Hsnhs & HokP & Hlic).
  rewrite Hfm. cbn [hci5_p7_fmv].
  assert (HinN: In (hn_addr N) (map hn_addr (hnodes_snapped4 T NS PS))).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  pose proof (hci5_p7_hn_valid (hci5_head NS) (hnodes_snapped4 T NS PS) (hn_addr N) HinN) as HvN.
  assert_PROP (Forall isptr (map hn_addr (hnodes_snapped4 T NS PS))) as Hptrs.
  { sep_apply (hci5_p7_hn_isptr (hci5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
  assert (HpNa: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
  specialize (HX a P eq_refl).
  eapply semax_pre; [ | apply semax_ifthenelse_PQR' with (v := Vint Int.one)].
  - apply andp_left2, now_later.
  - reflexivity.
  - entailer!.
  - entailer!. destruct (hn_addr N); try contradiction. reflexivity.
  - eapply semax_pre; [ | exact HX ].
    unfold hci5_p7_Qf, hci5_p7_st, hci5_p7_ci1, hci5_lvars, hci5_world, hci5_globs. cbn [app].
    rewrite <- Hnf. Intros. entailer!.
  - Intros. hci5_p7_absurd.
Qed.

End Seg.
