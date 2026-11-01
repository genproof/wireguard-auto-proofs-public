(* law cookie_reply, phase P12, segment X, the branch target == NULL: CHECK(hnodes_same_except(peers, NULL)) (v1: hcy4_p12_H.v).
   St -> St over fixed values (hcy5_p12_defs.v). *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_null_pure.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_x_null_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2) = nullval ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)
    hcy5_p12_x_sN
    (normal_ret_assert (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)).
Proof.
  intros HH Hinv Ht.
  destruct Hinv as (Hrep & Hlists & Hnp & HT & Hcln & Hcls & Hcm & Hhon & Hnow).
  unfold hcy5_p12_St, hcy5_Delta. simplify_func_tycontext.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  assert_PROP (Forall (fun x => isptr (fst (fst x))) CL) as Hcp.
  { sep_apply (hcy5_p12_x_null_cns_ptr (hcy5_chead CL) CL). entailer!. }
  rewrite (hcy5_p12_x_null_res xaead_dec L _ NS PS CL T CM' now2 Hlists Hcln Hcp Ht).
  change (peers_after PS None) with PS. change (hcy5_tgt NS CL None) with nullval.
  abbreviate_semax.
  unfold hcy5_p12_x_sN.
  assert_PROP (itable_wf T) as HwfT by (unfold itable at 1; entailer!).
  destruct (hcy5_p12_x_null_facts x25519 R L NS PS KE T Hlists HT HwfT)
    as (Hq0 & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9 & Hsame).
  assert_PROP (is_pointer_or_null (hcy5_head (hnodes_snapped4 T NS PS))) as Hhd.
  { sep_apply (hcy5_p12_x_null_hn_pn (hcy5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (hcy5_p12_x_null_vo Tsh (l_wa L) (hcy5_DA x25519 R L) (hcy5_khead KE) (map (kent_snapped T) KE)).
    forward_call (hcy5_head (hnodes_snapped4 T NS PS), hnodes_snapped4 T NS PS, PS,
                  hcy5_p12_x_null_sns T PS, hcy5_p12_x_null_rs PS, hcy5_p12_x_null_prs PS, nullval, Tsh, l_ita L, T,
                  hcy5_p12_x_null_VO x25519 R L T KE).
    rewrite Hsame.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. unfold hcy5_p12_x_null_VO. rewrite <- hcy5_p12_x_null_vo. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. apply ENTAIL_refl.
Qed.

End Seg.
