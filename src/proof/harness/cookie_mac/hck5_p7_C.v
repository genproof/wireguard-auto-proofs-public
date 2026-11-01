(* law cookie_mac, phase P7, segment C: s85 = CHECK(secret_birthdate == secret_birth && bytes_eq(secret)) (v1 hck3_p7_C.v.old).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_lemmas.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Section P7C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_C_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_T2 x25519 gv L FR) hck5_p7_s85
    (overridePost (hck5_T2 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_T2, hck5_Delta, hck5_R, hck5_p7_s85. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C. Intros ck MSG1 C1 MSG2 corrupted. Intros chk rl r VR.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wb L)) as FCwb by (unfold hck5_drest; entailer!).
  rewrite hck5_p7_cc_open by exact FCwb. Intros. match goal with Hc: cc_ok (snd VR) |- _ => pose proof Hc as (L1 & L2 & L3) end.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { entailer!. }
  { forward. forward_if (temp HK._t'74 (Vint Int.one)).
    { forward_call (Tsh, cc_addr (l_wb L), cc_secret (snd VR), Tsh, l_secret L, cc_secret (snd VR)).
      { entailer!. rewrite L1. destruct (l_wb L); try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
      rewrite hck5_p7_eqb_refl. forward. entailer!. }
    { exfalso. auto. }
    forward_if. { exfalso. match goal with H: _ = Int.zero |- _ => revert H end. simpl. intro X; inversion X. }
    forward. entailer!. }
  { forward. entailer!. }
  unfold POSTCONDITION, abbreviate.
  match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
  unfold hck5_T2. Exists R S A m c. Exists Q cmode C ck MSG1. Exists C1 MSG2 corrupted chk. Exists rl r VR.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  rewrite hck5_p7_cc_open by exact FCwb. entailer!.
Qed.

End P7C.
