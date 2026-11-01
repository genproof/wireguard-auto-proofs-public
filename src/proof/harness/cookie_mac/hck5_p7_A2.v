(* law cookie_mac, phase P7, segment A2 (statement 83, T1 -> T2) from its parts (as v1's
   hck3_p7_A2.v). *)
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
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_A2_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_A2_outer.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_A2_rot.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_A2_cookmac.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_A2_tail.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Section P7A2.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_A2_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_T1 x25519 gv L FR) hck5_p7_s83
    (overridePost (hck5_T2 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. apply hck5_p7_A2_outer_ok; [exact HH |].
  rewrite hck5_p7_A2_inner_eq.
  eapply semax_seq; [apply hck5_p7_A2_rot_ok; exact HH |].
  apply seq_assoc.
  eapply semax_seq; [apply hck5_p7_A2_cookmac_ok; exact HH |].
  apply hck5_p7_A2_tail_ok; exact HH.
Qed.

End P7A2.
