(* law cookie_reply: phase P11 of main, statements
   66..69: the harness's model: target = NULL, the walk of ita, the cnode search, the decryption CHECK.

   (+ its children's files). *)
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
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_A.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_B.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_C.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P11_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S10 x25519 xaead_enc xaead_dec gv L FR) hcy5_P11
    (overridePost (hcy5_S11 x25519 xaead_enc xaead_dec gv L FR) (hcy5_R gv)).
Proof.
  intros HH. rewrite hcy5_p11_eq.
  eapply hcy5_semax_cut; [cbv; discriminate | rewrite <- hcy5_p11_eqA; apply hcy5_p11_A_ok; exact HH |].
  eapply semax_seq.
  - rewrite hcy5_overridePost2. apply hcy5_p11_B_ok; exact HH.
  - apply hcy5_p11_C_ok; exact HH.
Qed.

End Phase.
