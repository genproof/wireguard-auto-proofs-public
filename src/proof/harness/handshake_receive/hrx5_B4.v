(* law handshake_receive: main's phase B4 = body statements 21..25: tw, fwd, hnodes_snap, kents_snap, the model block (target, acc_init, acc_resp).
   From hrx5_S3 to hrx5_S4 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_A.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_Z.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section B4.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B4_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S3 x25519 gv L FR) hrx5_B4
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HY.
  destruct hrx5_bphases_eq as (_ & _ & _ & E4 & _). rewrite E4, hrx5_B4_split. clear E4.
  apply hrx5_seql_app with (Q := hrx5_B4_S3b x25519 gv L FR); [discriminate | discriminate | |].
  - rewrite hrx5_overridePost2, <- hrx5_B4_A_eq. apply (hrx5_B4_A_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HY).
  - rewrite <- hrx5_B4_M_eq. unfold hrx5_B4_S3b.
    Intros R sec birth S w NS PS T. Intros head nk KE st i kc lul q. Intros proto ip4 ip6 port o dp img.
    destruct o as [b | M | M | M].
    + apply (hrx5_B4_Z_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE
               st i kc lul q proto ip4 ip6 port (OBuf b) dp img HY I).
    + apply (hrx5_B4_I_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE
               st i kc lul q proto ip4 ip6 port (OInit M) dp img HY I).
    + apply (hrx5_B4_R_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE
               st i kc lul q proto ip4 ip6 port (OResp M) dp img HY I).
    + apply (hrx5_B4_C_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE
               st i kc lul q proto ip4 ip6 port (OCookie M) dp img HY I).
Qed.

End B4.
