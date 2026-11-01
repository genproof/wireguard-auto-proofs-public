(* law handshake_receive, phase B3, branch kind 3, segment F:
   stmt 4 (fill_cookie_msg(mc)): hrx5_K3_A -> hrx5_K3_F.
*)
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
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Local Open Scope logic.

#[local] Instance hrx5_k3f_cce : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.
Lemma hrx5_k3f_conv_cmsg sh p : @data_at_ Cookie.CS sh t_cmsg p = @data_at_ W sh t_cmsg p.
Proof. rewrite (@data_at__change_composite Cookie.CS W _ sh t_cmsg); [reflexivity | prove_cs_preserve_type]. Qed.

Section K3F.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3_F_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K3_A x25519 gv L FR) hrx5_K3_SF
    (overridePost (hrx5_K3_F x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K3_A, hrx5_K3_St.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto. Intros ip4 ip6 port mc img M.
  unfold hrx5_K3_SF, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XA; cbn [app].
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  repeat flatten_sepcon_in_SEP.
  replace (@data_at_ W Ews t_cmsg mc) with (@data_at_ Cookie.CS Ews t_cmsg mc) by (apply hrx5_k3f_conv_cmsg).
  forward_call (Ews, mc). Intros M'.
  unfold hrx5_K3_F, hrx5_K3_St.
  Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto.
  Exists ip4 ip6 port mc img M'.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XF; cbn [app].
  entailer!.
Qed.

End K3F.
