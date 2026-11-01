(* law handshake: main's phase P1, segment B = statements 10..13: setup_device x2, m_identity_of x2.
   (section P1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p1_B_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p1_SA gv L FR) hhs3_p1_B
    (overridePost (hhs3_p1_SB x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p1_SA, hhs3_Delta, hhs3_R, hhs3_p1_B. simplify_func_tycontext. abbreviate_semax.
  Intros rawa rawb psk up S a0 f0 l0.
  unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
  forward_call (gv, S, Tsh, l_wa L, l_ita L, l_pta L, Tsh, l_rawa L, rawa).
  Intros seca.
  forward_call (gv, shim_draw S seca, Tsh, l_wb L, l_itb L, l_ptb L, Tsh, l_rawb L, rawb).
  Intros secb.
  change (s_boot (shim_draw S seca)) with (s_boot S).
  unfold hhs3_consts. repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_ia L, Tsh, l_rawa L, rawa).
  forward_call (gv, Tsh, l_ib L, Tsh, l_rawb L, rawb).
  unfold hhs3_p1_SB.
  Exists (mkRun rawa rawb up psk seca secb (s_boot S)) (shim_draw (shim_draw S seca) secb) a0 f0 l0.
  unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp, hhs3_consts;
    cbn [app r_rawa r_rawb r_up r_psk r_seca r_secb r_boot0].
  unfold hhs3_DA, hhs3_DB, hhs3_IA, hhs3_IB; cbn [r_rawa r_rawb r_up r_psk r_seca r_secb r_boot0].
  entailer!.
  destruct H4 as (? & ? & ?).
  unfold hhs3_run_ok, hhs3_cnt; cbn [r_rawa r_rawb r_up r_psk r_seca r_secb r_boot0 shim_draw
    s_allocs s_frees s_fails]; repeat split; auto; lia.
Qed.

End Seg.
