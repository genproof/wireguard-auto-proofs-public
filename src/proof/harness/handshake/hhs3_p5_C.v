(* law handshake, phase P5, segment C.
*)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p5_C_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hhs3_p5_C_resp_len M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (L1 & L2 & L3 & L4). unfold resp_bytes.
  rewrite !Zlength_app, !hhs3_p5_C_le32_len, L1, L2, L3, L4. reflexivity.
Qed.

Lemma hhs3_p5_C_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hhs3_p5_C_hout sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Section P5C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_C_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p5_SB x25519 aead_enc aead_dec gv L FR) hhs3_p5_C
    (overridePost (hhs3_p5_SC x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p5_SB, hhs3_p5_SBC, hhs3_Delta, hhs3_R, hhs3_p5_C. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb PA1 CI1 CI2 Q M2 H2 MR. Intros nowa Cre acc ST2.
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  assert_PROP (rm_ok (hhs3_M2m x25519 R M2)) as HM2. { unfold resp_rep. Intros. entailer!. }
  pose proof (hhs3_p5_C_resp_len _ HM2) as HL2.
  (* resp_img(rimg_before, m2) *)
  forward_call (Tsh, l_rimgb L, Ews, m2, hhs3_M2m x25519 R M2).
  (* CHECK(bytes_eq(rimg, rimg_before, RESP_LEN)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  + apply ENTAIL_refl.
  + forward_call (Tsh, l_rimg L, resp_bytes (hhs3_M2m x25519 R M2), Tsh, l_rimgb L, resp_bytes (hhs3_M2m x25519 R M2)).
    { rewrite HL2. entailer!. }
    rewrite hhs3_p5_C_eqb_refl.
    forward_if.
    * discriminate.
    * forward. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hhs3_p5_SC, hhs3_p5_SBC.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb PA1 CI1 CI2 Q M2 H2 MR. Exists nowa Cre acc ST2.
    unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
    sep_apply (hhs3_p5_C_hout Tsh (resp_bytes (hhs3_M2m x25519 R M2)) (l_rimgb L)).
    sep_apply (hhs3_p5_C_hout Tsh (resp_bytes (hhs3_M2m x25519 R M2)) (l_rimg L)). rewrite HL2.
    entailer!.
Qed.

End P5C.
