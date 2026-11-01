(* law handshake, phase P3, segment C.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p3_C_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hhs3_p3_C_init_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
  rewrite !Zlength_app, !hhs3_p3_C_le32_len, L1, L2, L3, L4, L5. reflexivity.
Qed.

Lemma hhs3_p3_C_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hhs3_p3_C_hout sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Section P3C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_C_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p3_SB x25519 aead_enc aead_dec gv L FR) hhs3_p3_C
    (overridePost (hhs3_p3_SC x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p3_SB, hhs3_p3_SBC, hhs3_Delta, hhs3_R, hhs3_p3_C. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb Cin acc CI1 CI2.
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  assert_PROP (im_ok (hhs3_M1m x25519 R M1)) as HM1. { unfold init_rep. Intros. entailer!. }
  pose proof (hhs3_p3_C_init_len _ HM1) as HL1.
  (* all_ok = all_ok && now_b >= 20000000 *)
  forward_if (temp HC._t'71 (Vint (if hhs3_p3_ok25 x25519 R I nowb then Int.one else Int.zero))).
  - forward. entailer!.
    unfold hhs3_p3_ok25. destruct (hhs3_ok2 x25519 R I); [| contradiction H8; reflexivity]. simpl.
    destruct (Int64.ltu (s_boot S) (Int64.repr 20000000)); reflexivity.
  - forward. entailer!.
    unfold hhs3_p3_ok25. destruct (hhs3_ok2 x25519 R I); [discriminate |]. reflexivity.
  - forward.
    (* init_img(img_before, m1) *)
    forward_call (Tsh, l_imgb L, Ews, m1, hhs3_M1m x25519 R M1).
    (* CHECK(bytes_eq(img, img_before, INIT_LEN)) *)
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    + apply ENTAIL_refl.
    + forward_call (Tsh, l_img L, init_bytes (hhs3_M1m x25519 R M1), Tsh, l_imgb L, init_bytes (hhs3_M1m x25519 R M1)).
      { rewrite HL1. entailer!. }
      rewrite hhs3_p3_C_eqb_refl.
      forward_if.
      * discriminate.
      * forward. entailer!.
    + forward. apply ENTAIL_refl.
    + unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hhs3_p3_SC, hhs3_p3_SBC.
      Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI (s_boot S) Cin acc CI1 CI2.
      unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
      sep_apply (hhs3_p3_C_hout Tsh (init_bytes (hhs3_M1m x25519 R M1)) (l_imgb L)). rewrite HL1.
      entailer!.
Qed.

End P3C.
