(* law cookie_reply: segment B of phase P5 (statements 38..40: m_cookie, k (m_label_key or bytes_set), the CHECK of the cookie key).  hcy5_p5_T1 -> hcy5_p5_T2.
*)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p5_b_lemmas.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p5_B_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p5_T1 x25519 xaead_enc gv L FR) hcy5_p5_B
    (overridePost (hcy5_p5_T2 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p5_T1, hcy5_Delta, hcy5_R, hcy5_p5_B. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp. Intros Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
  pose proof H as (HR & HQ & HN & Hrr & HCK & HCM).
  assert (LS := hcy5_p5_b_secret_len x25519 R L Q rr HR Hrr).
  unfold wg_consts. Intros.
  forward_call (gv, Tsh, l_cookie L, Tsh, l_secret L, cc_secret (hcy5_CC2 x25519 R L Q rr), Tsh, l_skb L, hcy5_skb Q m).
  rewrite hcy5_p5_b_mident_W. forward. rewrite <- hcy5_p5_b_mident_W.
  change (let (_, y) := let (_, y) := mident_val (hcy5_IB x25519 R) in y in y)
    with (Vint (if mi_ok (hcy5_IB x25519 R) then Int.one else Int.zero)).
  assert (EK := hcy5_p5_b_ekey_model x25519 R L).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    let F := eval pattern (hout Tsh 32 (l_k L)) in Sp in
    match F with ?f _ =>
      let Sp2 := eval cbv beta in (f (hbytes Tsh (cc_ekey (hcy5_CC1 x25519 R L)) (l_k L))) in
      forward_if (PROPx P (LOCALx Lc (SEPx Sp2))) end end.
  - assert (Eok: mi_ok (hcy5_IB x25519 R) = true).
    { change (mi_ok (hcy5_IB x25519 R)) with
        (memneq_bool (r_rawb R) zeros32 && memneq_bool (x25519 (r_rawb R) basepoint9) zeros32)%bool.
      destruct (_ && _)%bool; [reflexivity | contradiction H0; reflexivity]. }
    rewrite Eok in EK.
    unfold hcy5_drest. Intros.
    rewrite (hcy5_p5_b_id_open Tsh (id_addr (l_wb L))). Intros.
    rewrite (hcy5_p5_b_ers_split (id_pub (d_id (hcy5_DB x25519 R L)))). Intros.
    unfold hcy5_consts. Intros.
    change (hc_const gv HY._x_cookie_reply__M_LABEL_COOKIE cookie_label)
      with (hbytes Ers cookie_label (gv HY._x_cookie_reply__M_LABEL_COOKIE)).
    forward_call (gv, Tsh, l_k L, Ers, gv HY._x_cookie_reply__M_LABEL_COOKIE, cookie_label, id_addr (l_wb L),
                  id_pub (d_id (hcy5_DB x25519 R L))).
    { apply H2. }
    rewrite EK. change (hcy5_pubB x25519 R L) with (id_pub (d_id (hcy5_DB x25519 R L))).
    sep_apply (derives_refl' _ _ (eq_sym (hcy5_p5_b_ers_split (id_pub (d_id (hcy5_DB x25519 R L))) (id_addr (l_wb L))))).
    unfold hcy5_drest, hcy5_consts. rewrite (hcy5_p5_b_id_open Tsh (id_addr (l_wb L))).
    change (hc_const gv HY._x_cookie_reply__M_LABEL_COOKIE cookie_label)
      with (hbytes Ers cookie_label (gv HY._x_cookie_reply__M_LABEL_COOKIE)).
    entailer!.
  - assert (Eok: mi_ok (hcy5_IB x25519 R) = false).
    { change (mi_ok (hcy5_IB x25519 R)) with
        (memneq_bool (r_rawb R) zeros32 && memneq_bool (x25519 (r_rawb R) basepoint9) zeros32)%bool.
      destruct (_ && _)%bool; [exfalso; exact (Int.one_not_zero H0) | reflexivity]. }
    rewrite Eok in EK.
    forward_call (Tsh, l_k L, Byte.zero, 32).
    rewrite EK. entailer!.
  - rewrite (hcy5_p5_b_cc_open Tsh (cc_addr (l_wb L))). Intros.
    pose proof H0 as (L1 & L2 & L3).
    assert (EE := hcy5_p5_b_ekey x25519 R L Q rr).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_call (Tsh, offset_val 32 (cc_addr (l_wb L)), cc_ekey (hcy5_CC2 x25519 R L Q rr), Tsh, l_k L,
                    cc_ekey (hcy5_CC1 x25519 R L)).
      { entailer!. rewrite L2. unfold cc_addr, OFS_DEV_CHECKER. destruct (l_wb L); try contradiction.
        simpl. rewrite Ptrofs.add_assoc. reflexivity. }
      replace (bytes_eqb (cc_ekey (hcy5_CC2 x25519 R L Q rr)) (cc_ekey (hcy5_CC1 x25519 R L))) with true
        by (rewrite EE; symmetry; apply hcy5_p5_b_eqb_refl).
      forward_if.
      { exfalso. exact (Int.one_not_zero H1). }
      forward. entailer!. }
    { forward. entailer!. }
    unfold POSTCONDITION, abbreviate.
    match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
    replace (cookie_of (cc_secret (hcy5_CC2 x25519 R L Q rr)) (hcy5_skb Q m)) with CK by (rewrite HCK; reflexivity).
    unfold hcy5_p5_T2. Exists R S m c rp. Exists Q nonce rr CK CM.
    unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars, wg_consts. simpl app.
    rewrite (hcy5_p5_b_cc_open Tsh (cc_addr (l_wb L))).
    entailer!. apply derives_refl.
Qed.

End Seg.
