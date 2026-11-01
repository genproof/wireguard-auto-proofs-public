(* law cookie_mac: main's phase P4, statements 44..51 of hck5_cut.v:
   v1 P4 (hck3_P4.v.old).
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
Require Import WgNoise.proof.harness.cookie_mac.hck5_p4_lemmas.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Section P4.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p4_A_fc R L A : hck5_A x25519 R L A |-- !! @field_compatible Noise.CS t_peer [] (l_p L).
Proof. unfold hck5_A. sep_apply (hck5_p4_prest_fc Tsh (l_p L) (a_P A)). entailer!. Qed.

Lemma hck5_P4_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S3 x25519 gv L FR) hck5_P4
    (overridePost (hck5_S4 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S3, hck5_Delta, hck5_R, hck5_P4. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q.
  unfold hck5_bside, hck5_bufs, hck5_scr, hck5_globs, hck5_lvars, hck5_snaps0. simpl app.
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_p L)) as Hfp.
  { sep_apply hck5_p4_A_fc. entailer!. }
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wb L)) as Hfd.
  { sep_apply hck5_p4_drest_fc. entailer!. }
  unfold cookie_rep at 1. Intros lk.
  rewrite (hck5_p4_open _ _ _ Hfp).
  (* is_valid = nondet_u8() & 1 *)
  forward_call tt. Intros b1. forward. rewrite hck5_p4_bool.
  generalize (negb (Int.eq (Int.and (Int.repr b1) (Int.repr 1)) Int.zero)); intros vb.
  (* birthdate = draw_boottime() *)
  forward_call tt. Intros t0. forward.
  (* the 115 s edge *)
  forward_call tt. Intros b2.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
    forward_if (EX i: int, PROPx Pr (LOCALx (temp HK._t'36 (Vint i) :: Lc) (SEPx Rs))) end.
  { apply prop_right. intros [_ Hc]. apply (f_equal Int.signed) in Hc.
    rewrite Int.signed_repr in Hc by rep_lia. rewrite Int.signed_mone in Hc. lia. }
  { forward.
    Exists (if Int64.cmpu Cge (q_now Q) (Int64.repr 115000000002) then Int.one else Int.zero). entailer!.
    destruct (Int64.cmpu Cge (q_now Q) (Int64.repr 115000000002)); reflexivity. }
  { forward. Exists Int.zero. entailer!. }
  Intros i29.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
    let F := eval pattern t0 in Rs in
    match F with ?G t0 => forward_if (EX bd: int64, PROPx Pr (LOCALx Lc (SEPx (G bd)))) end end.
  { forward_call tt. Intros b3. forward.
    { entailer!. match goal with HX: _ /\ Int.repr 5 = Int.mone |- _ => destruct HX as [_ Hc] end.
      apply (f_equal Int.signed) in Hc. rewrite Int.signed_repr in Hc by rep_lia.
      rewrite Int.signed_mone in Hc. lia. }
    match goal with |- context [field_at _ _ [StructField HK._birthdate; _] (Vlong ?v) _] => Exists v end.
    entailer!. }
  { forward. Exists t0. entailer!. }
  Intros bd.
  (* nondet_bytes(p.latest_cookie.cookie, 16) *)
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (bytes (ck_cookie (hck5_C0 R))) (offset_val 369 (l_p L))).
  forward_call (offset_val 369 (l_p L), 16, Tsh).
  Intros ckl. rewrite (hck5_p4_nd ckl) by auto.
  (* have_sent_mac1 = nondet_u8() & 1 *)
  forward_call tt. Intros b4. forward. rewrite hck5_p4_bool.
  generalize (negb (Int.eq (Int.and (Int.repr b4) (Int.repr 1)) Int.zero)); intros sb.
  (* nondet_bytes(p.latest_cookie.last_mac1_sent, 16) *)
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (bytes (ck_last_mac1 (hck5_C0 R))) (offset_val 386 (l_p L))).
  forward_call (offset_val 386 (l_p L), 16, Tsh).
  Intros m1l. rewrite (hck5_p4_nd m1l) by auto.
  (* cookie_mode = nondet_u8() & 1 *)
  forward_call tt. Intros b5. forward.
  rewrite (hck5_p4_and1 b5) by auto.
  pose (ck0 := cookie_of (r_secret R) (hck5_skb Q m)).
  assert (Hck: hck5_is ck0 (cookie_of (r_secret R) (hck5_skb Q m))) by reflexivity.
  clearbody ck0.
  assert (Lck: Zlength (map Byte.repr ckl) = 16) by (rewrite Zlength_map; auto).
  assert (Lm1: Zlength (map Byte.repr m1l) = 16) by (rewrite Zlength_map; auto).
  destruct (Z.odd b5) eqn:Hodd.
  - (* cookie_mode *)
    forward_if; [| exfalso; apply Int.one_not_zero; assumption].
    sep_apply (hck5_p4_cc_unfold (l_wb L) (hck5_CC1 x25519 R L) Hfd). Intros lkc.
    forward.
    forward_call (cc_birth (hck5_CC1 x25519 R L), Int64.repr 120, q_now Q).
    set (b0 := cc_birth (hck5_CC1 x25519 R L)).
    match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
      let F := eval pattern b0 in Rs in
      match F with ?G b0 =>
        forward_if (PROPx Pr (LOCALx Lc (SEPx (G (if birthdate_expired b0 (Int64.repr 120) (q_now Q)
                                                  then q_now Q else b0))))) end end.
    { destruct (birthdate_expired b0 (Int64.repr 120) (q_now Q)) eqn:He; [| contradiction].
      forward. entailer!. }
    { destruct (birthdate_expired b0 (Int64.repr 120) (q_now Q)) eqn:He;
        [exfalso; apply Int.one_not_zero; assumption |].
      forward. entailer!. }
    (* m_cookie(p.latest_cookie.cookie, wb.cookie_checker.secret, &skb) *)
    unfold wg_consts.
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (bytes (map Byte.repr ckl)) (offset_val 369 (l_p L))).
    rewrite hck5_p4_hout.
    change (cc_secret (hck5_CC1 x25519 R L)) with (r_secret R).
    assert (Lsec: Zlength (r_secret R) = 32) by (destruct H as (_ & _ & _ & _ & Ls & _); exact Ls).
    rewrite (hck5_p4_hbytes Tsh 32 (r_secret R) (offset_val 80 (l_wb L)) Lsec).
    forward_call (gv, Tsh, offset_val 369 (l_p L), Tsh, offset_val 80 (l_wb L), r_secret R, Tsh, l_skb L, hck5_skb Q m).
    assert (Lck0: Zlength ck0 = 16) by (unfold hck5_is in Hck; rewrite Hck; apply hck5_p4_cookie_len).
    replace (cookie_of (r_secret R) (hck5_skb Q m)) with ck0 by exact Hck.
    rewrite <- (hck5_p4_hbytes Tsh 16 ck0 _ Lck0).
    rewrite <- (hck5_p4_hbytes Tsh 32 (r_secret R) _ Lsec).
    (* is_valid = true; birthdate = now *)
    forward. forward.
    change (Vint Int.one) with (Val.of_bool true).
    change (r_secret R) with (cc_secret (hck5_CC1 x25519 R L)).
    sep_apply (hck5_p4_cc_fold (l_wb L) (hck5_CC1 x25519 R L)
                 (if birthdate_expired b0 (Int64.repr 120) (q_now Q) then q_now Q else b0) lkc Hfd H14).
    sep_apply (hck5_p4_ck_fold (l_p L) (q_now Q) true ck0 sb (map Byte.repr m1l) (hck5_C0 R) lk Hfp Lck0 Lm1 H3).
    unfold hck5_S4.
    Exists R S A m c Q true
      (mkCookie (q_now Q) true ck0 sb (map Byte.repr m1l) (ck_dkey (hck5_C0 R)) (ck_mkey (hck5_C0 R))) ck0.
    rewrite hck5_p4_CC2_true. subst b0.
    unfold hck5_bside, hck5_bufs, hck5_scr2, hck5_globs, hck5_lvars, hck5_snaps0, wg_consts. simpl app.
    entailer!.
    + destruct H3 as (_ & _ & D1 & D2).
      split; [split; [exact Lck0 | split; [exact Lm1 | split; [exact D1 | exact D2]]] |].
      split; [reflexivity | split; [reflexivity | intros _; auto]].
    + rewrite sepcon_comm. apply derives_refl.
  - (* no cookie_mode *)
    forward_if.
    { contradiction. }
    forward.
    sep_apply (hck5_p4_ck_fold (l_p L) bd vb (map Byte.repr ckl) sb (map Byte.repr m1l) (hck5_C0 R) lk Hfp Lck Lm1 H3).
    Exists R S A m c Q false (mkCookie bd vb (map Byte.repr ckl) sb (map Byte.repr m1l) (ck_dkey (hck5_C0 R)) (ck_mkey (hck5_C0 R))) ck0.
    rewrite hck5_p4_CC2_false.
    unfold hck5_bside, hck5_bufs, hck5_scr2, hck5_globs, hck5_lvars, hck5_snaps0. simpl app.
    entailer!.
    + destruct H3 as (_ & _ & D1 & D2).
      split; [split; [exact Lck | split; [exact Lm1 | split; [exact D1 | exact D2]]] |].
      split; [reflexivity | split; [reflexivity | discriminate]].
    + apply derives_refl.
Qed.

End P4.
