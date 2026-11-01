(* law cookie_mac: main's phase P8, statements 90..94 of hck5_cut.v:
   v1 P8 (hck3_P8.v.old) + (v2) kents_free(kes) before return 0 (dissolution: hck5_freeH).
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
Require Import WgNoise.proof.harness.cookie_mac.hck5_p8_pure.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

#[local] Instance hck5_p8_cce_N : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.
#[local] Instance hck5_p8_cce_H : change_composite_env HCS W_cookie_mac.
Proof. make_cs_preserve HCS W_cookie_mac. Defined.

Lemma hck5_p8_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_cookie_mac sh t_mident (mident_val I) p.
Proof.
  assert (E := @data_at_change_composite HCS W_cookie_mac hck5_p8_cce_H sh t_mident (mident_val I) (mident_val I)
           (JMeq_refl _)).
  rewrite E; [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hck5_p8_tbool_cs sh (v: val) p :
  @data_at Noise.CS sh tbool v p = @data_at W_cookie_mac sh tbool v p.
Proof. exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_cookie_mac _ sh tbool v v (JMeq_refl v) eq_refl)). Qed.

Section P8.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P8_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hck5_freeH x25519 ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S7b x25519 gv L FR) hck5_P8
    (overridePost FF (hck5_R gv)).
Proof.
  intros HH HF. unfold hck5_S7b, hck5_Delta, hck5_R, hck5_P8. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck. Intros MSG1 C1 MSG2 corrupted chk rl r VR.
  apply hck5_post_canon.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps0. simpl app.
  unfold shim_state4, shim_core. Intros.
  rewrite (hck5_p8_tbool_cs Ews (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HK._t'96 (Vint (if andb (negb corrupted) (r_honest R) then Int.one else Int.zero)) :: Lc)
                (SEPx Rs))) end.
  - forward. entailer!. destruct corrupted; [discriminate|]. destruct (r_honest R); reflexivity.
  - forward. entailer!. destruct corrupted; [reflexivity|].
    match goal with Hc: _ <> Int.zero |- _ => elim Hc; reflexivity end.
  - rewrite (hck5_p8_mident_W Tsh (mident_of x25519 (r_rawb R)) (l_ib L)).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HK._t'97 (Vint (if andb (andb (negb corrupted) (r_honest R))
                    (mi_ok (mident_of x25519 (r_rawb R))) then Int.one else Int.zero)) :: Lc) (SEPx Rs))) end.
    + forward. forward. entailer!.
      destruct (andb (negb corrupted) (r_honest R)); [| match goal with Hc: _ <> Int.zero |- _ => elim Hc; reflexivity end].
      destruct (mi_ok _); reflexivity.
    + forward. entailer!.
      destruct (andb (negb corrupted) (r_honest R)); [| reflexivity].
      match goal with Hc: Int.one = Int.zero |- _ => discriminate Hc end.
    + match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
        forward_if (PROPx P (LOCALx Lc (SEPx Rs))) end.
      * assert (Ec: andb (andb (negb corrupted) (r_honest R)) (mi_ok (mident_of x25519 (r_rawb R))) = true).
        { match goal with Hc: (if ?b then Int.one else _) <> Int.zero |- _ =>
            destruct b eqn:E; [|elim Hc; reflexivity] end. exact E. }
        apply andb_prop in Ec as [Ec Hok]. apply andb_prop in Ec as [Ec Hh]. apply negb_true_iff in Ec.
        subst corrupted.
        pose proof (hck5_p8_round x25519 R L Q m cmode C ck MSG1 C1 MSG2 chk rl r VR S H H1 H2 H3 H4 H5 H6 Hh Hok)
          as [Hr1 Hr2].
        assert (Hrange: 0 <= fst VR <= 3)
          by (destruct H6 as (_&_&_&HVR&_); unfold hck5_is in HVR; subst VR; apply hck5_p8_vrange).
        assert (Hne0: Int.eq (Int.repr (fst VR)) (Int.repr 0) = false).
        { apply Int.eq_false. intro E. apply (f_equal Int.unsigned) in E. rewrite !Int.unsigned_repr in E by rep_lia.
          unfold INVALID_MAC in Hr1. lia. }
        match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
        -- entailer!.
        -- forward_if.
          ++ exfalso. rewrite Hne0 in *. apply Int.one_not_zero. assumption.
          ++ forward. entailer!.
        -- forward. entailer!.
        -- match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
             forward_if (PROPx P (LOCALx (temp HK._t'95 (Vint (if andb cmode chk then Int.one else Int.zero)) :: Lc)
                         (SEPx Rs))) end.
          ++ forward. entailer!. destruct cmode; [| match goal with Hc: _ <> Int.zero |- _ => elim Hc; reflexivity end].
             destruct chk; reflexivity.
          ++ forward. entailer!. destruct cmode; [| reflexivity].
             match goal with Hc: Int.one = Int.zero |- _ => discriminate Hc end.
          ++ forward_if.
             ** assert (Ecc: andb cmode chk = true)
                  by (destruct (andb cmode chk);
                      [reflexivity | match goal with Hc: _ <> Int.zero |- _ => elim Hc; reflexivity end]).
                apply andb_prop in Ecc as [Ecm Ech]. specialize (Hr2 Ecm Ech).
                destruct H6 as (_&_&_&_&_&HSrl&_). subst rl.
                match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
                --- entailer!.
                --- forward.
                    { entailer!. destruct (s_rlallow S); simpl; auto. }
                    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
                      forward_if (PROPx P (LOCALx (temp HK._t'94 (Vint (Int.repr (if s_rlallow S then 3 else 2)))
                                  :: Lc) (SEPx Rs))) end.
                    +++ forward. entailer!.
                        match goal with Ht: typed_true _ _ |- _ => destruct (s_rlallow S); [reflexivity | inv Ht] end.
                    +++ forward. entailer!.
                        match goal with Ht: typed_false _ _ |- _ => destruct (s_rlallow S); [inv Ht | reflexivity] end.
                    +++ forward_if.
                        *** exfalso. unfold VALID_MAC_WITH_COOKIE, VALID_MAC_WITH_COOKIE_BUT_RATELIMITED in Hr2.
                            match goal with Ht: Int.repr (Z.b2z _) = Int.zero |- _ =>
                              rewrite Hr2 in Ht; destruct (s_rlallow S); rewrite Int.eq_true in Ht;
                              apply Int.one_not_zero; exact Ht end.
                        *** forward. entailer!.
                --- forward. entailer!.
                --- unfold POSTCONDITION, abbreviate.
                    match goal with |- context [RA_normal (overridePost ?Q ?R')] =>
                      change (RA_normal (overridePost Q R')) with Q end.
                    entailer!.
             ** forward. entailer!.
      * forward. entailer!.
      * destruct H6 as (HM2 & HL2 & HLr & HVR & HSb & HSrl & HSlog).
        sep_apply (hck5_hbytes_free Ews MSG2 m). sep_apply (hck5_hbytes_free Ews MSG2 c). rewrite HL2.
        assert_PROP (isptr m /\ isptr c) as Pmc by entailer!. destruct Pmc as [Pm Pc].
        forward_call (tarray tuchar (q_n Q), m, gv).
        { rewrite if_false by (intro; subst; contradiction). unfold hck5_tok. cancel. }
        forward_call (tarray tuchar (q_n Q), c, gv).
        { rewrite if_false by (intro; subst; contradiction). unfold hck5_tok. cancel. }
        destruct HF as [HFA HFB].
        sep_apply (HFA R L A C1 H0).
        forward_call (gv, a_kes A, a_KE A).
        { cancel. }
        forward.
        rewrite <- (hck5_p8_mident_W Tsh (mident_of x25519 (r_rawb R)) (l_ib L)).
        pose proof (HFB R L (snd VR)) as B.
        pose proof (hck5_bufs_free x25519 R L H) as C'.
        unfold hck5_bside, hck5_bufs in B, C'. simpl fold_right in B, C'.
        rewrite sepcon_emp in B, C'.
        sep_apply B. sep_apply C'. sep_apply (hck5_skb_free Tsh (l_skb L) (hck5_skb Q m)).
        rewrite hck5_conv_cksnap, hck5_conv_hsnap, hck5_conv_prsnap, !hck5_conv_devsnap, hck5_conv_skbsnap,
          hck5_conv_shimsnap, !hck5_conv_bytes.
        cancel.
Qed.

End P8.
