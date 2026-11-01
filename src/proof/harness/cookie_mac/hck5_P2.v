(* law cookie_mac: main's phase P2, statements 28..33 of hck5_cut.v:
   v1 P2 (hck3_P2.v.old): len, the two mallocs, the early returns (dissolution: hck5_freeH).
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
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Section P2.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* S1b's SEP (and the returns' state) dissolves into main's stack frame *)
Lemma hck5_p2_frame R L A S gv FR :
  hck5_freeH x25519 -> hck5_run_ok x25519 R -> hck5_aok L A ->
  hck5_A x25519 R L A * fold_right sepcon emp (hck5_bside x25519 R L) *
  fold_right sepcon emp (hck5_bufs x25519 R L) *
  checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC1 x25519 R L) *
  cookie_rep Tsh (cookie_addr (l_p L)) (hck5_C0 R) *
  @data_at_ Cookie.CS Tsh t_skb (l_skb L) *
  fold_right sepcon emp (hck5_scr L) * fold_right sepcon emp (hck5_snaps0 L) *
  fold_right sepcon emp (hck5_globs gv S FR)
  |-- TT * @data_at_ W_cookie_mac Tsh (Tstruct HK._wg_device noattr) (l_wa L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._wg_device noattr) (l_wb L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._index_hashtable noattr) (l_ita L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._index_hashtable noattr) (l_itb L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._pubkey_hashtable noattr) (l_pta L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._pubkey_hashtable noattr) (l_ptb L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._wg_peer noattr) (l_p L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._m_identity noattr) (l_ib L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._ck_snap noattr) (l_cs L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._hs_snap noattr) (l_hs0 L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._pr_snap noattr) (l_ps0 L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._dev_snap noattr) (l_da L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._dev_snap noattr) (l_db L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._skb_snap noattr) (l_sks L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._shim_snap noattr) (l_ss L) *
    @data_at_ W_cookie_mac Tsh (Tstruct HK._sk_buff noattr) (l_skb L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_rawa L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_rawb L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_pub L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_k L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 16) (l_mac1 L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 16) (l_mac2 L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 16) (l_cookie L) *
    @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_secret L).
Proof.
  intros [HA HB] Hok Haok.
  sep_apply (HA R L A (hck5_C0 R) Haok).
  sep_apply (HB R L (hck5_CC1 x25519 R L)).
  sep_apply (hck5_bufs_free x25519 R L Hok).
  rewrite hck5_snaps0_free.
  unfold hck5_scr, hck5_globs. cbv [fold_right].
  rewrite hck5_conv_skb, hck5_conv_cksnap, !hck5_conv_bytes.
  cancel.
Qed.

(* the two frees and the return (msg or copy NULL) *)
Ltac hck5_p2_freeret R L A S gv FR n0 m c :=
  forward_call (tarray tuchar (n0 + 32), m, gv);
  [ first [rewrite if_true by auto | rewrite if_false by auto]; cancel |];
  forward_call (tarray tuchar (n0 + 32), c, gv);
  [ first [rewrite if_true by auto | rewrite if_false by auto]; cancel |];
  forward;
  eapply derives_trans; [| apply (hck5_p2_frame R L A S gv FR); auto];
  unfold hck5_bside, hck5_bufs, hck5_scr, hck5_snaps0, hck5_globs; cbv [fold_right]; cancel.

Lemma hck5_P2_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hck5_freeH x25519 ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S1b x25519 gv L FR) hck5_P2
    (overridePost (hck5_S2 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH HF. unfold hck5_S1b, hck5_Delta, hck5_R, hck5_P2. simplify_func_tycontext. abbreviate_semax.
  Intros R S A.
  apply hck5_post_canon.
  unfold hck5_lvars, hck5_scr, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps0. simpl app.
  forward_call tt. Intros n0.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HK._t'19 (Vint (if Int.max_unsigned <? n0 + 32 then Int.one else Int.zero)) :: Lc)
                (SEPx Rs))) end.
  - forward. entailer!. rewrite (Int64.unsigned_repr n0) in H2 by lia.
    assert (Int64.unsigned (Int64.repr (-1-32)) = 18446744073709551583) as E0 by reflexivity. rewrite E0 in H2.
    destruct (Int.max_unsigned <? n0 + 32) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. rep_lia.
  - forward. entailer!. rewrite (Int64.unsigned_repr n0) in H2 by lia.
    assert (Int64.unsigned (Int64.repr (-1-32)) = 18446744073709551583) as E0 by reflexivity. rewrite E0 in H2.
    unfold Int64.cmpu, Int64.ltu. change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (Int.max_unsigned <? n0 + 32) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      [rewrite zlt_true by lia | rewrite zlt_false by lia]; reflexivity.
  - forward_if.
    + forward.
      eapply derives_trans; [| apply (hck5_p2_frame R L A S gv FR); auto].
      unfold hck5_bside, hck5_bufs, hck5_scr, hck5_snaps0, hck5_globs. cbv [fold_right].
      cancel.
    + forward.
      assert (Hn: n0 + 32 <= Int.max_unsigned) by
        (destruct (Int.max_unsigned <? n0 + 32) eqn:E; [discriminate | apply Z.ltb_ge in E; lia]).
      replace (Int64.add (Int64.repr n0) (Int64.repr (Int.signed (Int.repr 32)))) with (Int64.repr (n0 + 32))
        by (rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia; reflexivity).
      forward_call (tarray tuchar (n0 + 32), gv).
      { simpl. rewrite Z.max_r by lia. rep_lia. }
      Intros m.
      forward_call (tarray tuchar (n0 + 32), gv).
      { simpl. rewrite Z.max_r by lia. rep_lia. }
      Intros c.
      destruct (eq_dec m nullval) as [Em|Em]; destruct (eq_dec c nullval) as [Ec|Ec].
      * (* msg == NULL *)
        Intros.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HK._t'22 (Vint Int.one) :: Lc) (SEPx Rs))) end.
        -- forward. entailer!.
        -- subst m. exfalso. auto.
        -- forward_if.
           ++ hck5_p2_freeret R L A S gv FR n0 m c.
           ++ exfalso. apply Int.one_not_zero. assumption.
      * (* msg == NULL *)
        Intros.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HK._t'22 (Vint Int.one) :: Lc) (SEPx Rs))) end.
        -- forward. entailer!.
        -- subst m. exfalso. auto.
        -- forward_if.
           ++ hck5_p2_freeret R L A S gv FR n0 m c.
           ++ exfalso. apply Int.one_not_zero. assumption.
      * (* copy == NULL *)
        Intros.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HK._t'22 (Vint Int.one) :: Lc) (SEPx Rs))) end.
        -- forward. entailer!.
        -- forward. entailer!.
        -- forward_if.
           ++ hck5_p2_freeret R L A S gv FR n0 m c.
           ++ exfalso. apply Int.one_not_zero. assumption.
      * (* both allocated *)
        Intros.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HK._t'22 (Vint Int.zero) :: Lc) (SEPx Rs))) end.
        -- forward. entailer!.
        -- forward. entailer!.
           match goal with Hf: field_compatible _ [] c |- _ => destruct Hf as [Hp _] end.
           destruct c; try contradiction. reflexivity.
        -- forward_if.
           ++ exfalso. auto.
           ++ forward.
              unfold hck5_S2. Exists R S A (n0 + 32) m c.
              unfold hck5_lvars, hck5_scr, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps0. simpl app.
              rewrite (hck5_conv_bytes Ews (n0+32) m), (hck5_conv_bytes Ews (n0+32) c). unfold hck5_tok.
              entailer!.
Qed.

End P2.
