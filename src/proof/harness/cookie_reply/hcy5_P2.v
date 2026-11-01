(* law cookie_reply: phase P2 of main, statements
   11..17: len = draw_size (too big: return), len += 32, msg / copy / reply = malloc (NULL: frees, return).

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

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* conversions between the world compspecs and the compspecs of S2's items *)
#[local] Instance hcy5_p2_cce_C : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p2_cce_H : change_composite_env HCS W_cookie_reply.
Proof. make_cs_preserve HCS W_cookie_reply. Defined.

Lemma hcy5_p2_conv_cmsg sh p : @data_at_ Cookie.CS sh t_cmsg p = @data_at_ W_cookie_reply sh t_cmsg p.
Proof.
  rewrite (@data_at__change_composite Cookie.CS W_cookie_reply _ sh t_cmsg); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcy5_p2_conv_bytes sh n p : hout sh n p = @data_at_ W_cookie_reply sh (tarray tuchar n) p.
Proof.
  unfold hout.
  rewrite (@data_at__change_composite HCS W_cookie_reply _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type].
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* S1's SEP dissolves into main's stack frame (the returns of P2) *)
Lemma hcy5_p2_frame R L S gv FR :
  hcy5_closeH -> hcy5_run_ok R ->
  device_rep Tsh (l_wa L) (hcy5_DA x25519 R L) *
  itable Tsh (l_ita L) {| t_D := []; t_L := [] |} *
  ptable Tsh (l_pta L) nullval * @data_at W Tsh (tptr t_hnode4) nullval (l_peers L) *
  hcy5_drest Tsh (l_wb L) (hcy5_DB x25519 R L) *
  checker_rep Tsh (cc_addr (l_wb L)) (hcy5_CC1 x25519 R L) *
  itable Tsh (l_itb L) {| t_D := []; t_L := [] |} *
  ptable Tsh (l_ptb L) nullval *
  @data_at HCS Tsh t_mident (mident_val (hcy5_IB x25519 R)) (l_ib L) *
  hbytes Tsh (r_rawa R) (l_rawa L) * hbytes Tsh (r_rawb R) (l_rawb L) *
  @data_at_ Cookie.CS Tsh t_skb (l_skb L) * hout Tsh 32 (l_pub L) *
  hout Tsh 32 (l_secret L) * hout Tsh 16 (l_cookie L) *
  hout Tsh 32 (l_k L) * hout Tsh 32 (l_enc L) * hout Tsh 64 (l_img L) *
  hout Tsh 64 (l_img2 L) * hout Tsh 16 (l_pt L) *
  @data_at_ W Tsh t_devsnap (l_da L) * @data_at_ W Tsh t_devsnap (l_db L) *
  @data_at_ W Tsh t_skbsnap (l_sks L) * @data_at_ W Tsh t_shimsnap (l_ss L) *
  mem_mgr gv * shim_state4 gv S hcy5_w0 * noise_globals gv Int64.zero *
  wg_consts gv * hcy5_consts gv * FR
  |-- TT * @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wa L) *
    @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wb L) *
    @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_ita L) *
    @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_itb L) *
    @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_pta L) *
    @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_ptb L) *
    @data_at_ W Tsh (Tstruct HY._m_identity noattr) (l_ib L) *
    @data_at_ W Tsh (Tstruct HY._sk_buff noattr) (l_skb L) *
    @data_at_ W Tsh (tarray tuchar 32) (l_rawa L) *
    @data_at_ W Tsh (tarray tuchar 32) (l_rawb L) *
    @data_at_ W Tsh (tarray tuchar 32) (l_pub L) *
    @data_at_ W Tsh (tarray tuchar 32) (l_secret L) *
    @data_at_ W Tsh (tarray tuchar 16) (l_cookie L) *
    @data_at_ W Tsh (tarray tuchar 32) (l_k L) *
    @data_at_ W Tsh (tarray tuchar 32) (l_enc L) *
    @data_at_ W Tsh (tarray tuchar 64) (l_img L) *
    @data_at_ W Tsh (tarray tuchar 64) (l_img2 L) *
    @data_at_ W Tsh (tptr (Tstruct HY._hnode noattr)) (l_peers L) *
    @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_da L) *
    @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_db L) *
    @data_at_ W Tsh (Tstruct HY._skb_snap noattr) (l_sks L) *
    @data_at_ W Tsh (Tstruct HY._shim_snap noattr) (l_ss L) *
    @data_at_ W Tsh (tarray tuchar 16) (l_pt L).
Proof.
  intros HC (LA & LB & _).
  destruct HC as (Hd & Hdc & Hit & Hpt & Hskb & Hskbc & Hmid & Hout & Hhb).
  sep_apply (Hd Tsh (l_wa L) (hcy5_DA x25519 R L)).
  sep_apply (Hdc Tsh (l_wb L) (hcy5_DB x25519 R L) (hcy5_CC1 x25519 R L)).
  sep_apply (Hit Tsh (l_ita L) {| t_D := []; t_L := [] |}).
  sep_apply (Hit Tsh (l_itb L) {| t_D := []; t_L := [] |}).
  sep_apply (Hpt Tsh (l_pta L) nullval).
  sep_apply (Hpt Tsh (l_ptb L) nullval).
  sep_apply (Hmid Tsh (mident_val (hcy5_IB x25519 R)) (l_ib L)).
  sep_apply (Hskbc Tsh (l_skb L)).
  sep_apply (Hhb Tsh (r_rawa R) (l_rawa L)).
  sep_apply (Hhb Tsh (r_rawb R) (l_rawb L)).
  rewrite LA, LB.
  sep_apply (Hout Tsh 32 (l_pub L)). sep_apply (Hout Tsh 32 (l_secret L)).
  sep_apply (Hout Tsh 16 (l_cookie L)). sep_apply (Hout Tsh 32 (l_k L)).
  sep_apply (Hout Tsh 32 (l_enc L)). sep_apply (Hout Tsh 64 (l_img L)).
  sep_apply (Hout Tsh 64 (l_img2 L)). sep_apply (Hout Tsh 16 (l_pt L)).
  sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) nullval (l_peers L)).
  simpl iter_sepcon.
  cancel.
Qed.

Lemma hcy5_P2_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_closeH ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S1 x25519 gv L FR) hcy5_P2
    (overridePost (hcy5_S2 x25519 gv L FR) (hcy5_R gv)).
Proof.
  intros HH HC. unfold hcy5_S1, hcy5_Delta, hcy5_R, hcy5_P2. simplify_func_tycontext. abbreviate_semax.
  Intros R S.
  apply hcy5_post_canon.
  unfold hcy5_lvars, hcy5_scrA, hcy5_globs, hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_snaps0. simpl app.
  forward_call tt. Intros n0.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HY._t'4 (Vint (if Int.max_unsigned <? n0 + 32 then Int.one else Int.zero)) :: Lc)
                (SEPx Rs))) end.
  - forward. entailer!. rewrite (Int64.unsigned_repr n0) in H1 by lia.
    assert (Int64.unsigned (Int64.repr (-1-32)) = 18446744073709551583) as E0 by reflexivity. rewrite E0 in H1.
    destruct (Int.max_unsigned <? n0 + 32) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. rep_lia.
  - forward. entailer!. rewrite (Int64.unsigned_repr n0) in H1 by lia.
    assert (Int64.unsigned (Int64.repr (-1-32)) = 18446744073709551583) as E0 by reflexivity. rewrite E0 in H1.
    unfold Int64.cmpu, Int64.ltu. change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (Int.max_unsigned <? n0 + 32) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      [rewrite zlt_true by lia | rewrite zlt_false by lia]; reflexivity.
  - forward_if.
    + forward. apply hcy5_p2_frame; auto.
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
      forward_call (t_cmsg, gv).
      Intros rp.
      destruct (eq_dec m nullval) as [Em|Em].
      * (* msg == NULL *)
        Intros.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HY._t'8 (Vint Int.one) :: Lc) (SEPx Rs))) end.
        -- forward. entailer!.
        -- subst m. exfalso. auto.
        -- match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
             forward_if (PROPx P (LOCALx (temp HY._t'9 (Vint Int.one) :: Lc) (SEPx Rs))) end.
           ++ forward. entailer!.
           ++ exfalso. apply Int.one_not_zero. assumption.
           ++ forward_if.
              ** forward_call (tarray tuchar (n0 + 32), m, gv).
                 { destruct (eq_dec m nullval); [|contradiction]. cancel. }
                 forward_call (tarray tuchar (n0 + 32), c, gv).
                 forward_call (t_cmsg, rp, gv).
                 forward.
                 eapply derives_trans; [| apply (hcy5_p2_frame R L S gv FR); auto]; cancel.
              ** exfalso. apply Int.one_not_zero. assumption.
      * destruct (eq_dec c nullval) as [Ec|Ec].
        -- (* copy == NULL *)
           Intros.
           match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
             forward_if (PROPx P (LOCALx (temp HY._t'8 (Vint Int.one) :: Lc) (SEPx Rs))) end.
           ++ forward. entailer!.
           ++ forward. entailer!.
           ++ match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
                forward_if (PROPx P (LOCALx (temp HY._t'9 (Vint Int.one) :: Lc) (SEPx Rs))) end.
              ** forward. entailer!.
              ** exfalso. apply Int.one_not_zero. assumption.
              ** forward_if.
                 --- forward_call (tarray tuchar (n0 + 32), m, gv).
                     { destruct (eq_dec m nullval); [contradiction|]. cancel. }
                     forward_call (tarray tuchar (n0 + 32), c, gv).
                     { destruct (eq_dec c nullval); [|contradiction]. cancel. }
                     forward_call (t_cmsg, rp, gv).
                     forward.
                     eapply derives_trans; [| apply (hcy5_p2_frame R L S gv FR); auto]; cancel.
                 --- exfalso. apply Int.one_not_zero. assumption.
        -- (* msg, copy allocated *)
           Intros.
           match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
             forward_if (PROPx P (LOCALx (temp HY._t'8 (Vint Int.zero) :: Lc) (SEPx Rs))) end.
           ++ forward. entailer!.
           ++ forward. entailer!.
              match goal with Hf: field_compatible _ [] c |- _ => destruct Hf as [Hp _] end.
              destruct c; try contradiction. reflexivity.
           ++ destruct (eq_dec rp nullval) as [Er|Er].
              ** (* reply == NULL *)
                 Intros.
                 match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
                   forward_if (PROPx P (LOCALx (temp HY._t'9 (Vint Int.one) :: Lc) (SEPx Rs))) end.
                 --- exfalso. auto.
                 --- forward. entailer!.
                 --- forward_if.
                     +++ forward_call (tarray tuchar (n0 + 32), m, gv).
                         { destruct (eq_dec m nullval); [contradiction|]. cancel. }
                         forward_call (tarray tuchar (n0 + 32), c, gv).
                         { destruct (eq_dec c nullval); [contradiction|]. cancel. }
                         forward_call (t_cmsg, rp, gv).
                         { destruct (eq_dec rp nullval); [|contradiction]. cancel. }
                         forward.
                         eapply derives_trans; [| apply (hcy5_p2_frame R L S gv FR); auto]; cancel.
                     +++ exfalso. apply Int.one_not_zero. assumption.
              ** (* all allocated *)
                 Intros.
                 match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
                   forward_if (PROPx P (LOCALx (temp HY._t'9 (Vint Int.zero) :: Lc) (SEPx Rs))) end.
                 --- exfalso. auto.
                 --- forward. entailer!.
                     match goal with Hf: field_compatible _ [] rp |- _ => destruct Hf as [Hp _] end.
                     destruct rp; try contradiction. reflexivity.
                 --- forward_if.
                     +++ exfalso. auto.
                     +++ forward.
                         unfold hcy5_S2. Exists R S (n0 + 32) m c rp.
                         unfold hcy5_lvars, hcy5_scrA, hcy5_globs, hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_snaps0.
                         simpl app.
                         rewrite (hcy5_p2_conv_bytes Ews (n0 + 32) m), (hcy5_p2_conv_bytes Ews (n0 + 32) c),
                           (hcy5_p2_conv_cmsg Ews rp).
                         unfold hcy5_tok.
                         entailer!.
Qed.

End Phase.
