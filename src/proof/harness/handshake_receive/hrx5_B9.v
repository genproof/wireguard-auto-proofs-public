(* law handshake_receive: main's phase B9 = body statements 42..43: free(skb.data), free(img).
   From hrx5_S8 to hrx5_SC (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.libc.libc_bytes.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the message object and the image as free's precondition (token * data_at_ at the world) *)
#[local] Instance hrx5_b9_cce_C : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

Definition hrx5_b9_ty (o: hrx5_obj) : type :=
  match o with
  | OBuf b => tarray tuchar (Zlength b)
  | OInit _ => t_init
  | OResp _ => t_resp
  | OCookie _ => t_cmsg
  end.

Lemma hrx5_b9_cmsg sh p : @data_at_ Cookie.CS sh t_cmsg p = @data_at_ W_handshake_receive sh t_cmsg p.
Proof.
  rewrite (@data_at__change_composite Cookie.CS W_handshake_receive _ sh t_cmsg);
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_b9_skb_cs sh (dv lv pv: val) (a b c: list val) p :
  @data_at Cookie.CS sh t_skb (dv, (lv, (pv, (a, (b, c))))) p =
  @data_at W_handshake_receive sh t_skb (dv, (lv, (pv, (a, (b, c))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Cookie.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_b9_obj dp o :
  obj_rep dp o |-- @malloc_token W_handshake_receive Ews (hrx5_b9_ty o) dp *
                   @data_at_ W_handshake_receive Ews (hrx5_b9_ty o) dp.
Proof.
  destruct o as [b|M|M|M]; simpl; apply sepcon_derives; try apply derives_refl.
  - unfold bytes_at. eapply derives_trans; [apply data_at_data_at_ |].
    rewrite (@data_at__tarray_tuchar_cs Noise.CS W_handshake_receive). apply derives_refl.
  - unfold init_rep. Intros. eapply derives_trans; [apply data_at_data_at_ |].
    rewrite hrx5_conv_init. apply derives_refl.
  - unfold resp_rep. Intros. eapply derives_trans; [apply data_at_data_at_ |].
    rewrite hrx5_conv_resp. apply derives_refl.
  - unfold cmsg_rep. Intros. eapply derives_trans; [apply data_at_data_at_ |].
    rewrite hrx5_b9_cmsg. apply derives_refl.
Qed.

Lemma hrx5_b9_img img msg :
  img_rep img msg |-- @malloc_token W_handshake_receive Ews (tarray tuchar (Zlength msg)) img *
                      @data_at_ W_handshake_receive Ews (tarray tuchar (Zlength msg)) img.
Proof.
  unfold img_rep. apply sepcon_derives; [apply derives_refl |].
  unfold hbytes. eapply derives_trans; [apply data_at_data_at_ |].
  rewrite <- hrx5_conv_bytes. apply derives_refl.
Qed.

Section B9.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B9_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S8 x25519 gv L FR) hrx5_B9
    (overridePost (hrx5_SC x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HY. unfold hrx5_Delta, hrx5_S8.
  Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto.
  Intros ip4 ip6 port o dp img.
  unfold hrx5_B9, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app].
  abbreviate_semax.
  unfold skb_rep, hrx5_skb, skb_val; cbn [sk_data sk_len sk_proto sk_ip4 sk_ip6 sk_port]. Intros.
  rewrite hrx5_b9_skb_cs.
  sep_apply (hrx5_b9_obj dp o).
  sep_apply (hrx5_b9_img img (obj_bytes o)).
  Intros.
  assert_PROP (isptr dp) by entailer!.
  assert_PROP (isptr img) by entailer!.
  forward.
  forward_call (hrx5_b9_ty o, dp, gv).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  forward_call (tarray tuchar (Zlength (obj_bytes o)), img, gv).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_SC x25519 gv L FR) end.
  unfold hrx5_SC, hrx5_SLc.
  Exists R sec birth S w NS PS T.
  Exists head nk KE st i kc lul.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_skb0; cbn [app].
  sep_apply (@data_at_data_at_ W_handshake_receive Tsh t_skb).
  rewrite <- hrx5_conv_skb.
  entailer!.
Qed.

End B9.
