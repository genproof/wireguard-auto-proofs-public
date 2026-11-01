(* law handshake_receive, phase B3, branch kind 0, segment Z:
   stmts 9..12: img = malloc(len); NULL -> free(buf), continue (hrx5_SC); bytes_copy(img, buf, len); skb.data = buf.
   States and statements: hrx5_B3_K0_defs.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_defs.
Local Open Scope logic.

(* byte arrays are the same in every compspecs (port of hrx5_B3_K0_A's k0a_tuchar_cs) *)
Lemma k0z_align_tuchar_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuchar n) z -> align_compatible_rec ce2 (tarray tuchar n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma k0z_fc_tuchar_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (k0z_align_tuchar_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (k0z_align_tuchar_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma k0z_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply k0z_fc_tuchar_cs.
Qed.

Lemma k0z_tuchar_cs_ {cs1 cs2: compspecs} sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. unfold data_at_, field_at_. apply k0z_tuchar_cs. Qed.

Lemma k0z_obj_open (B: list byte) dp :
  obj_rep dp (OBuf B) |--
  @malloc_token W_handshake_receive Ews (tarray tuchar (Zlength B)) dp *
  @data_at_ W_handshake_receive Ews (tarray tuchar (Zlength B)) dp.
Proof.
  unfold obj_rep, bytes_at. cancel.
  rewrite (@k0z_tuchar_cs Noise.CS W_handshake_receive). apply data_at_data_at_.
Qed.

Lemma k0z_bytes_hbytes sh (B: list byte) p : bytes_at sh B p = hbytes sh B p.
Proof. unfold bytes_at, hbytes. apply k0z_tuchar_cs. Qed.

Ltac k0z_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1 :=
  unfold hrx5_SC, hrx5_SLc;
  Exists R sec birth S w NS PS T head; Exists nk KE st i kc lul;
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_rglobs, hrx5_skb0; cbn [app];
  unfold hrx5_skb_part, qlen_rep; Intros dv lv;
  go_lower;
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 _))); repeat split; auto; try lia;
     try (rewrite eqb_type_refl; reflexivity) |];
  sep_apply (@data_at_data_at_ HRX Ews tint);
  sep_apply (@data_at_data_at_ Cookie.CS Tsh t_skb);
  cancel.

#[local] Instance k0z_cce : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

Lemma k0z_skb_cs sh (dv lv pv: val) (a b c: list val) p :
  @data_at Cookie.CS sh t_skb (dv, (lv, (pv, (a, (b, c))))) p =
  @data_at W_handshake_receive sh t_skb (dv, (lv, (pv, (a, (b, c))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Cookie.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma k0z_skbd L dp lv proto ip4 ip6 port :
  0 <= proto <= 65535 -> Zlength ip4 = 4 -> Zlength ip6 = 16 -> Zlength port = 2 ->
  @data_at W_handshake_receive Tsh t_skb
    (dp, (lv, (Vint (Int.repr proto), (bytes ip4, (bytes ip6, bytes port))))) (l_skb L) |--
  hrx5_B3_skbd L dp proto ip4 ip6 port.
Proof.
  intros. unfold hrx5_B3_skbd. rewrite <- k0z_skb_cs. Exists lv. entailer!.
Qed.

Lemma k0z_obj_close (B: list byte) dp :
  @malloc_token W_handshake_receive Ews (tarray tuchar (Zlength B)) dp * hbytes Ews B dp |--
  obj_rep dp (OBuf B).
Proof. unfold obj_rep. rewrite k0z_bytes_hbytes. cancel. Qed.

Lemma k0z_img_close (B: list byte) img :
  @malloc_token W_handshake_receive Ews (tarray tuchar (Zlength B)) img * hbytes Ews B img |--
  img_rep img B.
Proof. unfold img_rep. cancel. Qed.

Section K0Z.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K0_Z_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M x25519 gv L FR) hrx5_K0_Z
    (overridePost (hrx5_B3_Q x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K0_M, hrx5_K0_Mc.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto.
  Intros ip4 ip6 port B dp.
  unfold hrx5_K0_Z, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  assert (HB: 0 <= Zlength B <= Int.max_unsigned) by (pose proof (Zlength_nonneg B); simpl in H3; lia).
  assert (Hdp: isptr dp) by (destruct dp; try contradiction; exact I).
  forward_call (tarray tuchar (Zlength B), gv).
  { simpl. rep_lia. }
  Intros img.
  destruct (eq_dec img nullval) as [Himg|Himg].
  { (* NULL: free(buf); continue *)
    subst img.
    forward_if; [| exfalso; auto].
    sep_apply (k0z_obj_open B dp).
    forward_call (tarray tuchar (Zlength B), dp, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    match goal with |- _ |-- RA_continue ?X => change (RA_continue X) with (hrx5_SC x25519 gv L FR) end.
    k0z_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1. }
  try rewrite if_false by exact Himg. Intros.
  forward_if; [contradiction |].
  unfold obj_rep. rewrite k0z_bytes_hbytes.
  assert (Ho: @data_at_ W_handshake_receive Ews (tarray tuchar (Zlength B)) img = hout Ews (Zlength B) img)
    by (unfold hout; apply k0z_tuchar_cs_).
  rewrite Ho; clear Ho. flatten_sepcon_in_SEP.
  forward_call (Ews, img, Ews, dp, B).
  unfold hrx5_skb_part. Intros dv lv.
  rewrite k0z_skb_cs.
  forward.
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_B3_Q x25519 gv L FR) end.
  sep_apply (k0z_skbd L dp lv proto ip4 ip6 port H6 H7 H8 H9).
  sep_apply (k0z_obj_close B dp).
  sep_apply (k0z_img_close B img).
  unfold hrx5_B3_Q.
  Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port (OBuf B) dp img.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_ptrs; cbn [app obj_bytes obj_kind].
  go_lower. apply andp_right.
  { apply prop_right. refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj H4 _)))))).
    repeat split; auto. }
  cancel.
Qed.

End K0Z.
