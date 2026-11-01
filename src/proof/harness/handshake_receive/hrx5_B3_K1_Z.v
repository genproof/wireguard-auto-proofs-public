(* law handshake_receive, B3 kind 1: segment Z (hrx5_B3_K1_defs.v). *)
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
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K1_defs.
Local Open Scope logic.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.

(* ---------------------------------------------------------------------- *)
(* helpers *)
(* ---------------------------------------------------------------------- *)

(* byte arrays are the same in every compspecs *)
Lemma k1z_align_tuchar_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuchar n) z -> align_compatible_rec ce2 (tarray tuchar n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros j Hj.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hj].
  inv H. econstructor; eauto.
Qed.

Lemma k1z_fc_tuchar_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (k1z_align_tuchar_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (k1z_align_tuchar_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma k1z_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply k1z_fc_tuchar_cs.
Qed.

Lemma k1z_bytes_hbytes sh (B: list byte) p : bytes_at sh B p = hbytes sh B p.
Proof. unfold bytes_at, hbytes. apply k1z_tuchar_cs. Qed.

(* a 148-byte buffer as 116 ++ 16 ++ 16 *)
Lemma k1z_split3 sh (l: list byte) p :
  Zlength l = 148 -> @field_compatible Noise.CS (tarray tuchar 148) [] p ->
  hbytes sh l p =
  hbytes sh (sublist 0 116 l) p * hbytes sh (sublist 116 132 l) (offset_val 116 p) *
  hbytes sh (sublist 132 148 l) (offset_val 132 p).
Proof.
  intros HL FC.
  rewrite <- !k1z_bytes_hbytes.
  assert (E: l = sublist 0 116 l ++ sublist 116 132 l ++ sublist 132 148 l).
  { rewrite sublist_rejoin by lia. rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. }
  assert (LA: Zlength (sublist 0 116 l) = 116) by (rewrite Zlength_sublist; lia).
  assert (LB: Zlength (sublist 116 132 l) = 16) by (rewrite Zlength_sublist; lia).
  assert (LC: Zlength (sublist 132 148 l) = 16) by (rewrite Zlength_sublist; lia).
  set (A := sublist 0 116 l) in *. set (B := sublist 116 132 l) in *. set (C := sublist 132 148 l) in *.
  clearbody A B C. subst l.
  rewrite prot_rep3_bytes_app.
  2:{ rewrite LA, Zlength_app, LB, LC. exact FC. }
  rewrite LA.
  rewrite (prot_rep3_bytes_app_at sh B C p 116 132 16 16).
  - rewrite sepcon_assoc. reflexivity.
  - auto.
  - auto.
  - lia.
  - destruct FC as (? & ? & ? & ? & ?). destruct p; try contradiction.
    unfold field_compatible, size_compatible, align_compatible in *; simpl in *.
    split; [auto|]. split; [reflexivity|]. split.
    + rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr; rewrite ?Ptrofs.unsigned_repr; rep_lia.
    + split; [| split; auto].
      apply align_compatible_rec_Tarray. intros j Hj.
      eapply align_compatible_rec_Tarray_inv with (i := j + 116) in H2; [| lia].
      inv H2. econstructor; eauto. simpl in *.
      match goal with HC: By_value Mint8unsigned = By_value _ |- _ => inv HC end.
      apply Z.divide_1_l.
Qed.

(* the message with the image's macs *)
Definition k1z_M (M: init_msg) (IMG: list byte) : init_msg :=
  mkIM (im_type M) (im_sender M) (im_eph M) (im_encs M) (im_enct M) (sublist 116 132 IMG) (sublist 132 148 IMG).

Lemma k1z_M_ok M IMG : im_ok M -> Zlength IMG = 148 -> im_ok (k1z_M M IMG).
Proof.
  intros (? & ? & ? & ? & ?) HL. unfold im_ok, k1z_M; cbn [im_eph im_encs im_enct im_mac1 im_mac2].
  rewrite !Zlength_sublist by lia. lia.
Qed.

Lemma k1z_init_bytes_pre M : im_ok M ->
  sublist 0 116 (init_bytes M) =
  le32 (im_type M) ++ le32 (im_sender M) ++ im_eph M ++ im_encs M ++ im_enct M.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). unfold init_bytes.
  rewrite !app_assoc.
  rewrite sublist_app1 by (rewrite ?Zlength_app, ?prot_rep3_le32_len; lia).
  rewrite sublist_app1 by (rewrite ?Zlength_app, ?prot_rep3_le32_len; lia).
  rewrite sublist_same by (rewrite ?Zlength_app, ?prot_rep3_le32_len; lia).
  rewrite ?app_assoc. reflexivity.
Qed.

Lemma k1z_M_bytes M IMG :
  im_ok M -> Zlength IMG = 148 -> sublist 0 116 IMG = sublist 0 116 (init_bytes M) ->
  init_bytes (k1z_M M IMG) = IMG.
Proof.
  intros OK HL HS.
  pose proof (k1z_init_bytes_pre M OK) as HP.
  unfold init_bytes, k1z_M; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
  transitivity ((le32 (im_type M) ++ le32 (im_sender M) ++ im_eph M ++ im_encs M ++ im_enct M) ++
                 sublist 116 132 IMG ++ sublist 132 148 IMG).
  { rewrite <- !app_assoc. reflexivity. }
  rewrite <- HP, <- HS.
  rewrite sublist_rejoin by lia. rewrite sublist_rejoin by lia.
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma k1z_fc148 p : malloc_compatible 148 p -> @field_compatible Noise.CS (tarray tuchar 148) [] p.
Proof. intros H. apply malloc_compatible_field_compatible; auto. Qed.

Lemma k1z_fcinit p : malloc_compatible 148 p -> @field_compatible Noise.CS t_init [] p.
Proof. intros H. apply malloc_compatible_field_compatible; auto. Qed.

(* mi opened for the two copies *)
Lemma k1z_mi_open M IMG mi :
  malloc_compatible 148 mi -> im_ok M -> sublist 0 116 IMG = sublist 0 116 (init_bytes M) ->
  init_rep Ews mi M |--
  hbytes Ews (sublist 0 116 IMG) mi * hout Ews 16 (offset_val 116 mi) * hout Ews 16 (offset_val 132 mi).
Proof.
  intros MC OK HS. unfold init_rep. Intros.
  rewrite prot_rep3_init_eq by (auto; apply k1z_fcinit; auto).
  rewrite k1z_bytes_hbytes.
  assert (HL: Zlength (init_bytes M) = 148).
  { destruct OK as (? & ? & ? & ? & ?). unfold init_bytes. rewrite !Zlength_app, !prot_rep3_le32_len. lia. }
  rewrite (k1z_split3 Ews (init_bytes M) mi HL (k1z_fc148 mi MC)).
  rewrite HS. unfold hout, hbytes.
  rewrite !Zlength_sublist by lia.
  replace (132 - 116) with 16 by lia. replace (148 - 132) with 16 by lia.
  cancel.
Qed.

Lemma k1z_mi_close M IMG mi :
  malloc_compatible 148 mi -> im_ok M -> Zlength IMG = 148 ->
  sublist 0 116 IMG = sublist 0 116 (init_bytes M) ->
  hbytes Ews (sublist 0 116 IMG) mi * hbytes Ews (sublist 116 132 IMG) (offset_val 116 mi) *
  hbytes Ews (sublist 132 148 IMG) (offset_val 132 mi) |--
  init_rep Ews mi (k1z_M M IMG).
Proof.
  intros MC OK HL HS. unfold init_rep. apply andp_right.
  { apply prop_right. apply k1z_M_ok; auto. }
  rewrite prot_rep3_init_eq by (auto using k1z_M_ok, k1z_fcinit).
  rewrite k1z_M_bytes by auto. rewrite k1z_bytes_hbytes.
  rewrite (k1z_split3 Ews IMG mi HL (k1z_fc148 mi MC)). cancel.
Qed.

Lemma k1z_ptr_sub (oi: ptrofs) (a b: Z) :
  Ptrofs.sub (Ptrofs.add oi (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr 148))))
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 32))) = Ptrofs.add oi (Ptrofs.repr 116) /\
  Ptrofs.sub (Ptrofs.add oi (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr 148))))
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 16))) = Ptrofs.add oi (Ptrofs.repr 132).
Proof.
  split; rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc; f_equal; apply Ptrofs.same_if_eq; vm_compute; reflexivity.
Qed.

#[local] Instance k1z_cce : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

Lemma k1z_skb_cs sh (dv lv pv: val) (a b c: list val) p :
  @data_at Cookie.CS sh t_skb (dv, (lv, (pv, (a, (b, c))))) p =
  @data_at W_handshake_receive sh t_skb (dv, (lv, (pv, (a, (b, c))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Cookie.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma k1z_skbd L dp lv proto ip4 ip6 port :
  0 <= proto <= 65535 -> Zlength ip4 = 4 -> Zlength ip6 = 16 -> Zlength port = 2 ->
  @data_at W_handshake_receive Tsh t_skb (dp, (lv, (Vint (Int.repr proto), (bytes ip4, (bytes ip6, bytes port)))))
    (l_skb L) |-- hrx5_B3_skbd L dp proto ip4 ip6 port.
Proof.
  intros. unfold hrx5_B3_skbd. rewrite <- k1z_skb_cs. Exists lv. entailer!.
Qed.

Section K1Z.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K1_Z_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K1_C x25519 gv L FR) hrx5_K1_SZ
    (overridePost (hrx5_B3_Q x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K1_C, hrx5_K1_St.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto.
  Intros ip4 ip6 port mi img M IMG.
  unfold hrx5_K1_SZ, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  unfold hrx5_K1_XM.
  sep_apply (k1z_mi_open M IMG mi H3 H4 H6).
  assert_PROP (@field_compatible Noise.CS (tarray tuchar 148) [] img) as FCimg.
  { unfold hbytes. rewrite H5. entailer!. }
  rewrite (k1z_split3 Ews IMG img H5 FCimg).
  pose proof FCimg as FCimg0.
  assert (Pmi: isptr mi) by (destruct mi; try contradiction; exact I).
  destruct FCimg as [Pimg FCimg'].
  destruct mi as [| | | | | bm om]; try contradiction. destruct img as [| | | | | bi oi]; try contradiction.
  pose proof (k1z_ptr_sub oi 0 0) as [PS1 PS2].
  forward_call (Ews, offset_val 116 (Vptr bm om), Ews, offset_val 116 (Vptr bi oi), sublist 116 132 IMG).
  { go_lower. apply prop_right. simpl. rewrite Zlength_sublist by lia. rewrite PS1, Ptrofs.add_zero. reflexivity. }
  { rewrite Zlength_sublist by lia. replace (132 - 116) with 16 by lia. cancel. }
  { rewrite Zlength_sublist by lia. rep_lia. }
  forward_call (Ews, offset_val 132 (Vptr bm om), Ews, offset_val 132 (Vptr bi oi), sublist 132 148 IMG).
  { go_lower. apply prop_right. simpl. rewrite Zlength_sublist by lia. rewrite PS2, Ptrofs.add_assoc, ptrofs_add_repr. reflexivity. }
  { rewrite Zlength_sublist by lia. replace (148 - 132) with 16 by lia. cancel. }
  { rewrite Zlength_sublist by lia. rep_lia. }
  unfold hrx5_skb_part. Intros dv lv. rewrite k1z_skb_cs.
  forward.
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_B3_Q x25519 gv L FR) end.
  sep_apply (k1z_mi_close M IMG (Vptr bm om) H3 H4 H5 H6).
  sep_apply (derives_refl' _ _ (eq_sym (k1z_split3 Ews IMG (Vptr bi oi) H5 FCimg0))).
  sep_apply (k1z_skbd L (Vptr bm om) lv proto ip4 ip6 port H7 H8 H9 H10).
  unfold hrx5_B3_Q.
  Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port (OInit (k1z_M M IMG)) (Vptr bm om) (Vptr bi oi).
  unfold obj_rep, img_rep, obj_bytes, obj_kind, hrx5_ptrs, obj_ok.
  rewrite (k1z_M_bytes M IMG H4 H5 H6), H5.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  go_lower. apply andp_right.
  { apply prop_right.
    refine (conj H (conj H0 (conj H1 (conj H2 (conj (k1z_M_ok M IMG H4 H5) (conj H3 _)))))).
    repeat split; auto. }
  cancel.
Qed.

End K1Z.
