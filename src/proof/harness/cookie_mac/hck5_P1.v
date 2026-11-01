(* law cookie_mac: main's phase P1, statements 0..19 of hck5_cut.v:
   v1 P1 (hck3_P1.v.old) + statement 7 (v2): CHECK(bytes_eq(wb.cookie_checker.secret, wg_shim_random_log, 32) && wb.cookie_checker.secret_birthdate == wg_shim_boottime_ns).
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
Require Import WgNoise.proof.harness.cookie_mac.hck5_p1_lemmas.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Section P1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P1_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S0 gv L FR) hck5_P1
    (overridePost (hck5_S1 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S0, hck5_Delta, hck5_R, hck5_P1. simplify_func_tycontext. abbreviate_semax.
  unfold hck5_lvars, hck5_snaps0.
  forward.
  forward_call tt. Intros boot. unfold shim_state4 at 1. unfold shim_core at 1. Intros. unfold hck5_shim0 at 1. cbn [s_boot].
  rewrite (@hck5_p1_tulong_cs Noise.CS W_cookie_mac _ _ (gv _wg_shim_boottime_ns)).
  change _wg_shim_boottime_ns with HK._wg_shim_boottime_ns. forward.
  rewrite (@hck5_p1_tulong_cs W_cookie_mac Noise.CS _ _ (gv HK._wg_shim_boottime_ns)).
  change HK._wg_shim_boottime_ns with _wg_shim_boottime_ns.
  sep_apply (hck5_p1_shim_fold gv (hck5_p1_set_boot hck5_shim0 boot) H0).
  assert (FS: forall S, shim_core gv S * refwarn4 gv hck5_w0 |-- shim_state4 gv S hck5_w0)
    by (intros; unfold shim_state4; cancel).
  sep_apply FS.
  forward_call (gv, zeros32, zeros32, Int64.zero).
  rewrite !hck5_conv_bytes.
  forward_call (l_rawa L, 32, Tsh). Intros bsA.
  forward_call (l_rawb L, 32, Tsh). Intros bsB.
  rewrite (hck5_p1_nd _ _ _ _ H1 H2), (hck5_p1_nd _ _ _ _ H3 H4).
  assert (LA: Zlength (map Byte.repr bsA) = 32) by (rewrite Zlength_map; auto).
  assert (LB: Zlength (map Byte.repr bsB) = 32) by (rewrite Zlength_map; auto).
  forward_call (gv, hck5_p1_set_boot hck5_shim0 boot, hck5_w0, Tsh, l_wa L, l_ita L, l_pta L, Tsh, l_rawa L, map Byte.repr bsA).
  Intros secA.
  forward_call (gv, shim_draw (hck5_p1_set_boot hck5_shim0 boot) secA, hck5_w0, Tsh, l_wb L, l_itb L, l_ptb L, Tsh, l_rawb L, map Byte.repr bsB).
  Intros secB.
  change (s_boot (hck5_p1_set_boot hck5_shim0 boot)) with boot.
  change (s_boot (shim_draw (hck5_p1_set_boot hck5_shim0 boot) secA)) with boot.
  unfold hck5_consts. repeat flatten_sepcon_in_SEP.
  set (RA := map Byte.repr bsA) in *. set (RB := map Byte.repr bsB) in *.
  set (DA := setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) RA secA boot).
  set (DB := setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) RB secB boot).
  rewrite (hck5_p1_dev_split Tsh (l_wb L) DB). unfold hck5_drest. Intros.
  rename H7 into FCB.
  rewrite (hck5_p1_cc_open Tsh (l_wb L)) by exact FCB. Intros.
  rename H7 into HccB.
  set (S2 := shim_draw (shim_draw (hck5_p1_set_boot hck5_shim0 boot) secA) secB).
  unfold shim_state4 at 1. rewrite hck5_p1_shim_open. Intros. rename H7 into HS2.
  assert (LG: s_log S2 = secB) by (apply hck5_p1_draw_log; assumption).
  rewrite LG.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { assert (EsB: cc_secret (d_cc DB) = secB) by reflexivity. rewrite EsB.
    forward_call (Tsh, cc_addr (l_wb L), secB, Ews, gv _wg_shim_random_log, secB).
    { entailer!. simpl. rewrite H6. unfold cc_addr. destruct (l_wb L); try contradiction; simpl.
      unfold OFS_DEV_CHECKER. rewrite Ptrofs.add_zero. reflexivity. }
    rewrite hck5_p1_eqb_refl.
    forward_if (temp HK._t'3 (Vint Int.one)).
    { unfold hck5_p1_shrest. Intros.
      rewrite (@hck5_p1_tulong_cs Noise.CS W_cookie_mac _ _ (gv _wg_shim_boottime_ns)).
      change _wg_shim_boottime_ns with HK._wg_shim_boottime_ns. forward. forward. forward.
      rewrite (@hck5_p1_tulong_cs W_cookie_mac Noise.CS _ _ (gv HK._wg_shim_boottime_ns)).
      change HK._wg_shim_boottime_ns with _wg_shim_boottime_ns.
      entailer!.
      { change (cc_birth (d_cc DB)) with boot. change (s_boot S2) with boot. unfold Int64.cmpu.
        rewrite Int64.eq_true. reflexivity. }
      unfold hck5_p1_shrest. cancel. }
    { exfalso. exact (Int.one_not_zero H7). }
    forward_if. { discriminate. } forward. entailer!. rewrite EsB. apply derives_refl. }
  { forward. apply ENTAIL_refl. }
  gather_SEP (hbytes Ews secB (gv _wg_shim_random_log)) (hck5_p1_shrest gv S2).
  replace_SEP 0 (shim_core gv S2).
  { entailer!. rewrite hck5_p1_shim_open, LG. entailer!. }
  sep_apply (FS S2). clear FS.
  rename FCB into H7. rename HccB into H9.
  forward_call (gv, Tsh, l_ib L, Tsh, l_rawb L, RB).
  set (IB := mident_of x25519 RB).
  rewrite hck5_p1_mident_W. forward. rewrite <- hck5_p1_mident_W.
  rewrite (hck5_p1_id_open Tsh (id_addr (l_wb L))). Intros.
  change (let (_, y) := let (_, y) := mident_val IB in y in y) with (Vint (if mi_ok IB then Int.one else Int.zero)).
  assert (HokB: mi_ok IB = id_has (d_id DB)) by reflexivity.
  assert (LpubB: Zlength (id_pub (d_id DB)) = 32) by apply H8.
  pose proof H9 as (LsB & LeB & LmB).
  unfold wg_consts. Intros.
  change (hc_const gv HK._x_cookie_mac__M_LABEL_MAC1 mac1_label) with (hbytes Ers mac1_label (gv HK._x_cookie_mac__M_LABEL_MAC1)).
  change (hc_const gv HK._x_cookie_mac__M_LABEL_COOKIE cookie_label) with (hbytes Ers cookie_label (gv HK._x_cookie_mac__M_LABEL_COOKIE)).
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { assert (Eok: mi_ok IB = true).
    { change (memneq_bool RB zeros32 && memneq_bool (x25519 RB basepoint9) zeros32)%bool with (mi_ok IB) in H10.
      destruct (mi_ok IB); [reflexivity | contradiction H10; reflexivity]. }
    assert (EkM: cc_mkey (d_cc DB) = label_key mac1_label (id_pub (d_id DB))).
    { unfold DB, setup_dev, checker_keys. cbn [d_cc cc_mkey d_id]. fold (setup_identity x25519 RB).
      change (id_has (setup_identity x25519 RB)) with (mi_ok IB). rewrite Eok. reflexivity. }
    assert (EkC: cc_ekey (d_cc DB) = label_key cookie_label (id_pub (d_id DB))).
    { unfold DB, setup_dev, checker_keys. cbn [d_cc cc_ekey d_id]. fold (setup_identity x25519 RB).
      change (id_has (setup_identity x25519 RB)) with (mi_ok IB). rewrite Eok. reflexivity. }
    rewrite <- (hck5_conv_bytes Tsh 32 (l_k L)).
    rewrite (hck5_p1_ers_split (id_pub (d_id DB))). Intros.
    forward_call (gv, Tsh, l_k L, Ers, gv HK._x_cookie_mac__M_LABEL_MAC1, mac1_label, id_addr (l_wb L), id_pub (d_id DB)).
    assert (EqM: bytes_eqb (cc_mkey (d_cc DB)) (label_key mac1_label (id_pub (d_id DB))) = true)
      by (rewrite EkM; apply hck5_p1_eqb_refl).
    assert (EqC: bytes_eqb (cc_ekey (d_cc DB)) (label_key cookie_label (id_pub (d_id DB))) = true)
      by (rewrite EkC; apply hck5_p1_eqb_refl).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_call (Tsh, offset_val 64 (cc_addr (l_wb L)), cc_mkey (d_cc DB), Tsh, l_k L,
                    label_key mac1_label (id_pub (d_id DB))).
      { rewrite LmB. entailer!. }
      rewrite EqM.
      forward_if. { discriminate. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    sep_apply (hck5_p1_hbytes_out Tsh (label_key mac1_label (id_pub (d_id DB))) (l_k L)).
    rewrite hck5_p1_label_len.
    forward_call (gv, Tsh, l_k L, Ers, gv HK._x_cookie_mac__M_LABEL_COOKIE, cookie_label, id_addr (l_wb L), id_pub (d_id DB)).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_call (Tsh, offset_val 32 (cc_addr (l_wb L)), cc_ekey (d_cc DB), Tsh, l_k L,
                    label_key cookie_label (id_pub (d_id DB))).
      { rewrite LeB. entailer!. }
      rewrite EqC.
      forward_if. { discriminate. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    sep_apply (hck5_hbytes_free Tsh (label_key cookie_label (id_pub (d_id DB))) (l_k L)).
    rewrite hck5_p1_label_len.
    sep_apply (derives_refl' _ _ (eq_sym (hck5_p1_ers_split (id_pub (d_id DB)) (id_addr (l_wb L))))).
    unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!. apply derives_refl.
  }
  { assert (Eok: mi_ok IB = false).
    { change (memneq_bool RB zeros32 && memneq_bool (x25519 RB basepoint9) zeros32)%bool with (mi_ok IB) in H10.
      destruct (mi_ok IB); [contradiction Int.one_not_zero | reflexivity]. }
    assert (EzM: is_zero (cc_mkey (d_cc DB)) = true).
    { unfold DB, setup_dev, checker_keys. cbn [d_cc cc_mkey d_id]. fold (setup_identity x25519 RB).
      change (id_has (setup_identity x25519 RB)) with (mi_ok IB). rewrite Eok. reflexivity. }
    assert (EzC: is_zero (cc_ekey (d_cc DB)) = true).
    { unfold DB, setup_dev, checker_keys. cbn [d_cc cc_ekey d_id]. fold (setup_identity x25519 RB).
      change (id_has (setup_identity x25519 RB)) with (mi_ok IB). rewrite Eok. reflexivity. }
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_call (Tsh, offset_val 64 (cc_addr (l_wb L)), cc_mkey (d_cc DB)).
      { rewrite LmB. entailer!. }
      rewrite EzM.
      forward_if (temp HK._t'7 (Vint Int.one)).
      { forward_call (Tsh, offset_val 32 (cc_addr (l_wb L)), cc_ekey (d_cc DB)).
        { rewrite LeB. entailer!. }
        rewrite EzC. forward. entailer!. }
      { discriminate. }
      forward_if. { discriminate. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!. apply derives_refl. }
  unfold hck5_p1_ccrest. Intros lkc.
  change (cc_dev (d_cc DB)) with (l_wb L).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    { rewrite (field_at_data_at Tsh t_dev (DOT hc_prog3.I._dev)).
      rewrite field_address_offset by auto with field_compatible. simpl.
      rewrite isptr_offset_val_zero by auto. entailer!. }
    { assert_PROP (isptr (l_wb L)) as Pw by entailer!. destruct (l_wb L); try contradiction.
      unfold sem_cmp_pp in H10. simpl in H10. destruct (eq_block b b); [|congruence].
      rewrite Ptrofs.eq_true in H10. unfold typed_true in H10. simpl in H10. discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hck5_hbytes_free Tsh (cc_secret (d_cc DB)) (cc_addr (l_wb L))). rewrite LsB.
  forward_call (cc_addr (l_wb L), 32, Tsh). Intros bsS.
  rewrite (hck5_p1_nd _ _ _ _ H10 H11).
  forward_call tt. Intros birth.
  forward.
  forward_call tt. Intros u8.
  forward.
  { entailer!. match goal with X: _ /\ Int.repr 4 = Int.mone |- _ => destruct X as [_ X]; discriminate X end. }
  set (hb := negb (Int.eq (Int.mods (Int.repr u8) (Int.repr 4)) (Int.repr 0))).
  replace (Vint (Int.repr (Z.b2z hb))) with (Vint (if hb then Int.one else Int.zero)) by (destruct hb; reflexivity).
  rewrite <- (hck5_conv_bytes Tsh 32 (l_pub L)).
  gather_SEP (hout Tsh 32 (l_pub L)).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    forward_if (EX PUB: list byte,
      PROPx [Zlength PUB = 32; hb = true -> PUB = id_pub (d_id DB)]
      (LOCALx Q (SEPx (hbytes Tsh PUB (l_pub L) :: R)))) end.
  { replace (hout Tsh 32 (l_pub L)) with (hout Tsh (Zlength (id_pub (d_id DB))) (l_pub L)) by (rewrite LpubB; reflexivity).
    forward_call (Tsh, l_pub L, Tsh, id_addr (l_wb L), id_pub (d_id DB)).
    { rewrite LpubB. entailer!. simpl. unfold id_addr, OFS_DEV_IDENTITY.
      destruct (l_wb L); try contradiction; simpl. rewrite Ptrofs.add_zero. reflexivity. }
    Exists (id_pub (d_id DB)). entailer!. }
  { rewrite hck5_conv_bytes. forward_call (l_pub L, 32, Tsh). Intros bsP.
    rewrite (hck5_p1_nd _ _ _ _ H15 H16).
    Exists (map Byte.repr bsP). entailer!.
    split; [rewrite Zlength_map; auto |].
    intros E. rewrite E in H14. contradiction (Int.one_not_zero H14). }
  Intros PUB.
  rename H14 into LPUB. rename H15 into HPUB.
  change (ptable Tsh (l_pta L) nullval) with (ptable Tsh (d_ptab DA) nullval).
  gather_SEP (blake2s_globals gv) (curve25519_globals gv) (zero_page gv) (cookie_globals gv).
  fold (wg_consts gv).
  forward_call (gv, Tsh, l_p L, Tsh, l_wa L, DA, nullval, Tsh, l_pub L, PUB, nullval, zeros32, Int64.repr 1).
  { rewrite if_true by reflexivity. rewrite emp_sepcon. cancel. }
  rewrite !if_true by reflexivity.
  set (P0 := setup_peer_val x25519 DA (l_wa L) (l_p L) nullval PUB zeros32 (Int64.repr 1)).
  rewrite (hck5_p1_peer_split Tsh (l_p L) P0).
  rewrite (hck5_p1_ck_open Tsh (cookie_addr (l_p L)) (p_cookie P0)). Intros.
  rewrite <- (hck5_conv_bytes Tsh 32 (l_k L)).
  rewrite (hck5_p1_ers_split PUB). unfold wg_consts. Intros.
  forward_call (gv, Tsh, l_k L, Ers, gv HK._x_cookie_mac__M_LABEL_MAC1, mac1_label, l_pub L, PUB).
  assert (EqPM: bytes_eqb (ck_mkey (p_cookie P0)) (label_key mac1_label PUB) = true) by apply hck5_p1_eqb_refl.
  assert (EqPC: bytes_eqb (ck_dkey (p_cookie P0)) (label_key cookie_label PUB) = true) by apply hck5_p1_eqb_refl.
  assert (LcM: Zlength (ck_mkey (p_cookie P0)) = 32) by apply hck5_p1_label_len.
  assert (LcD: Zlength (ck_dkey (p_cookie P0)) = 32) by apply hck5_p1_label_len.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 74 (cookie_addr (l_p L)), ck_mkey (p_cookie P0), Tsh, l_k L,
                  label_key mac1_label PUB).
    rewrite EqPM.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hck5_p1_hbytes_out Tsh (label_key mac1_label PUB) (l_k L)).
  rewrite hck5_p1_label_len.
  forward_call (gv, Tsh, l_k L, Ers, gv HK._x_cookie_mac__M_LABEL_COOKIE, cookie_label, l_pub L, PUB).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 42 (cookie_addr (l_p L)), ck_dkey (p_cookie P0), Tsh, l_k L,
                  label_key cookie_label PUB).
    rewrite EqPC.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hck5_p1_hbytes_out Tsh (label_key cookie_label PUB) (l_k L)). rewrite hck5_p1_label_len.
  sep_apply (derives_refl' _ _ (eq_sym (hck5_p1_ers_split PUB (l_pub L)))).
  sep_apply (hck5_p1_ck_close Tsh (cookie_addr (l_p L)) (p_cookie P0) H14).
  sep_apply (hck5_p1_id_close Tsh (id_addr (l_wb L)) (d_id DB) H8).
  sep_apply (hck5_p1_drest_fold Tsh (l_wb L) DB H7).
  sep_apply (hck5_p1_ccrest_fold Tsh (l_wb L) (l_wb L) lkc).
  set (CC1 := mkChk (map Byte.repr bsS) (cc_ekey (d_cc DB)) (cc_mkey (d_cc DB)) birth (l_wb L)).
  assert (HCC1: cc_ok CC1) by (split; [unfold CC1; simpl; rewrite Zlength_map; auto | split; auto]).
  change (hbytes Tsh (map Byte.repr bsS) (cc_addr (l_wb L))) with (hbytes Tsh (cc_secret CC1) (cc_addr (l_wb L))).
  change (hbytes Tsh (cc_ekey (d_cc DB))) with (hbytes Tsh (cc_ekey CC1)).
  change (hbytes Tsh (cc_mkey (d_cc DB))) with (hbytes Tsh (cc_mkey CC1)).
  change (Vlong birth) with (Vlong (cc_birth CC1)).
  change (hck5_p1_ccrest Tsh (l_wb L) (l_wb L)) with (hck5_p1_ccrest Tsh (l_wb L) (cc_dev CC1)).
  sep_apply (hck5_p1_cc_close Tsh (l_wb L) CC1 H7 HCC1).
  gather_SEP (blake2s_globals gv) (curve25519_globals gv) (zero_page gv) (cookie_globals gv).
  fold (wg_consts gv).
  change (hbytes Ers mac1_label (gv HK._x_cookie_mac__M_LABEL_MAC1)) with (hc_const gv HK._x_cookie_mac__M_LABEL_MAC1 mac1_label).
  change (hbytes Ers cookie_label (gv HK._x_cookie_mac__M_LABEL_COOKIE)) with (hc_const gv HK._x_cookie_mac__M_LABEL_COOKIE cookie_label).
  change (ptable Tsh (d_ptab DA) (l_p L)) with (ptable Tsh (l_pta L) (l_p L)).
  rewrite <- !hck5_conv_bytes.
  unfold POSTCONDITION, abbreviate. simpl RA_normal.
  unfold hck5_S1.
  Exists (mkRun5 RA RB secA secB boot (map Byte.repr bsS) birth hb PUB) S2.
  unfold hck5_aside1, hck5_snaps0, hck5_bside, hck5_bufs, hck5_scr, hck5_globs, hck5_consts, hck5_lvars.
  cbn [app r_rawa r_rawb r_seca r_secb r_boot0 r_secret r_birth r_honest r_pub].
  change (hck5_DA x25519 _ L) with DA. change (hck5_DB x25519 _ L) with DB.
  change (hck5_P0 x25519 _ L) with P0. change (hck5_CC1 x25519 _ L) with CC1.
  change (hck5_C0 _) with (p_cookie P0).
  entailer!.
  refine (conj LA (conj LB (conj H5 (conj H6 (conj _ (conj LPUB (conj H (conj H12 HPUB)))))))).
  simpl; rewrite Zlength_map; auto.
Qed.

End P1.
