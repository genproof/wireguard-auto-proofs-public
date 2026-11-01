(* law cookie_reply: phase P11, segment C (statement 69): the decryption and the CHECK of the accepted peer's cookie.
   cookie_reply/hcy4_p11_C.v. *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_C_lemmas.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Ltac hcy5_p11_C_dead :=
  exfalso;
  first
  [ match goal with Hf: ?x <> ?x |- _ => exact (Hf eq_refl) end
  | match goal with Hf: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hf) end
  | match goal with Hf: Int.zero = Int.one |- _ => exact (Int.one_not_zero (eq_sym Hf)) end
  | discriminate | congruence ].

(* hcy5_p11_C_cn_close with the snapshot's rest unfolded (VST unfolds it) *)
Lemma hcy5_p11_C_cn_close' C c nd b X :
  cookie_ok C -> @field_compatible W t_cnode5 [] c -> ck_sent C = b ->
  (@field_at W Ews t_cnode5 (DOT HY._n) nd c *
   @field_at W Ews t_cnode5 (DOT HY._cs DOT HY._have_sent_mac1) (Val.of_bool b) c *
   hbytes Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 c)) *
   hbytes Ews (ck_dkey C) (offset_val 42 (offset_val 8 c)) *
   hbytes Ews (ck_mkey C) (offset_val 74 (offset_val 8 c)) *
   @field_at CKS Ews t_cksnap (DOT HY._birthdate) (Vlong (ck_birth C)) (offset_val 8 c) *
   @field_at CKS Ews t_cksnap (DOT HY._is_valid) (Val.of_bool (ck_valid C)) (offset_val 8 c) *
   hbytes Ews (ck_cookie C) (offset_val 9 (offset_val 8 c)) *
   spacer Ews 106 112 (offset_val 8 c) *
   (hcy5_p11_C_cn1 c nd (Some C) -* X) |-- X)%logic.
Proof.
  intros Hok FC Hb. eapply derives_trans; [| apply (hcy5_p11_C_cn_close C c nd b X Hok FC Hb)].
  unfold hcy5_p11_C_snrest. cancel.
Qed.

Lemma hcy5_p11_C_pout sh bs p : 0 < Zlength bs -> @WgNoise.proof.protocol.prot_dec3.prim_out W sh (map Vubyte bs) p = hbytes sh bs p.
Proof.
  intros Hl. unfold WgNoise.proof.protocol.prot_dec3.prim_out. rewrite Zlength_map, if_false by lia. rewrite hcy5_p11_C_hW. reflexivity.
Qed.

Lemma hcy5_p11_C_cm_fold sh rp CM : cm_ok CM -> @field_compatible W t_cmsg [] rp ->
  (@field_at W sh t_cmsg (DOT HY._header DOT HY._type) (Vint (cm_type CM)) rp *
   @field_at W sh t_cmsg (DOT HY._receiver_index) (Vint (cm_receiver CM)) rp *
   hbytes sh (cm_nonce CM) (offset_val 8 rp) * hbytes sh (cm_enc CM) (offset_val 32 rp) |-- cmsg_rep sh rp CM)%logic.
Proof. intros Hok FC. rewrite hcy5_p11_C_cm_open. unfold hcy5_p11_C_cm. entailer!. Qed.

(* the accepted peer's cookie at the world, with explicit field values *)
Definition hcy5_p11_C_ckp (ca: val) (b: int64) (v: bool) (ck: list byte) (s: bool) (lm dk mk: list byte) (lk: val)
  : mpred :=
  (@field_at W Ews hcy5_p11_C_tck (DOT HY._birthdate) (Vlong b) ca *
   @field_at W Ews hcy5_p11_C_tck (DOT HY._is_valid) (Val.of_bool v) ca *
   hbytes Ews ck (offset_val 9 ca) *
   @field_at W Ews hcy5_p11_C_tck (DOT HY._have_sent_mac1) (Val.of_bool s) ca *
   hbytes Ews lm (offset_val 26 ca) *
   hbytes Ews dk (offset_val 42 ca) *
   hbytes Ews mk (offset_val 74 ca) *
   spacer Ews 106 108 ca * @field_at W Ews hcy5_p11_C_tck (DOT HY._lock) lk ca)%logic.

Lemma hcy5_p11_C_ck_eq b v ck s lm dk mk lk ca :
  cookie_ok (mkCookie b v ck s lm dk mk) -> @field_compatible W hcy5_p11_C_tck [] ca ->
  @data_at Noise.CS Ews t_cookie (cookie_val (mkCookie b v ck s lm dk mk) lk) ca =
  hcy5_p11_C_ckp ca b v ck s lm dk mk lk.
Proof.
  intros Hok FC. rewrite (hcy5_p11_C_cookie_split Ews _ lk ca Hok).
  rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  unfold hcy5_p11_C_ckp. reflexivity.
Qed.

Lemma hcy5_p11_C_ck_open PS a P b v ck s lm dk mk :
  In (a, Ews, P) PS -> p_cookie P = mkCookie b v ck s lm dk mk ->
  peers_rep PS |--
  EX lk: val, !! (cookie_ok (mkCookie b v ck s lm dk mk) /\ @field_compatible W hcy5_p11_C_tck [] (cookie_addr a)) &&
   (hcy5_p11_C_ckp (cookie_addr a) b v ck s lm dk mk lk *
    (cookie_rep Ews (cookie_addr a) (mkCookie b v ck s lm dk mk) -* peers_rep PS)).
Proof.
  intros Hin HC.
  sep_apply (hcy5_p11_C_peer PS a Ews P Hin). rewrite HC.
  unfold cookie_rep at 1. Intros lk. Exists lk.
  rewrite (hcy5_p11_C_cookie_split Ews _ lk (cookie_addr a) H).
  assert_PROP (@field_compatible W hcy5_p11_C_tck [] (cookie_addr a)) as FC.
  { entailer!.
    match goal with Hf: field_compatible hcy5_p11_C_tck (DOT HY._birthdate) _ |- _ =>
      destruct Hf as (A1 & A2 & A3 & A4 & _) end.
    repeat split; auto. }
  rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  unfold hcy5_p11_C_ckp. apply andp_right; [apply prop_right; split; auto |].
  cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey]. simpl nested_field_offset. cancel.
Qed.

Lemma hcy5_p11_C_ck_close ca b v ck s lm dk mk lk X :
  cookie_ok (mkCookie b v ck s lm dk mk) -> @field_compatible W hcy5_p11_C_tck [] ca ->
  (hcy5_p11_C_ckp ca b v ck s lm dk mk lk * (cookie_rep Ews ca (mkCookie b v ck s lm dk mk) -* X) |-- X)%logic.
Proof.
  intros Hok FC.
  eapply derives_trans; [| apply (modus_ponens_wand (cookie_rep Ews ca (mkCookie b v ck s lm dk mk)) X)].
  apply sepcon_derives; [| apply derives_refl].
  unfold cookie_rep. Exists lk. rewrite (hcy5_p11_C_ck_eq b v ck s lm dk mk lk ca Hok FC). entailer!.
Qed.

Ltac hcy5_p11_C_fif t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t v :: Lc) (SEPx Sp))) end.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p11_C_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p11_TB x25519 xaead_enc xaead_dec gv L FR) hcy5_p11_sC
    (overridePost (hcy5_S11 x25519 xaead_enc xaead_dec gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p11_TB, hcy5_Delta, hcy5_R, hcy5_p11_sC. simplify_func_tycontext. abbreviate_semax.
  Intros R Sh m c rp Q nonce rr CK CM.
  Intros NS PS T np CL KE CM' honest now2.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  destruct (eq_dec (hcy5_p11_t0 NS CL T (cm_receiver CM')) nullval) as [Ht0 | Ht0].
  { (* no target *)
    rewrite Ht0.
    forward_if.
    { exfalso. first [discriminate | apply H8; reflexivity]. }
    forward.
    unfold hcy5_S11. Exists R Sh m c rp. Exists Q nonce rr CK CM. Exists NS PS T np CL. Exists KE CM' honest now2.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
    rewrite (hcy5_p11_agree0 xaead_dec NS CL T PS CM' now2 Ht0).
    entailer!. }
  destruct (hcy5_p11_agree xaead_dec L (map ke_addr KE) NS PS T CL CM' now2 H0 H3 H4 Ht0)
    as (a & E & P & nd & CL1 & CL2 & NS1 & N & NS2 & Hlk & Hsf & HCL & HNS & HNa & HNp & Hres & Htgt).
  set (t0 := hcy5_p11_t0 NS CL T (cm_receiver CM')) in *. clearbody t0.
  set (C := p_cookie P) in *.
  assert (Hcl := hcy5_p11_C_cn (hcy5_chead CL) CL1 t0 nd (Some C) CL2). rewrite <- HCL in Hcl.
  sep_apply Hcl. clear Hcl.
  unfold hcy5_p11_C_cn1 at 1. unfold hcy5_cs_rep. Intros.
  assert_PROP (cookie_ok C) as HCok.
  { sep_apply (hcy5_p11_C_snap_ok Ews C (offset_val 8 t0)). entailer!. }
  assert_PROP (@field_compatible W t_cnode5 [] t0) as FCt0.
  { entailer!. match goal with Hf: field_compatible t_cnode5 _ t0 |- _ => destruct Hf as (A1 & A2 & A3 & A4 & _) end.
    repeat split; auto. }
  assert (Pt0: isptr t0) by (destruct FCt0; auto).
  rewrite (hcy5_p11_C_snap_split C t0 HCok FCt0). Intros.
  forward_if.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_zero64; auto].
    repeat apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto. vm_compute. reflexivity. }
  2: { exfalso. contradiction. }
  assert (TCB: tc_val tbool (Val.of_bool (ck_sent C))) by (destruct (ck_sent C); hnf; auto).
  forward.
  destruct (ck_sent C) eqn:Hsent.
  2: { (* no mac1 sent: target = NULL *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'59 (Vint Int.one) :: Lc) (SEPx Sp))) end.
    { forward. entailer!. }
    { hcy5_p11_C_dead. }
    forward_if.
    2: { hcy5_p11_C_dead. }
    forward.
    sep_apply (hcy5_p11_C_cn_close' C t0 nd false (hcy5_cns (hcy5_chead CL) CL) HCok FCt0 Hsent).
    unfold hcy5_S11. Exists R Sh m c rp. Exists Q nonce rr CK CM. Exists NS PS T np CL. Exists KE CM' honest now2.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
    rewrite Htgt. entailer!. }
  (* mac1 sent: the decryption *)
  pose proof HH as (_ & _ & HX).
  pose proof H5 as (Lno & Len).
  pose proof HCok as (Lck & Llm & Ldk & Lmk).
  destruct (xaead_dec (ck_dkey C) (cm_nonce CM') (ck_last_mac1 C) (cm_enc CM')) as [pt|] eqn:Hdec.
  2: { (* the decryption fails: target = NULL *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'59 (Vint Int.one) :: Lc) (SEPx Sp))) end.
    { hcy5_p11_C_dead. }
    { rewrite hcy5_p11_C_cm_open. Intros. unfold hcy5_p11_C_cm.
      unfold wg_consts. rewrite hcy5_p11_C_zp.
      rewrite (hcy5_p11_C_hprim Ews (cm_enc CM') (offset_val 32 rp)) by lia.
      rewrite (hcy5_p11_C_hprim Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 t0))) by lia.
      rewrite (hcy5_p11_C_hW Ews (cm_nonce CM') (offset_val 8 rp)), (hcy5_p11_C_hW Ews (ck_dkey C) (offset_val 42 (offset_val 8 t0))), Lno, Ldk.
      rewrite (hcy5_p11_C_hout16 Tsh (l_pt L)).
      Intros.
      forward_call (Tsh, l_pt L, Zrepeat Vundef 16, Ews, offset_val 32 rp, cm_enc CM', Ews, offset_val 26 (offset_val 8 t0),
                    ck_last_mac1 C, Ews, offset_val 8 rp, cm_nonce CM', Ews, offset_val 42 (offset_val 8 t0), ck_dkey C, gv).
      { entailer!. destruct t0; try contradiction. destruct rp; try contradiction. rewrite Len, Llm. simpl.
        rewrite !Ptrofs.add_assoc. reflexivity. }
      { rewrite Len. reflexivity. }
      rewrite Hdec. cbv iota.
      rewrite <- (hcy5_p11_C_hout16 Tsh (l_pt L)).
      rewrite <- (hcy5_p11_C_hprim Ews (cm_enc CM') (offset_val 32 rp)) by lia.
      rewrite <- (hcy5_p11_C_hprim Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 t0))) by lia.
      replace (@data_at W Ews (tarray tuchar 24) (map Vubyte (cm_nonce CM')) (offset_val 8 rp))
        with (hbytes Ews (cm_nonce CM') (offset_val 8 rp)) by (rewrite hcy5_p11_C_hW, Lno; reflexivity).
      replace (@data_at W Ews (tarray tuchar 32) (map Vubyte (ck_dkey C)) (offset_val 42 (offset_val 8 t0)))
        with (hbytes Ews (ck_dkey C) (offset_val 42 (offset_val 8 t0))) by (rewrite hcy5_p11_C_hW, Ldk; reflexivity).
      rewrite <- hcy5_p11_C_zp.
      match goal with Hf: field_compatible t_cmsg [] rp |- _ => rename Hf into FCrp end.
      sep_apply (hcy5_p11_C_cm_fold Ews rp CM' H5 FCrp).
      forward.
      unfold wg_consts. entailer!. }
    forward_if.
    2: { hcy5_p11_C_dead. }
    forward.
    sep_apply (hcy5_p11_C_cn_close' C t0 nd true (hcy5_cns (hcy5_chead CL) CL) HCok FCt0 Hsent).
    unfold hcy5_S11. Exists R Sh m c rp. Exists Q nonce rr CK CM. Exists NS PS T np CL. Exists KE CM' honest now2.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
    rewrite Htgt. entailer!. }
  (* the decryption succeeds: pt, then the CHECK of the accepted peer's cookie *)
  change (hcy5_is (hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2)) t0) in Htgt.
  pose proof (xaead_dec_length _ _ HX _ _ _ _ _ Hdec) as Lpt. rewrite Len in Lpt. simpl in Lpt.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    let F := eval pattern (hout Tsh 16 (l_pt L)) in Sp in
    match F with ?f _ => let Sp2 := eval cbv beta in (f (hbytes Tsh pt (l_pt L))) in
      forward_if (PROPx P (LOCALx (temp HY._t'59 (Vint Int.zero) :: Lc) (SEPx Sp2))) end end.
  { hcy5_p11_C_dead. }
  { rewrite hcy5_p11_C_cm_open. Intros. unfold hcy5_p11_C_cm.
    unfold wg_consts. rewrite hcy5_p11_C_zp.
    rewrite (hcy5_p11_C_hprim Ews (cm_enc CM') (offset_val 32 rp)) by lia.
    rewrite (hcy5_p11_C_hprim Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 t0))) by lia.
    rewrite (hcy5_p11_C_hW Ews (cm_nonce CM') (offset_val 8 rp)), (hcy5_p11_C_hW Ews (ck_dkey C) (offset_val 42 (offset_val 8 t0))), Lno, Ldk.
    rewrite (hcy5_p11_C_hout16 Tsh (l_pt L)).
    Intros.
    forward_call (Tsh, l_pt L, Zrepeat Vundef 16, Ews, offset_val 32 rp, cm_enc CM', Ews, offset_val 26 (offset_val 8 t0),
                  ck_last_mac1 C, Ews, offset_val 8 rp, cm_nonce CM', Ews, offset_val 42 (offset_val 8 t0), ck_dkey C, gv).
    { entailer!. destruct t0; try contradiction. destruct rp; try contradiction. rewrite Len, Llm. simpl.
      rewrite !Ptrofs.add_assoc. reflexivity. }
    { rewrite Len. reflexivity. }
    rewrite Hdec. cbv iota.
    rewrite (hcy5_p11_C_pout Tsh pt (l_pt L)) by lia.
    rewrite <- (hcy5_p11_C_hprim Ews (cm_enc CM') (offset_val 32 rp)) by lia.
    rewrite <- (hcy5_p11_C_hprim Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 t0))) by lia.
    replace (@data_at W Ews (tarray tuchar 24) (map Vubyte (cm_nonce CM')) (offset_val 8 rp))
      with (hbytes Ews (cm_nonce CM') (offset_val 8 rp)) by (rewrite hcy5_p11_C_hW, Lno; reflexivity).
    replace (@data_at W Ews (tarray tuchar 32) (map Vubyte (ck_dkey C)) (offset_val 42 (offset_val 8 t0)))
      with (hbytes Ews (ck_dkey C) (offset_val 42 (offset_val 8 t0))) by (rewrite hcy5_p11_C_hW, Ldk; reflexivity).
    rewrite <- hcy5_p11_C_zp.
    match goal with Hf: field_compatible t_cmsg [] rp |- _ => rename Hf into FCrp end.
    sep_apply (hcy5_p11_C_cm_fold Ews rp CM' H5 FCrp).
    forward.
    unfold wg_consts. entailer!. }
  forward_if.
  { hcy5_p11_C_dead. }
  (* t'80 = target->n; t'81 = t'80->p; c = &t'81->latest_cookie *)
  assert (HinN: In N (hnodes_snapped4 T NS PS)) by (rewrite HNS; apply in_elt).
  sep_apply (hcy5_p11_C_node (hcy5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) N (e_peer E) HinN HNp).
  Intros. rewrite HNa.
  assert_PROP (isptr nd) as Pnd. { entailer!. }
  forward.
  set (P' := p_set_cookie P (hcy5_p11_newck C now2 pt)) in *.
  assert (HinP: In (e_peer E, Ews, P') (peers_after PS (Some (e_peer E, P')))).
  { exact (hcy5_p11_C_supd_in PS (e_peer E) Ews P P' Hsf). }
  rewrite Hres.
  assert_PROP (@field_compatible Noise.CS t_peer [] (e_peer E)) as FCp.
  { sep_apply (hcy5_p11_C_pfc _ _ _ _ HinP). entailer!. }
  assert (Pp: isptr (e_peer E)) by (destruct FCp; auto).
  forward.
  forward.
  match goal with |- context [temp HY._c (offset_val ?z (e_peer E))] =>
    replace z with OFS_PEER_COOKIE by reflexivity end.
  fold (cookie_addr (e_peer E)).
  sep_apply (hcy5_p11_C_ck_open _ (e_peer E) P' now2 true pt false (ck_last_mac1 C) (ck_dkey C) (ck_mkey C) HinP eq_refl).
  Intros lk.
  match goal with Hf: cookie_ok (mkCookie _ _ _ _ _ _ _) |- _ => rename Hf into HCk' end.
  match goal with Hf: field_compatible hcy5_p11_C_tck [] _ |- _ => rename Hf into FCck end.
  unfold hcy5_p11_C_ckp, hcy5_p11_C_tck. Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 9 (cookie_addr (e_peer E)), pt, Tsh, l_pt L, pt).
    { entailer!. unfold cookie_addr. destruct (e_peer E); try contradiction. rewrite Lpt. reflexivity. }
    rewrite hcy5_p11_C_eqb_refl.
    hcy5_p11_C_fif HY._t'50 (Vint Int.one).
    { forward. forward. unfold Int64.cmpu. rewrite Int64.eq_true. entailer!. }
    { hcy5_p11_C_dead. }
    hcy5_p11_C_fif HY._t'51 (Vint Int.one).
    { forward. forward. entailer!. }
    { hcy5_p11_C_dead. }
    hcy5_p11_C_fif HY._t'52 (Vint Int.one).
    { forward. forward. entailer!. }
    { hcy5_p11_C_dead. }
    hcy5_p11_C_fif HY._t'53 (Vint Int.one).
    { forward_call (Ews, offset_val 26 (cookie_addr (e_peer E)), ck_last_mac1 C, Ews, offset_val 26 (offset_val 8 t0),
                    ck_last_mac1 C).
      { entailer!. unfold cookie_addr. destruct (e_peer E); try contradiction. destruct t0; try contradiction.
        rewrite Llm. simpl. rewrite !Ptrofs.add_assoc. reflexivity. }
      rewrite hcy5_p11_C_eqb_refl. forward. entailer!. }
    { hcy5_p11_C_dead. }
    hcy5_p11_C_fif HY._t'55 (Vint Int.one).
    { forward_call (Ews, offset_val 42 (cookie_addr (e_peer E)), ck_dkey C, Ews, offset_val 42 (offset_val 8 t0),
                    ck_dkey C).
      { entailer!. unfold cookie_addr. destruct (e_peer E); try contradiction. destruct t0; try contradiction.
        rewrite Ldk. simpl. rewrite !Ptrofs.add_assoc. reflexivity. }
      rewrite hcy5_p11_C_eqb_refl. forward. entailer!. }
    { hcy5_p11_C_dead. }
    hcy5_p11_C_fif HY._t'57 (Vint Int.one).
    { forward_call (Ews, offset_val 74 (cookie_addr (e_peer E)), ck_mkey C, Ews, offset_val 74 (offset_val 8 t0),
                    ck_mkey C).
      { entailer!. unfold cookie_addr. destruct (e_peer E); try contradiction. destruct t0; try contradiction.
        rewrite Lmk. simpl. rewrite !Ptrofs.add_assoc. reflexivity. }
      rewrite hcy5_p11_C_eqb_refl. forward. entailer!. }
    { hcy5_p11_C_dead. }
    forward_if.
    { hcy5_p11_C_dead. }
    forward. entailer!. }
  { forward. entailer!. }
  (* after the CHECK: close the cookie, the node, the cnode; pt back to hout; the post S11 *)
  assert (CKC := hcy5_p11_C_ck_close (cookie_addr (e_peer E)) now2 true pt false (ck_last_mac1 C) (ck_dkey C)
                   (ck_mkey C) lk (peers_rep (peers_after PS (Some (e_peer E, P')))) HCk' FCck).
  unfold hcy5_p11_C_ckp, hcy5_p11_C_tck in CKC.
  sep_apply CKC.
  sep_apply (modus_ponens_wand (@field_at W Ews t_hnode4 (DOT HY._p) (e_peer E) nd)
               (hnodes_rep4 W (hcy5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  sep_apply (hcy5_p11_C_cn_close' C t0 nd true (hcy5_cns (hcy5_chead CL) CL) HCok FCt0 Hsent).
  sep_apply (hcy5_p11_C_hbytes_out Tsh pt (l_pt L)). rewrite Lpt.
  unfold hcy5_S11. Exists R Sh m c rp. Exists Q nonce rr CK CM. Exists NS PS T np CL. Exists KE CM' honest now2.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  unfold hcy5_is in Htgt. rewrite Htgt, Hres. entailer!.
Qed.

End Phase.
