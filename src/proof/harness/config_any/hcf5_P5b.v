(* law config_any: main's phase P5b, statements 57..74: hq = the initial handshake (18 field writes / byte helpers), CHECK(hs_same(&hq, &q.handshake)).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require Import WgNoise.proof.harness.config_any.hcf5_p5b_lem.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

Lemma hcf5_p5b_succ a l : ~ In a l -> succ_in l a = nullval.
Proof.
  induction l as [|x l IH]; simpl; intros N; [reflexivity |].
  destruct (EqDec_val x a) as [E|E]; [exfalso; apply N; left; exact E |].
  apply IH. intros I; apply N; right; exact I.
Qed.

Lemma hcf5_p5b_vin a l : ~ In a l -> vin a l = false.
Proof. intros N. unfold vin. destruct (in_dec _ a l); [contradiction | reflexivity]. Qed.

Lemma hcf5_p5b_vdev wa D : device_rep Tsh wa D = vobjs W_config_any [VDev Tsh wa D].
Proof. unfold vobjs; simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcf5_p5b_hout X p : Zlength X = 32 -> hbytes Tsh X p |-- hout Tsh 32 p.
Proof. intros HL. unfold hbytes, hout. rewrite HL. apply data_at_data_at_. Qed.

Ltac hcf5_p5b_par :=
  apply prop_right; unfold field_address;
  rewrite if_true by (apply field_compatible_cons; split; auto; cbv; tauto);
  match goal with Hf: field_compatible t_hsnap [] ?q |- _ =>
    destruct q eqn:?; try (destruct Hf; contradiction); reflexivity end.

Section P5b.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P5b_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_S5a x25519 gv L FR) hcf5_P5b
    (overridePost (hcf5_S5b x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HX. unfold hcf5_S5a, hcf5_Delta, hcf5_R, hcf5_P5b. simplify_func_tycontext. abbreviate_semax.
  unfold hcf5_Fx.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0. Intros RAW QPUB PSK ub.
  unfold hcf5_core, hcf5_globs, hcf5_X5a. cbn [app].
  repeat flatten_sepcon_in_SEP.
  freeze [2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;18;19;22;23] FR1.
  rewrite hcf5_conv_hsnap, hcf5_p5b_open. Intros. repeat flatten_sepcon_in_SEP.
  forward. forward. forward. forward. forward. forward. forward. forward.
  unfold hcf5_p5b_fa.
  forward_call (Tsh, field_address t_hsnap (DOT HF._ephemeral_private) (l_hq L), Byte.zero, 32).
  { hcf5_p5b_par. }
  replace (hout Tsh 32 (field_address t_hsnap (DOT HF._remote_static) (l_hq L)))
    with (hout Tsh (Zlength QPUB) (field_address t_hsnap (DOT HF._remote_static) (l_hq L))) by (rewrite H0; reflexivity).
  forward_call (Tsh, field_address t_hsnap (DOT HF._remote_static) (l_hq L), Tsh, l_qpub L, QPUB).
  { rewrite H0. hcf5_p5b_par. }
  forward_call (Tsh, field_address t_hsnap (DOT HF._remote_ephemeral) (l_hq L), Byte.zero, 32).
  { hcf5_p5b_par. }
  assert (Lpriv: Zlength (mi_priv (mident_of x25519 RAW)) = 32)
    by (destruct H as [HR _]; simpl; unfold clamp; list_solve).
  forward_call (Tsh, field_address t_hsnap (DOT HF._precomputed_static_static) (l_hq L), Tsh, l_id L,
                mident_of x25519 RAW, Tsh, l_qpub L, QPUB).
  { hcf5_p5b_par. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval cbv [replace_nth] in (replace_nth 17 R (hbytes Tsh (if ub then PSK else zeros32)
                                           (field_address t_hsnap (DOT HF._preshared_key) (l_hq L)))) in
    forward_if (PROPx P (LOCALx Q (SEPx R'))) end.
  { destruct ub; [| exfalso; apply H5; reflexivity].
    replace (hout Tsh 32 (field_address t_hsnap (DOT HF._preshared_key) (l_hq L)))
      with (hout Tsh (Zlength PSK) (field_address t_hsnap (DOT HF._preshared_key) (l_hq L))) by (rewrite H1; reflexivity).
    forward_call (Tsh, field_address t_hsnap (DOT HF._preshared_key) (l_hq L), Tsh, l_psk L, PSK).
    { rewrite H1. hcf5_p5b_par. }
    apply andp_left2. unfold PROPx. apply andp_derives; [apply derives_refl |].
    unfold LOCALx. apply andp_derives; [apply derives_refl |].
    intro rho. unfold SEPx. cbn [fold_right_sepcon]. cancel. }
  { destruct ub; [discriminate |].
    forward_call (Tsh, field_address t_hsnap (DOT HF._preshared_key) (l_hq L), Byte.zero, 32).
    { hcf5_p5b_par. }
    apply andp_left2. unfold PROPx. apply andp_derives; [apply derives_refl |].
    unfold LOCALx. apply andp_derives; [apply derives_refl |].
    intro rho. unfold SEPx. cbn [fold_right_sepcon]. cancel. apply derives_refl. }
  forward_call (Tsh, field_address t_hsnap (DOT HF._hash) (l_hq L), Byte.zero, 32).
  { hcf5_p5b_par. }
  forward_call (Tsh, field_address t_hsnap (DOT HF._chaining_key) (l_hq L), Byte.zero, 32).
  { hcf5_p5b_par. }
  forward_call (Tsh, field_address t_hsnap (DOT HF._latest_timestamp) (l_hq L), Byte.zero, 12).
  { hcf5_p5b_par. }
  forward.
  (* hq is the snapshot of q's handshake *)
  set (Hq := hcf5_qhs x25519 D L QPUB PSK ub).
  set (SN := hs_snap_cur T (l_q L) (hcf5_qpeer Hq)).
  pose proof H2 as (Hrun & Hboot & Hw & Hdok & Hpok & Hslots & HTok & Hks).
  pose proof HTok as (HTD & _ & _ & _ & HTq).
  destruct (HTq eq_refl) as (_ & Hent & Hnin).
  pose proof H as [HRAW [ID0 [HID0 HDID]]].
  assert (Lss: Zlength (m_precomputed_model x25519 (mident_of x25519 RAW) QPUB) = 32)
    by (unfold m_precomputed_model; destruct (andb _ _); [apply HX | reflexivity]).
  assert (Lpsk: Zlength (if ub then PSK else zeros32) = 32) by (destruct ub; [exact H1 | reflexivity]).
  assert (Ea: l_q L = e_peer (sn_entry SN))
    by (unfold SN, hs_snap_cur, snap_of; cbn [sn_entry]; rewrite Hent; reflexivity).
  assert (Eb: Vlong (Int64.repr (Int.signed (Int.repr 0))) = sn_next SN)
    by (unfold SN, hs_snap_cur, snap_of; cbn [sn_next]; rewrite (hcf5_p5b_succ _ _ Hnin); reflexivity).
  assert (Ec: Vint Int.zero = Val.of_bool (sn_hashed SN))
    by (unfold SN, hs_snap_cur, snap_of; cbn [sn_hashed]; rewrite (hcf5_p5b_vin _ _ Hnin); reflexivity).
  assert (Ed: Vint (Int.repr 1) = Vint (e_type (sn_entry SN)))
    by (unfold SN, hs_snap_cur, snap_of; cbn [sn_entry]; rewrite Hent; reflexivity).
  assert (Ee: Vint (Int.repr 0) = Vint (e_index (sn_entry SN)))
    by (unfold SN, hs_snap_cur, snap_of; cbn [sn_entry]; rewrite Hent; reflexivity).
  assert (E4: m_precomputed_model x25519 (mident_of x25519 RAW) QPUB = hs_ss (sn_hs SN)).
  { change (hs_ss (sn_hs SN)) with (precomputed x25519 (d_id D) QPUB). rewrite HDID. reflexivity. }
  freeze [4;5;9;10;11;23;24] FR2.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx P (LOCALx Q (SEPx [FRZL FR2; @data_at HCS Tsh t_hsnap (hsnap_val SN) (l_hq L)]))) end.
  { apply andp_left2. unfold PROPx. apply andp_derives; [apply derives_refl |].
    unfold LOCALx. apply andp_derives; [apply derives_refl |].
    intro rho. unfold SEPx. cbn [fold_right_sepcon]. rewrite !sepcon_emp.
    eapply derives_trans; [| apply sepcon_derives; [apply derives_refl |]].
    2: apply (hcf5_p5b_close Tsh (l_hq L) SN (l_q L) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) (Vint Int.zero)
     (Vint (Int.repr 1)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vlong (Int64.repr (Int.signed (Int.repr 0))))
     (offset_val 8 (l_w L)) (Vint (Int.repr 0))
     (Zrepeat Byte.zero 32) QPUB (Zrepeat Byte.zero 32) (m_precomputed_model x25519 (mident_of x25519 RAW) QPUB)
     (if ub then PSK else zeros32) (Zrepeat Byte.zero 32) (Zrepeat Byte.zero 32) (Zrepeat Byte.zero 12)
     Ea Eb Ec Ed Ee eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl E4 eq_refl eq_refl eq_refl eq_refl
     eq_refl H0 eq_refl Lss Lpsk eq_refl eq_refl eq_refl H4).
    cancel. }
  thaw FR2.
  rewrite (hcf5_p5b_vdev (l_w L) D).
  change (hs_mem false Tsh (l_q L) (hcf5_qpeer (hcf5_qhs x25519 D L QPUB PSK ub)))
    with (hs_mem false Tsh (l_q L) (hcf5_qpeer Hq)).
  assert (Hin: In (hs_addr (l_q L)) (saddrs (t_D T))) by (rewrite HTD; left; reflexivity).
  assert_PROP (isptr (l_q L)) as Pq by (go_lowerx; apply prop_right;
    match goal with K: lvar_denote hcf5_defs.HF._q _ _ _ |- _ => eapply (lvar_isptr hcf5_defs.HF._q); exact K end).
  assert (Hqok: hcf5_qok L Hq).
  { split; [| reflexivity].
    change (hs_ok (hs_initial x25519 (d_id D) (id_addr (l_w L)) QPUB (if ub then PSK else zeros32))).
    unfold hs_ok, hs_initial. cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
    rewrite HDID. repeat split; try reflexivity; assumption. }
  assert (HV: Forall vobj_ok [VDev Tsh (l_w L) D] /\
              Forall (vp_ok (hs_own (l_q L) T [VDev Tsh (l_w L) D])) (hs_ptrs SN SN)).
  { split; [apply Forall_cons; [apply readable_share_top | apply Forall_nil] |].
    unfold hs_ptrs, hs_ptrs_nn. rewrite <- Ea, <- Eb.
    assert (V1: vp_ok (hs_own (l_q L) T [VDev Tsh (l_w L) D]) (Vlong (Int64.repr (Int.signed (Int.repr 0)))))
      by (left; reflexivity).
    assert (V2: vp_ok (hs_own (l_q L) T [VDev Tsh (l_w L) D]) (l_q L)) by (right; left; reflexivity).
    assert (V3: vp_ok (hs_own (l_q L) T [VDev Tsh (l_w L) D]) (hs_sid (sn_hs SN))).
    { unfold hs_own, vobjs_addrs. cbn [map concat vobj_addrs app].
      right; right. apply in_or_app; right; right; left; reflexivity. }
    repeat (apply Forall_cons; [assumption |]); apply Forall_nil. }
  assert (HSN: hs_snap_cur T (l_q L) (hcf5_qpeer Hq) = SN) by reflexivity.
  clearbody SN Hq.
  clear Ea Eb Ec Ed Ee E4.
  unfold hcf5_lvars.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  - apply ENTAIL_refl.
  - eapply semax_seq'; [prove_call_setup (@nil Type) funspec_sub_refl
      (Tsh, l_hq L, SN, Tsh, l_q L, hcf5_qpeer Hq, false, Tsh, l_it L, T, [VDev Tsh (l_w L) D]) | ].
    clear_Delta_specs. clear_MORE_POST.
    forward_call_id1_wow.
    { rewrite HSN. exact HV. }
    rewrite HSN, hcf5_snap_eqb_refl.
    Intros vret. unfold eq_no_post. cbn [app]. Intros. subst vret. simpl remove_localdef_temp.
    unfold MORE_COMMANDS, abbreviate.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. entailer!.
  - forward. apply ENTAIL_refl.
  - unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hcf5_S5b.
    rewrite <- (hcf5_p5b_vdev (l_w L) D). thaw FR1.
    sep_apply (hcf5_p5b_hout QPUB (l_qpub L) H0).
    sep_apply (hcf5_p5b_hout PSK (l_psk L) H1).
    Exists R S w D P T KE D0. Exists sn0 P0 r0 S0. Exists w0 h0 RAW Hq.
    unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_X5b, hcf5_lvars. cbn [app].
    rewrite HSN.
    entailer!.
Qed.

End P5b.
