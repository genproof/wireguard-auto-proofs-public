(* law handshake_receive, phase B8 branch I, segment I1: CHECK(h->state == CONSUMED_INITIATION && remote_ephemeral / latest_timestamp / hash / chaining_key vs mi / ci && remote_index == mi->sender_index && last_initiation_consumption == m_last_consumption(s->lic, now))  (QI -> QI).

   Shared (proved): hrx5_B8_I_sep.v (accessors, port of hci5_p8_A3_sep.v), hrx5_B8_I_pure.v (the model analysis). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_pure.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.blake2s.model.
Local Open Scope Z_scope.

(* ---- pure facts of branch I for the CHECK (port of hci5_p8_A3_pure.v's facts) ---- *)
Lemma hrx5_B8I1_len_blake2s key m : Zlength (blake2s key 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma hrx5_B8I1_len_hmac k d : Zlength (hmac k d) = 32.
Proof. unfold hmac, HASH. apply hrx5_B8I1_len_blake2s. Qed.

Lemma hrx5_B8I1_len2 aead_enc aead_dec SS CK H ENCT t ck h : aead_props aead_enc aead_dec ->
  Zlength ENCT = 28 -> m_consume_init2_model aead_dec SS CK H ENCT = Some (t, ck, h) ->
  Zlength t = 12 /\ Zlength ck = 32 /\ Zlength h = 32.
Proof.
  intros HA HL H0.
  unfold m_consume_init2_model, consume_init_stage2 in H0.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) eqn:E; inv H0.
  apply (aead_dec_length _ _ HA) in E. cbn [im_enct] in E.
  unfold kdf1, mix_hash, HASH. rewrite hrx5_B8I1_len_hmac, hrx5_B8I1_len_blake2s. lia.
Qed.

Lemma hrx5_B8I1_find_in : forall PS s a P, pk_find PS s = Some (a, P) -> exists sh, In (a, sh, P) PS.
Proof.
  induction PS as [|[[x sh] Q] PS IH]; simpl; intros s a P H; [discriminate|].
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) s).
  - inv H. eauto.
  - destruct (IH _ _ _ H) as [sh' Hin]. eauto.
Qed.

Lemma hrx5_B8I1_sfind : forall PS a sh P, NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Hnd Hin; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. reflexivity.
  - rewrite if_false; [eauto|]. intros ->. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hrx5_B8I1_split T : forall PS NS a sh P,
  map hn_p NS = map peer_addr4 PS -> NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ hn_snapshot4 T N (a, sh, P) :: NS2 /\
    hrx5_nfind NS a = hn_addr N /\ hn_p N = a.
Proof.
  induction PS as [|[[x sh0] Q] PS IH]; intros NS a sh P Hmap Hnd Hin; [contradiction|].
  destruct NS as [|N0 NS]; [discriminate|]. simpl in Hmap. injection Hmap as Hx Hmap. subst x.
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [H1 H2].
  change (hnodes_snapped4 T (N0 :: NS) ((hn_p N0, sh0, Q) :: PS)) with
    (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: hnodes_snapped4 T NS PS).
  destruct Hin as [Heq | Hin].
  - inv Heq. exists [], N0, (hnodes_snapped4 T NS PS).
    simpl. rewrite if_true by auto. auto.
  - destruct (IH NS a sh P Hmap H2 Hin) as (NS1 & N & NS2 & E & Ha & Hp).
    exists (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: NS1), N, NS2.
    split; [rewrite E; reflexivity|]. split; [| auto].
    simpl. rewrite if_false; auto. intros Hx. rewrite Hx in H1. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hrx5_B8I1_facts x25519 aead_enc aead_dec R L NS PS KE T head nk M now a P t ck2 h2 :
  aead_props aead_enc aead_dec ->
  hrx5_inv x25519 R L NS PS KE T head nk -> im_ok M ->
  hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M now = Some (a, P, t, ck2, h2) ->
  exists NS1 N NS2,
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
    hn_addr N = hrx5_nfind NS a /\ hn_snap N = hsnap_val (hs_snap_cur T a P) /\
    sfind PS a = Some (Ews, P) /\
    Zlength t = 12 /\ Zlength ck2 = 32 /\ Zlength h2 = 32.
Proof.
  intros HA Hl HM Ht.
  unfold hrx5ci_tgt in Ht.
  destruct (mi_ok _); [|discriminate].
  destruct (m_consume_init1_model x25519 aead_dec _ _ _) as [[[[s k] ck1] h1]|]; [|discriminate].
  destruct (pk_find PS s) as [[a0 P0]|] eqn:Hf; [|discriminate].
  destruct (m_consume_init2_model aead_dec _ ck1 h1 (im_enct M)) as [[[t0 ck0] h0]|] eqn:H2; [|discriminate].
  destruct (_ && _)%bool; [|discriminate]. inv Ht.
  destruct (hrx5_B8I1_len2 aead_enc aead_dec _ _ _ _ _ _ _ HA (proj1 (proj2 (proj2 HM))) H2) as (Lt & Lck & Lh).
  destruct (hrx5_B8I1_find_in _ _ _ _ Hf) as [sh Hin].
  destruct Hl as (Hpok & _ & Hnd & _ & Hnp & _).
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hok.
  assert (Hsh: sh = Ews) by (destruct Hok; auto). subst sh.
  destruct (hrx5_B8I1_split T PS NS a Ews P Hnp Hnd Hin) as (NS1 & N & NS2 & E & Hfind & Hp).
  exists NS1, (hn_snapshot4 T N (a, Ews, P)), NS2.
  split; [exact E|]. cbn [hn_snapshot4 hn_addr hn_p hn_snap].
  split; [auto|]. split; [reflexivity|].
  split; [apply hrx5_B8I1_sfind; auto|]. auto.
Qed.

(* ---- the field last_initiation_consumption of a node's snapshot (port of hci5_p8_A3_s10's accessors) ---- *)
Lemma hrx5_B8I1_flic sn y :
  hrx5_B8I_acc (@field_at W Ews t_hsnap [StructField HH._last_initiation_consumption] (Vlong (hs_lic (sn_hs sn))) y)
    (@data_at W Ews t_hsnap (hsnap_val sn) y).
Proof.
  rewrite <- hrx5_B8I_HW.
  rewrite <- (@field_at_change_composite HCS W hrx5_B8I_cceHW Ews t_hsnap
    [StructField HH._last_initiation_consumption] (Vlong (hs_lic (sn_hs sn))) (Vlong (hs_lic (sn_hs sn))) (JMeq_refl _))
    by (vm_compute; reflexivity).
  unfold hrx5_B8I_acc.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts HCS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif HCS Ews t_hsnap [] (StructField HH._last_initiation_consumption)
    (hsnap_val sn) (Vlong (hs_lic (sn_hs sn))) y); [apply JMeq_refl | auto with field_compatible]|].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (Vlong (hs_lic (sn_hs sn)))).
  apply wand_derives; [apply derives_refl|]. unfold data_at. apply derives_refl'. f_equal.
Qed.

Lemma hrx5_B8I1_nlic N NS l sn : In N NS -> hn_snap N = hsnap_val sn ->
  hrx5_B8I_acc (@field_at W Ews t_hsnap [StructField HH._last_initiation_consumption] (Vlong (hs_lic (sn_hs sn)))
    (offset_val 8 (hn_addr N))) (hnodes_rep4 W l NS).
Proof.
  intros Hin Hsn. apply (hrx5_B8I_nodes_acc _ N); auto. intros nx.
  apply hrx5_B8I_acc_pure with (c := @field_compatible CKS t_hnode4 [] (hn_addr N));
    [eapply derives_trans; [apply (@data_at_local_facts CKS)|]; apply prop_derives; tauto|].
  intros FC. eapply hrx5_B8I_acc_trans; [|apply hrx5_B8I_nfld_snap].
  rewrite (hrx5_B8I_snap_at _ _ FC), Hsn. apply hrx5_B8I1_flic.
Qed.

(* ---- ci.ts (offset 128 of the harness's mcinit) ---- *)
Section CIts.
#[local] Existing Instance HCS.
Lemma hrx5_B8I1_ci_ts sh ck h key spub t ci : Zlength t = 12 ->
     @data_at HCS sh t_mcinit (mcinit_val ck h key spub (bytes t)) ci |--
     hbytes sh t (offset_val 128 ci) *
     (hbytes sh t (offset_val 128 ci) -* @data_at HCS sh t_mcinit (mcinit_val ck h key spub (bytes t)) ci).
Proof.
  intros L. assert_PROP (@field_compatible HCS t_mcinit [] ci) by entailer!.
  unfold mcinit_val. unfold_data_at (@data_at HCS _ _ _ ci).
  rewrite (@field_at_data_at HCS sh t_mcinit [StructField HH._ts]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.
End CIts.

(* ---- msg->sender_index as one field at the world compspecs (port of hci5_p8_A3_s9_msg) ---- *)
Section S9M.
#[local] Existing Instance Noise.CS.
Lemma hrx5_B8I1_msgN sh m M : init_rep sh m M |--
  @field_at Noise.CS sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m *
  (@field_at Noise.CS sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m -* init_rep sh m M).
Proof.
  unfold init_rep. Intros.
  assert_PROP (field_compatible t_init [] m) by entailer!. unfold_data_at (data_at _ _ _ m).
  cancel.
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right; auto | cancel].
Qed.
End S9M.

Lemma hrx5_B8I1_msg sh m M : init_rep sh m M |--
  @field_at W sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m *
  (@field_at W sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m -* init_rep sh m M).
Proof.
  rewrite <- (hrx5_B8I_fW sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M))
    (Vint (im_sender M)) m (JMeq_refl _)) by (vm_compute; reflexivity).
  apply hrx5_B8I1_msgN.
Qed.

Lemma hrx5_B8I1_bytes_eqb_refl b : bytes_eqb b b = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec b b); congruence. Qed.

Ltac hrx5_B8I1_absurd := exfalso; match goal with
  | Hc: HS_CONSUMED_INITIATION <> Int.repr 2 |- _ => apply Hc; reflexivity
  | Hc: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hc)
  | Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc)
  | Hc: _ = Int.zero |- _ => rewrite ?Int.eq_true, ?Int64.eq_true in Hc; exact (Int.one_not_zero Hc)
  end.

Ltac hrx5_B8I1_post := match goal with |- _ |-- RA_normal (match ?X with _ => _ end) =>
  destruct X as [r1 r2 r3 r4] end; cbn [RA_normal].

Local Open Scope logic.

Lemma hrx5_B8I_I1_ok : hrx5_B8I_I1_stmt.
Proof.
  unfold hrx5_B8I_I1_stmt, hrx5_B8I_seg.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1 S1 lul1 HY.
  unfold hrx5_B8I_QI, hrx5_Delta, hrx5_B8I_I1.
  unfold hrx5_B8I_props, hrx5_B8I_temps, hrx5_lvars, hrx5_B8I_world, hrx5_rest, hrx5_cglobs, hrx5_B8I_scr; cbn [app].
  abbreviate_semax.
  Intros.
  destruct HY as (Hx & Ha & Hxa).
  destruct (hrx5_B8I1_facts x25519 aead_enc aead_dec R L NS PS KE T head nk M (s_boot S) a P t ck2 h2 Ha H3 H6 H9)
    as (NS1 & N & NS2 & HNS & Hna & Hsn & Hsf & Lt & Lck & Lh).
  assert_PROP (isptr a) as Pa.
  { rewrite (hrx5_B8I_peers PS a Ews P (hrx5_B8I_put P M (s_boot S) t ck2 h2) Hsf).
    sep_apply (hrx5_B8I_peer_fc Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). entailer!.
    unfold hs_addr in *. match goal with Hf: field_compatible _ _ (offset_val _ ?x) |- isptr ?x =>
      apply field_compatible_isptr in Hf; destruct x; try contradiction; exact I end. }
  assert (Pdp: isptr dp) by (clear - H7; destruct dp; try contradiction; exact I).
  rewrite (hrx5_B8I_peers PS a Ews P (hrx5_B8I_put P M (s_boot S) t ck2 h2) Hsf).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - sep_apply (hrx5_B8I_pk_state Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
    rewrite (hrx5_B8I_put_state P M (s_boot S) t ck2 h2).
    forward.
    sep_apply (hrx5_B8I_mp
      (@field_at W Ews t_hs [StructField prot_repr3.I._state] (Vint HS_CONSUMED_INITIATION) (hs_addr a))
      (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
    (* link 1: state == CONSUMED_INITIATION && bytes_eq(remote_ephemeral, mi->unencrypted_ephemeral) *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'114 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { sep_apply (hrx5_B8I_pk_reph Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
      rewrite (hrx5_B8I_put_reph P M (s_boot S) t ck2 h2).
      sep_apply (hrx5_B8I_msg_eph Ews dp M). Intros.
      forward_call (Ews, offset_val 168 a, im_eph M, Ews, offset_val 8 dp, im_eph M).
      + unfold hs_addr. destruct a; try contradiction; exact I.
      + entailer!.
        simpl. destruct H6 as (L1 & _). rewrite L1. unfold hs_addr. rewrite offset_offset_val. reflexivity.
      + destruct H6 as (L1 & _). rewrite L1. rep_lia.
      + rewrite hrx5_B8I1_bytes_eqb_refl.
        forward.
        sep_apply (hrx5_B8I_mp (hbytes Ews (im_eph M) (offset_val 8 dp)) (init_rep Ews dp M)).
        sep_apply (hrx5_B8I_mp (hbytes Ews (im_eph M) (offset_val 168 a))
          (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
        hrx5_B8I1_post. entailer!. }
    { hrx5_B8I1_absurd. }
    (* link 2: bytes_eq(latest_timestamp, ci.ts, 12) *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'116 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { sep_apply (hrx5_B8I_pk_ts Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
      rewrite (hrx5_B8I_put_ts P M (s_boot S) t ck2 h2).
      sep_apply (hrx5_B8I1_ci_ts Tsh ck2 h2 key spub t (l_ci L) Lt). Intros.
      forward_call (Ews, offset_val 328 a, t, Tsh, offset_val 128 (l_ci L), t).
      { unfold hs_addr. destruct a; try contradiction; exact I. }
      { entailer!. rewrite Lt. unfold hs_addr. simpl. normalize. }
      all: try (rewrite ?Lt, ?Lh, ?Lck; rep_lia).
        rewrite hrx5_B8I1_bytes_eqb_refl.
        forward.
        sep_apply (hrx5_B8I_mp (hbytes Tsh t (offset_val 128 (l_ci L)))
          (@data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L))).
        sep_apply (hrx5_B8I_mp (hbytes Ews t (offset_val 328 a)) (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
        hrx5_B8I1_post. entailer!. }
    { hrx5_B8I1_absurd. }
    (* link 3: bytes_eq(hash, ci.st.h, 32) *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'118 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { sep_apply (hrx5_B8I_pk_hash Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
      rewrite (hrx5_B8I_put_hash P M (s_boot S) t ck2 h2).
      sep_apply (hrx5_B8I_ci_st Tsh ck2 h2 key spub (bytes t) (l_ci L) Lck Lh). Intros.
      forward_call (Ews, offset_val 264 a, h2, Tsh, offset_val 32 (l_ci L), h2).
      { unfold hs_addr. destruct a; try contradiction; exact I. }
      { entailer!. simpl. rewrite Lh. unfold hs_addr. rewrite !offset_offset_val. reflexivity. }
      all: try (rewrite ?Lt, ?Lh, ?Lck; rep_lia).
        rewrite hrx5_B8I1_bytes_eqb_refl.
        forward.
        sep_apply (hrx5_B8I_mp (hbytes Tsh ck2 (l_ci L) * hbytes Tsh h2 (offset_val 32 (l_ci L)))%logic
          (@data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L))).
        sep_apply (hrx5_B8I_mp (hbytes Ews h2 (offset_val 264 a)) (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
        hrx5_B8I1_post. entailer!. }
    { hrx5_B8I1_absurd. }
    (* link 4: bytes_eq(chaining_key, ci.st.ck, 32) *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'120 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { sep_apply (hrx5_B8I_pk_ck Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
      rewrite (hrx5_B8I_put_ck P M (s_boot S) t ck2 h2).
      sep_apply (hrx5_B8I_ci_st Tsh ck2 h2 key spub (bytes t) (l_ci L) Lck Lh). Intros.
      forward_call (Ews, offset_val 296 a, ck2, Tsh, l_ci L, ck2).
      { unfold hs_addr. destruct a; try contradiction; exact I. }
      { entailer!. simpl. rewrite Lck. unfold hs_addr. rewrite !offset_offset_val. change (0 + 0) with 0.
        rewrite (isptr_offset_val_zero (l_ci L)) by auto. reflexivity. }
      all: try (rewrite ?Lt, ?Lh, ?Lck; rep_lia).
        rewrite hrx5_B8I1_bytes_eqb_refl.
        forward.
        sep_apply (hrx5_B8I_mp (hbytes Tsh ck2 (l_ci L) * hbytes Tsh h2 (offset_val 32 (l_ci L)))%logic
          (@data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L))).
        sep_apply (hrx5_B8I_mp (hbytes Ews ck2 (offset_val 296 a)) (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
        hrx5_B8I1_post. entailer!. }
    { hrx5_B8I1_absurd. }
    (* link 5: h->remote_index == mi->sender_index *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'122 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { sep_apply (hrx5_B8I_pk_rindex Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
      rewrite (hrx5_B8I_put_rindex P M (s_boot S) t ck2 h2).
      sep_apply (hrx5_B8I1_msg Ews dp M). Intros.
      forward. forward. forward.
      sep_apply (hrx5_B8I_mp
        (@field_at W Ews t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) dp) (init_rep Ews dp M)).
      sep_apply (hrx5_B8I_mp
        (@field_at W Ews t_hs [StructField prot_repr3.I._remote_index] (Vint (im_sender M)) (hs_addr a))
        (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
      hrx5_B8I1_post. rewrite Int.eq_true. entailer!. }
    { hrx5_B8I1_absurd. }
    (* link 6: h->last_initiation_consumption == m_last_consumption(s->last_initiation_consumption, now) *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'123 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { pose (Fl := @field_at W Ews t_hsnap [StructField HH._last_initiation_consumption] (Vlong (hs_lic (p_hs P)))
        (offset_val 8 (hrx5_nfind NS a))).
      assert (Hnode: hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) |--
        Fl * (Fl -* hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
      { unfold Fl. rewrite <- Hna. change (hs_lic (p_hs P)) with (hs_lic (sn_hs (hs_snap_cur T a P))).
        apply hrx5_B8I1_nlic; [rewrite HNS; apply in_elt | exact Hsn]. }
      sep_apply Hnode. Intros.
      unfold Fl. forward. fold Fl.
      sep_apply (hrx5_B8I_mp Fl (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
      freeze [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41] FZ.
      forward_call (hs_lic (p_hs P), s_boot S).
      thaw FZ.
      sep_apply (hrx5_B8I_pk_lic Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)). Intros.
      rewrite (hrx5_B8I_put_lic P M (s_boot S) t ck2 h2).
      forward. forward.
      rewrite <- (hrx5_B8I_put_lic P M (s_boot S) t ck2 h2).
      sep_apply (hrx5_B8I_mp
        (@field_at W Ews t_hs [StructField prot_repr3.I._last_initiation_consumption]
           (Vlong (hs_lic (p_hs (hrx5_B8I_put P M (s_boot S) t ck2 h2)))) (hs_addr a))
        (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
      hrx5_B8I1_post. rewrite Int64.eq_true. entailer!. }
    { hrx5_B8I1_absurd. }
    (* CHECK *)
    forward_if True.
    { hrx5_B8I1_absurd. }
    { forward. hrx5_B8I1_post. entailer!. }
    forward.
    match goal with |- context [hrx5_RB ?a ?b ?c ?d] => destruct (hrx5_RB a b c d) as [r1 r2 r3 r4] end.
    unfold loop_nocontinue_ret_assert. cbn [RA_break RA_normal]. entailer!.
  - match goal with |- context [hrx5_RB ?a ?b ?c ?d] => destruct (hrx5_RB a b c d) as [r1 r2 r3 r4] end.
    cbn [RA_normal].
    rewrite (hrx5_B8I_peers PS a Ews P (hrx5_B8I_put P M (s_boot S) t ck2 h2) Hsf).
    entailer!.
Qed.
