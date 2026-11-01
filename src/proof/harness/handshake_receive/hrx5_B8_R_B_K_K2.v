(* v2, law handshake_receive, B8 R B part K: segment K2, the keypair CHECK (kp != NULL && initiator && entry.peer == target->p && entry.index == s->index && table_has(&itd, &kp->entry) && remote_index == mr->sender_index). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Ltac hrx5_B8RBK2_sub :=
  let Q0 := fresh "Q0" in let HQ := fresh "HQ" in
  intros Q0 HQ; simpl In in HQ;
  repeat (destruct HQ as [<- | HQ]; [simpl In; repeat (first [left; reflexivity | right]) | ]);
  contradiction.

Lemma hrx5_B8RBK2_close (Pl: list Prop) Q Q' R R' :
  fold_right and True Pl -> (forall q, In q Q' -> In q Q) -> fold_right_sepcon R |-- fold_right_sepcon R' ->
  PROPx [] (LOCALx Q (SEPx R)) |-- PROPx Pl (LOCALx Q' (SEPx R')).
Proof.
  intros HP HQ HR. eapply derives_trans; [apply LOCALx_shuffle_derives, HQ|].
  unfold PROPx, LOCALx, SEPx. intro rho. cbn. normalize. try (apply andp_right; [apply prop_right, HP|]).
  apply andp_derives; [apply derives_refl | apply HR].
Qed.

Lemma hrx5_B8RBK2_eqp t1 t2 x : is_pointer_or_null x ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t1) (tptr t2) x x)) = Vint Int.one.
Proof.
  intros Hx. destruct x; try contradiction; simpl in Hx;
    unfold eval_binop, sem_binary_operation', sem_cmp, sem_cmp_pp; simpl; rewrite !andb_false_r; simpl.
  - subst. reflexivity.
  - destruct (eq_block b b); [| congruence]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hrx5_B8RBK2_itab_vp tab T k E : sfind (t_D T) k = Some (Ews, E) -> itable Tsh tab T |-- valid_pointer k.
Proof.
  intros Hf. eapply derives_trans; [apply (hrx5_B8RBK_pool tab T k E Hf)|].
  apply sepcon_valid_pointer1. unfold entry_at. apply data_at_valid_ptr; [auto | vm_compute; reflexivity].
Qed.

Lemma hrx5_B8RBK2_saddrs {A: Type} (D: list (val * share * A)) x sh v : sfind D x = Some (sh, v) -> In x (saddrs D).
Proof.
  intros H. apply hrx5_B8RBK_sfind_In in H. unfold saddrs.
  change x with ((fun '(x, _, _) => x) (x, sh, v)). apply in_map, H.
Qed.

(* the index field of a node's handshake snapshot (s = offset_val 8 node), the rest of the list in the wand *)
Lemma hrx5_B8RBK2_snap_split shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
  @data_at W shs t_hsnap
    (a, (b, (c, (d, (e, (f, (g, (h, (l1, (l2, (l3, (l4, (l5, (l6, (l7, (l8, ri)))))))))))))))) s =
  field_at shs t_hsnap (DOT HM._peer) a s * field_at shs t_hsnap (DOT HM._next) b s *
  field_at shs t_hsnap (DOT HM._hashed) c s * spacer shs 17 20 s *
  field_at shs t_hsnap (DOT HM._type) d s * field_at shs t_hsnap (DOT HM._index) e s *
  field_at shs t_hsnap (DOT HM._state) f s * field_at shs t_hsnap (DOT HM._last_initiation_consumption) g s *
  field_at shs t_hsnap (DOT HM._static_identity) h s *
  data_at shs (tarray tuchar 32) l1 (field_address t_hsnap (DOT HM._ephemeral_private) s) *
  data_at shs (tarray tuchar 32) l2 (field_address t_hsnap (DOT HM._remote_static) s) *
  data_at shs (tarray tuchar 32) l3 (field_address t_hsnap (DOT HM._remote_ephemeral) s) *
  data_at shs (tarray tuchar 32) l4 (field_address t_hsnap (DOT HM._precomputed_static_static) s) *
  data_at shs (tarray tuchar 32) l5 (field_address t_hsnap (DOT HM._preshared_key) s) *
  data_at shs (tarray tuchar 32) l6 (field_address t_hsnap (DOT HM._hash) s) *
  data_at shs (tarray tuchar 32) l7 (field_address t_hsnap (DOT HM._chaining_key) s) *
  data_at shs (tarray tuchar 12) l8 (field_address t_hsnap (DOT HM._latest_timestamp) s) *
  field_at shs t_hsnap (DOT HM._remote_index) ri s.
Proof.
  match goal with |- @data_at _ _ _ ?v _ = _ => set (V := v) end.
  unfold data_at.
  rewrite (@field_at_Tstruct W shs t_hsnap [] HH._hs_snap noattr V V s eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at shs t_hsnap (DOT HM._ephemeral_private)),
    (field_at_data_at shs t_hsnap (DOT HM._remote_static)),
    (field_at_data_at shs t_hsnap (DOT HM._remote_ephemeral)),
    (field_at_data_at shs t_hsnap (DOT HM._precomputed_static_static)),
    (field_at_data_at shs t_hsnap (DOT HM._preshared_key)),
    (field_at_data_at shs t_hsnap (DOT HM._hash)),
    (field_at_data_at shs t_hsnap (DOT HM._chaining_key)),
    (field_at_data_at shs t_hsnap (DOT HM._latest_timestamp)).
  simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Lemma hrx5_B8RBK2_hsnap_eq sn :
  hsnap_val sn =
  (e_peer (sn_entry sn), (sn_next sn, (Val.of_bool (sn_hashed sn), (Vint (e_type (sn_entry sn)),
  (Vint (e_index (sn_entry sn)),
  (Vint (hs_state (sn_hs sn)), (Vlong (hs_lic (sn_hs sn)), (hs_sid (sn_hs sn), (bytes (hs_eph (sn_hs sn)),
  (bytes (hs_rstatic (sn_hs sn)), (bytes (hs_reph (sn_hs sn)), (bytes (hs_ss (sn_hs sn)),
  (bytes (hs_psk (sn_hs sn)), (bytes (hs_hash (sn_hs sn)), (bytes (hs_ck (sn_hs sn)), (bytes (hs_ts (sn_hs sn)),
  Vint (hs_rindex (sn_hs sn)))))))))))))))))).
Proof. reflexivity. Qed.

Lemma hrx5_B8RBK2_idx_acc (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
  hrx5_B8RBK_acc (@field_at W Ews t_hsnap (DOT HM._index) e s)
    (@data_at W Ews t_hsnap
      (a, (b, (c, (d, (e, (f, (g, (h, (l1, (l2, (l3, (l4, (l5, (l6, (l7, (l8, ri)))))))))))))))) s).
Proof.
  rewrite hrx5_B8RBK2_snap_split.
  do 12 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.

Lemma hrx5_B8RBK2_nfld_idx N nx sn : hn_snap N = hsnap_val sn ->
  hrx5_B8RBK_acc (@field_at W Ews t_hsnap [StructField HM._index] (Vint (e_index (sn_entry sn))) (offset_val 8 (hn_addr N)))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBK_nv N nx) (hn_addr N)).
Proof.
  intros Hs.
  eapply hrx5_B8RBK_acc_trans; [| apply hrx5_B8RBK_nfld_snap].
  apply hrx5_B8RBK_acc_pure with (c := @field_compatible CKS t_hnode4 [] (hn_addr N)).
  { eapply derives_trans; [apply field_at_local_facts |]. apply prop_derives.
    intros ((A1 & A2 & A3 & A4 & _) & _); repeat split; auto. }
  intros FC. rewrite (hrx5_B8RBK_snap_at _ _ FC), Hs, hrx5_B8RBK2_hsnap_eq.
  apply hrx5_B8RBK2_idx_acc.
Qed.

Lemma hrx5_B8RBK2_node_idx NSs l N sn : In N NSs -> hn_snap N = hsnap_val sn ->
  hnodes_rep4 W l NSs |--
  @field_at W Ews t_hsnap [StructField HM._index] (Vint (e_index (sn_entry sn))) (offset_val 8 (hn_addr N)) *
  (@field_at W Ews t_hsnap [StructField HM._index] (Vint (e_index (sn_entry sn))) (offset_val 8 (hn_addr N)) -*
   hnodes_rep4 W l NSs).
Proof.
  intros Hin Hs. exact (hrx5_B8RBK_nodes_acc _ N NSs l Hin (fun nx => hrx5_B8RBK2_nfld_idx N nx sn Hs)).
Qed.

Lemma hrx5_B8RB_K2_ok : hrx5_B8RB_K2_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Ssk hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_K2.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HPall end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  pose proof HPall as HP.
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG HFF]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA, hrx5_B8RB_FS in HFF. cbn [fold_right] in HG, HFF, HP0.
  destruct HG as (HGo & _).
  subst o. clear HP0 HFF.
  abbreviate_semax.
  pose proof HPall as HP.
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG HFF]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA, hrx5_B8RB_FS in HFF. cbn [fold_right] in HG, HFF, HP0.
  destruct HP0 as (Hbase & Hinv & Hst & Hi & Hobj & Hmc & Hacc & Hrd & _).
  destruct HG as (_ & HGfwd & HGai & HGar & HGtgt & HGj & HGPS & HGnp & HGtg & HGlen & HGN & HGsf & HGvin & HGep
    & HGet & HGal & HGfa & HGfr & _).
  destruct HFF as ((HFa & HFPS & HFT & HFKS & HFS & HFin & HFsf & HFz & HFx & _) & HFs & HFk & HFvh & HFvk & HFsk
    & HFinit & HFri & HFrefs & HFclr & HFw & HFWx & _).
  assert (Hsf: sfind PS a = Some (Ews, P)).
  { destruct Hinv as (_ & _ & HND & _). exact (hrx5_B8RBK_sfind_Znth PS j a Ews P HND HGj HGPS). }
  assert (HT3: rw_T (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6
    port (OResp M) dp d) = hrx5_B8RB_T3 T a (rd_k d)) by (rewrite HFT, HFs; reflexivity).
  assert (HFKS': rw_KS (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6
    port (OResp M) dp d) = [(rd_k d, hrx5_B8RB_K P M ck h kc (hrx5_B8RB_S1 x25519 R L sec birth S q lul (OResp M) d))])
    by (rewrite HFKS, HFs; reflexivity).
  set (N := Znth j (hnodes_snapped4 T NS PS)) in HGN.
  assert (HNin: In N (hnodes_snapped4 T NS PS)).
  { apply Znth_In. rewrite hrx5_B8RBK_snapped_len by exact HGlen. lia. }
  assert (HNa: hn_addr N = tg) by (rewrite HGN; reflexivity).
  assert (HNp: hn_p N = a) by (rewrite HGN; reflexivity).
  assert (HNs: hn_snap N = hsnap_val (hs_snap_cur T a P)) by (rewrite HGN; reflexivity).
  assert (HPT: hrx5_ptrs dp (OResp M) = [temp HM._buf nullval; temp HM._mi nullval; temp HM._mr dp;
    temp HM._mc nullval]) by reflexivity.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  rewrite HPT.
  unfold hrx5_B8R_tl, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. Intros.
  rewrite HFPS, (hrx5_B8RBK_peers PS a Ews P (hrx5_B8RB_Pz d P M ck h) Hsf).
  rewrite (hrx5_B8RBK_itab x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
    (OResp M) dp d), HT3.
  rewrite HFKS'. unfold keypairs_rep. cbn [iter_sepcon keypair_item_rep]. rewrite sepcon_emp.
  unfold obj_rep. rewrite hrx5_B8RBK_resp_W. Intros.
  set (k := rd_k d) in *.
  set (K := hrx5_B8RB_K P M ck h kc (hrx5_B8RB_S1 x25519 R L sec birth S q lul (OResp M) d)) in *.
  set (T3 := hrx5_B8RB_T3 T a k) in *.
  set (Pz := hrx5_B8RB_Pz d P M ck h) in *.
  assert_PROP (@field_compatible Noise.CS t_kp [] k) as Hfck.
  { sep_apply (hrx5_B8RBK_kp_fc k K). entailer!. }
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca.
  { unfold peer_rep at 1. entailer!. }
  freeze FR0 := - (itable _ _ _) (peer_rep _ _ _) (hnodes_rep4 _ _ _) (keypair_rep _ _ _) (data_at _ t_resp _ _).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'179 (Vint Int.one) :: Q) (SEPx R))) end.
  { apply denote_tc_test_eq_split.
    - sep_apply (hrx5_B8RBK2_itab_vp (l_itd L) _ k _ HFsk). apply sepcon_valid_pointer1, derives_refl.
    - auto with valid_pointer. }
  { sep_apply (hrx5_B8RBK_kp_init k K). Intros. rewrite HFinit.
    change (Val.of_bool true) with (Vint Int.one).
    forward. forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    entailer!. }
  { exfalso. exact (HFk H0). }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'180 (Vint Int.one) :: Q) (SEPx R))) end.
  { sep_apply (hrx5_B8RBK_kentry (l_itd L) T3 k _ HFsk Hfck). Intros.
    rewrite HFvk. unfold entry_val. cbn [e_peer e_type e_index Val.of_bool].
    assert (Hpa: is_pointer_or_null a) by (destruct Hfca as [Hp _]; destruct a; try contradiction; simpl; auto).
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    pose proof (hrx5_B8RBK_nodes_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) N
      (hnodes_snapped4 T NS PS) (hrx5_head (hnodes_snapped4 T NS PS)) HNin (fun nx => hrx5_B8RBK_nfld_p N nx)) as HA.
    unfold hrx5_B8RBK_acc in HA. sep_apply HA. clear HA. Intros.
    rewrite HNa, HNp.
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        match goal with |- _ |-- valid_pointer ?x =>
          apply derives_trans with (peer_rep Ews x Pz * TT); [cancel |];
          apply sepcon_valid_pointer1, hrx5_B8RBK_vp_peer; apply readable_nonidentity; auto end. }
    rewrite hrx5_B8RBK2_eqp by exact Hpa.
    entailer!. }
  { exfalso. apply Int.one_not_zero. assumption. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'181 (Vint Int.one) :: Q) (SEPx R))) end.
  { sep_apply (hrx5_B8RBK_kentry (l_itd L) T3 k _ HFsk Hfck). Intros.
    rewrite HFvk. unfold entry_val. cbn [e_peer e_type e_index Val.of_bool].
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    sep_apply (hrx5_B8RBK2_node_idx (hnodes_snapped4 T NS PS) (hrx5_head (hnodes_snapped4 T NS PS)) N
      (hs_snap_cur T a P) HNin HNs). Intros.
    rewrite HNa.
    change (e_index (sn_entry (hs_snap_cur T a P))) with (e_index (t_entry_d T (hs_addr a))).
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    forward.
    entailer!. rewrite Int.eq_true. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'182 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward_call (Tsh, l_itd L, T3, k).
    all: try (solve [destruct Hfck as [Hp _]; exact Hp]).
    { entailer!. simpl. destruct Hfck as [Hp _]. destruct k; try contradiction. simpl. rewrite Ptrofs.add_zero.
      reflexivity. }
    { apply (hrx5_B8RBK2_saddrs _ _ _ _ HFsk). }
    rewrite HFvk.
    forward.
    entailer!. }
  { exfalso. apply Int.one_not_zero. assumption. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'184 (Vint Int.one) :: Q) (SEPx R))) end.
  { sep_apply (hrx5_B8RBK_kp_rindex k K). Intros. rewrite HFri.
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    forward.
    forward.
    entailer!. rewrite Int.eq_true. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  forward_if.
  { match goal with H: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end. }
  { forward. apply andp_left2. apply LOCALx_shuffle_derives. hrx5_B8RBK2_sub. }
  forward.
  { destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. unfold loop2_ret_assert. cbn [RA_break RA_normal].
    apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate, overridePost.
  destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_normal].
  thaw FR0.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1.
  rewrite HFPS, (hrx5_B8RBK_peers PS a Ews P Pz Hsf).
  rewrite (hrx5_B8RBK_itab x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
    (OResp M) dp d), HT3.
  rewrite HFKS'. unfold keypairs_rep. cbn [iter_sepcon keypair_item_rep]. rewrite sepcon_emp.
  unfold obj_rep. rewrite hrx5_B8RBK_resp_W, (prop_true_andp _ _ H).
  apply andp_left2. apply hrx5_B8RBK2_close; [exact HPall | hrx5_B8RBK2_sub |].
  cbn [fold_right_sepcon]. cancel.
Qed.
