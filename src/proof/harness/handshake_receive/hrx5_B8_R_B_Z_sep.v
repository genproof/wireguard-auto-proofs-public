(* law handshake_receive: B8 branch R segment B: Z helpers: node snapshot / peer / shim counter access wands, pure facts.
   Prefix hrx5_b8rbz_. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.protocol.prot_cs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

#[local] Instance hrx5_b8rbz_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_b8rbz_cceKH : change_composite_env CKS HCS.
Proof. make_cs_preserve CKS HCS. Defined.

Section Helpers.

(* a node's fields *)
Definition hrx5_b8rbz_flds (N: hnode4) (nx: val) : mpred :=
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) (hn_addr N) *
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_addr N) *
  spacer Ews 300 304 (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._next) nx (hn_addr N).

Lemma hrx5_b8rbz_cell N nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) =
  hrx5_b8rbz_flds N nx.
Proof.
  unfold hrx5_b8rbz_flds. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS W_handshake_receive _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS W_handshake_receive _ Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_refs N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hrx5_b8rbz_node NS1 N NS2 : forall l,
  hnodes_rep4 W_handshake_receive l (NS1 ++ N :: NS2) |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hrx5_b8rbz_flds N nx *
     (hrx5_b8rbz_flds N nx -* hnodes_rep4 W_handshake_receive l (NS1 ++ N :: NS2))).
Proof.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx.
    assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as Hfc.
    { sep_apply (@data_at_local_facts CKS). entailer!. }
    rewrite hrx5_b8rbz_cell. entailer!.
    rewrite <- wand_sepcon_adjoint. Exists nx. rewrite hrx5_b8rbz_cell. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. entailer!.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hrx5_b8rbz_snap N sn l : @field_compatible CKS t_hnode4 [] l -> hn_snap N = hsnap_val sn ->
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) l = @data_at HCS Ews t_hsnap (hsnap_val sn) (offset_val 8 l).
Proof.
  intros Hfc E. rewrite E.
  rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
  apply (@data_at_cs_eq CKS HCS hrx5_b8rbz_cceKH); [apply JMeq_refl | reflexivity].
Qed.

(* the snapshot of node j, with the access wand *)
Lemma hrx5_b8rbz_nsnap X j N sn l :
  0 <= j < Zlength X -> Znth j X = N -> hn_snap N = hsnap_val sn ->
  hnodes_rep4 W_handshake_receive l X |--
  @data_at HCS Ews t_hsnap (hsnap_val sn) (offset_val 8 (hn_addr N)) *
  (@data_at HCS Ews t_hsnap (hsnap_val sn) (offset_val 8 (hn_addr N)) -* hnodes_rep4 W_handshake_receive l X).
Proof.
  intros Hj HN Hs.
  assert (HX: X = sublist 0 j X ++ N :: sublist (j + 1) (Zlength X) X).
  { subst N. rewrite <- (sublist_same 0 (Zlength X) X) at 1 by lia. rewrite (sublist_split 0 j (Zlength X)) by lia.
    rewrite (sublist_split j (j+1) (Zlength X)) by lia. rewrite sublist_len_1 by lia. reflexivity. }
  rewrite HX at 1. sep_apply (hrx5_b8rbz_node (sublist 0 j X) N (sublist (j + 1) (Zlength X) X) l).
  rewrite <- HX. Intros nx.
  unfold hrx5_b8rbz_flds at 1. rewrite (hrx5_b8rbz_snap N sn (hn_addr N) H Hs).
  match goal with |- ?a1 * ?a2 * ?a3 * ?a4 * ?a5 * ?a6 * ?W |-- _ =>
    apply derives_trans with (a2 * ((a1 * a3 * a4 * a5 * a6) * W)); [cancel|] end.
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  match goal with |- context [(?D -* ?Y)] =>
    apply derives_trans with (D * (D -* Y)); [|apply modus_ponens_wand] end.
  unfold hrx5_b8rbz_flds. rewrite (hrx5_b8rbz_snap N sn (hn_addr N) H Hs). cancel.
Qed.

Lemma hrx5_b8rbz_papp PS1 x PS2 : peers_rep (PS1 ++ x :: PS2) = peer_item_rep x * peers_rep (PS1 ++ PS2).
Proof. unfold peers_rep. rewrite !iter_sepcon_app. simpl. apply pred_ext; cancel. Qed.

Lemma hrx5_b8rbz_split (PS: list (val * share * peer)) a sh P P' :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  exists PS1 PS2, supd PS a P' = PS1 ++ (a, sh, P') :: PS2.
Proof.
  intros Hnd Hin. destruct (in_split _ _ Hin) as (PS1 & PS2 & E). exists PS1, PS2.
  subst PS. rewrite map_app in Hnd. cbn [map peer_addr4] in Hnd.
  apply NoDup_remove_2 in Hnd. clear Hin.
  induction PS1 as [|[[x s] w] PS1 IH]; simpl.
  - rewrite if_true by reflexivity. reflexivity.
  - simpl in Hnd. rewrite if_false by (intros ->; apply Hnd; left; reflexivity).
    f_equal. apply IH. intros Hx. apply Hnd. right. exact Hx.
Qed.

(* the peer at a in an updated list, with the access wand *)
Lemma hrx5_b8rbz_peer PS PS' a P P' :
  NoDup (map peer_addr4 PS) -> In (a, Ews, P) PS -> PS' = supd PS a P' ->
  peers_rep PS' |-- peer_rep Ews a P' * (peer_rep Ews a P' -* peers_rep PS').
Proof.
  intros Hnd Hin ->.
  destruct (hrx5_b8rbz_split PS a Ews P P' Hnd Hin) as (PS1 & PS2 & E). rewrite E.
  rewrite hrx5_b8rbz_papp. unfold peer_item_rep.
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. apply derives_refl.
Qed.

Lemma hrx5_b8rbz_tulong {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

(* the two counters of the shim, with the access wand *)
Lemma hrx5_b8rbz_shim gv S w :
  shim_state4 gv S w |--
  (@data_at W_handshake_receive Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at W_handshake_receive Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures)) *
  ((@data_at W_handshake_receive Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
    @data_at W_handshake_receive Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures)) -*
   shim_state4 gv S w).
Proof.
  unfold shim_state4, shim_core. Intros.
  rewrite (hrx5_b8rbz_tulong (cs1 := Noise.CS) (cs2 := W_handshake_receive) Ews _ (gv _wg_shim_allocs)).
  rewrite (hrx5_b8rbz_tulong (cs1 := Noise.CS) (cs2 := W_handshake_receive) Ews _ (gv _wg_shim_alloc_failures)).
  match goal with |- ?b1 * ?b2 * ?b3 * ?b4 * ?b5 * ?b6 * ?A * ?F * ?b9 * ?b10 * ?b11 * ?b12 * ?rw |-- _ =>
    apply derives_trans with ((A * F) * (b1 * b2 * b3 * b4 * b5 * b6 * b9 * b10 * b11 * b12 * rw)); [cancel|] end.
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hrx5_b8rbz_ss sh v p : @data_at CKS sh t_shimsnap v p = @data_at W_handshake_receive sh t_shimsnap v p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite CKS W_handshake_receive _ sh t_shimsnap);
    [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_b8rbz_dev sh wg D : device_rep sh wg D = vobjs W_handshake_receive [VDev sh wg D].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

End Helpers.

(* ---------------------------------------------------------------------- *)
(* pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b8rbz_snapped_len T NS PS : Zlength NS = Zlength PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength NS.
Proof.
  intros E. unfold hnodes_snapped4. rewrite Zlength_map, !Zlength_correct, combine_length.
  rewrite !Zlength_correct in E. rewrite Nat.min_l by lia. reflexivity.
Qed.

Lemma hrx5_b8rbz_pok x25519 R L NS PS KE T head nk j a P :
  hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= j < Zlength PS -> Znth j PS = (a, Ews, P) ->
  NoDup (map peer_addr4 PS) /\ In (a, Ews, P) PS /\ hs_sid (p_hs P) = id_addr (l_wd L).
Proof.
  intros (Hpok & _ & Hnd & _) Hj HP.
  assert (Hin: In (a, Ews, P) PS) by (rewrite <- HP; apply Znth_In; exact Hj).
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hk. unfold hrx5_pok in Hk.
  destruct Hk as (_ & _ & Hsid & _). auto.
Qed.

Lemma hrx5_b8rbz_vp T T' a P Pz wg D :
  zeroed_from (hs_snap_cur T a P) (hs_snap_cur T' a Pz) = true ->
  e_peer (t_entry_d T (hs_addr a)) = a -> hs_sid (p_hs P) = id_addr wg ->
  Forall (vp_ok (hs_own a T' [VDev Tsh wg D])) (hs_ptrs_nn (hs_snap_cur T a P) (hs_snap_cur T' a Pz)).
Proof.
  intros Hz He Hs.
  unfold zeroed_from in Hz. cbv zeta in Hz.
  destruct (eq_dec (e_peer (sn_entry (hs_snap_cur T a P))) (e_peer (sn_entry (hs_snap_cur T' a Pz)))) as [Ep|];
    [| rewrite ?andb_false_r, ?andb_false_l in Hz; discriminate].
  destruct (eq_dec (hs_sid (sn_hs (hs_snap_cur T a P))) (hs_sid (sn_hs (hs_snap_cur T' a Pz)))) as [Es|];
    [| rewrite ?andb_false_r, ?andb_false_l in Hz; discriminate].
  unfold hs_ptrs_nn. rewrite <- Ep, <- Es.
  unfold hs_snap_cur, snap_of in *; cbn [sn_entry sn_hs] in *. rewrite He, Hs.
  unfold hs_own, vobjs_addrs. cbn [map vobj_addrs concat].
  rewrite app_nil_r.
  repeat apply Forall_cons; try apply Forall_nil; right.
  all: first [left; reflexivity | right; apply in_or_app; right; simpl; auto].
Qed.

(* closing a segment whose precondition dropped its PROPs (kept in the context) *)
Lemma hrx5_b8rbz_fin {cs: compspecs} Delta (Pl: list Prop) Q Q' R R' :
  fold_right and True Pl -> (forall q, In q Q -> In q Q') -> fold_right_sepcon R' |-- fold_right_sepcon R ->
  ENTAIL Delta, PROPx [] (LOCALx Q' (SEPx R')) |-- PROPx Pl (LOCALx Q (SEPx R)).
Proof.
  intros HP HQ HR. apply andp_left2.
  eapply derives_trans; [apply (LOCALx_shuffle_derives [] Q' Q R'); exact HQ|].
  unfold PROPx, LOCALx, SEPx. intro rho. simpl.
  apply andp_derives; [apply prop_derives; intros _; exact HP|].
  apply andp_derives; [apply derives_refl | apply HR].
Qed.
