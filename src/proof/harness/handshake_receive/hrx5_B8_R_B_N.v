(* law handshake_receive: B8 branch R segment B: DEAD = CHECK(h->entry.hashed && index kept && frees + 1).
*)
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
Local Open Scope logic.

#[local] Instance hrx5_B8RBN_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_B8RBN_cceKW : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

(* ---- access wands ---- *)
Definition hrx5_B8RBN_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B8RBN_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B8RBN_acc_refl Q : hrx5_B8RBN_acc Q Q.
Proof.
  unfold hrx5_B8RBN_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B8RBN_acc_eq Q A : Q = A -> hrx5_B8RBN_acc Q A.
Proof. intros ->. apply hrx5_B8RBN_acc_refl. Qed.

Lemma hrx5_B8RBN_acc_l Q A F : hrx5_B8RBN_acc Q A -> hrx5_B8RBN_acc Q (A * F).
Proof.
  unfold hrx5_B8RBN_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B8RBN_acc_r Q A F : hrx5_B8RBN_acc Q A -> hrx5_B8RBN_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B8RBN_acc_l, H. Qed.

Lemma hrx5_B8RBN_acc_prop Q (c: Prop) A : (c -> hrx5_B8RBN_acc Q A) -> hrx5_B8RBN_acc Q (!! c && A).
Proof.
  unfold hrx5_B8RBN_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RBN_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B8RBN_acc Q (A x)) -> hrx5_B8RBN_acc Q (EX x, A x).
Proof.
  unfold hrx5_B8RBN_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply (exp_right x), derives_refl.
Qed.

Lemma hrx5_B8RBN_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B8RBN_acc Q A) -> hrx5_B8RBN_acc Q A.
Proof.
  unfold hrx5_B8RBN_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B8RBN_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hrx5_B8RBN_acc Q (f x) -> hrx5_B8RBN_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hrx5_B8RBN_acc_l, H | apply hrx5_B8RBN_acc_r, IH, Hin].
Qed.

Lemma hrx5_B8RBN_acc_trans Q B P : hrx5_B8RBN_acc Q B -> hrx5_B8RBN_acc B P -> hrx5_B8RBN_acc Q P.
Proof.
  unfold hrx5_B8RBN_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RBN_fW sh t gfs (v: @reptype Noise.CS (@nested_field_type Noise.CS t gfs))
  (v': @reptype W (@nested_field_type W t gfs)) p :
  JMeq v v' -> cs_preserve_type Noise.CS W (@coeq _ _ hrx5_B8RBN_cceN) t = true ->
  @field_at Noise.CS sh t gfs v p = @field_at W sh t gfs v' p.
Proof. intros H1 H2. exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W _ sh t gfs v v' H1 H2)). Qed.

(* ---- the peer a: its handshake is field compatible ---- *)
Lemma hrx5_B8RBN_in_supd {A: Type} : forall (l: list (val * share * A)) a sh (P Q: A),
  In (a, sh, P) l -> exists sh', In (a, sh', Q) (supd l a Q).
Proof.
  induction l as [|[[x sh0] v] l IH]; simpl; intros a sh P Q Hin; [contradiction|].
  destruct (EqDec_val x a) as [<-|Hne].
  - exists sh0. left. reflexivity.
  - destruct Hin as [Heq|Hin]; [inversion Heq; congruence|].
    destruct (IH a sh P Q Hin) as [sh' H']. exists sh'. right. exact H'.
Qed.

Lemma hrx5_B8RBN_peer_fc sh a Q : peer_rep sh a Q |-- !! (@field_compatible Noise.CS t_hs [] (hs_addr a)).
Proof.
  unfold peer_rep, hs_rep. Intros. entailer!.
  match goal with H: @field_compatible Noise.CS t_hs [StructField I._state] (hs_addr a) |- _ =>
    destruct H as (? & ? & ? & ? & ?) end.
  repeat split; auto.
Qed.

Lemma hrx5_B8RBN_peers_fc PS a sh P Q : In (a, sh, P) PS ->
  peers_rep (supd PS a Q) |-- !! (@field_compatible Noise.CS t_hs [] (hs_addr a)) && peers_rep (supd PS a Q).
Proof.
  intros Hin. destruct (hrx5_B8RBN_in_supd PS a sh P Q Hin) as [sh' Hin'].
  apply andp_right; [| apply derives_refl].
  assert (HA: hrx5_B8RBN_acc (peer_rep sh' a Q) (peers_rep (supd PS a Q))).
  { unfold peers_rep. apply (hrx5_B8RBN_acc_iter _ _ (a, sh', Q)); [exact Hin' | apply hrx5_B8RBN_acc_refl]. }
  eapply derives_trans; [exact HA|].
  sep_apply (hrx5_B8RBN_peer_fc sh' a Q). entailer!.
Qed.

(* ---- the handshake's entry in the pool of T ---- *)
Lemma hrx5_B8RBN_entry_eq sh h (v: @reptype Noise.CS t_entry_s) : @field_compatible Noise.CS t_hs [] h ->
  @data_at Noise.CS sh t_entry_s v h = @field_at W sh t_hs [StructField I._entry] v h.
Proof.
  intros FC. rewrite <- (hrx5_B8RBN_fW sh t_hs [StructField I._entry] v v h (JMeq_refl _)) by (vm_compute; reflexivity).
  rewrite (@field_at_data_at Noise.CS sh t_hs [StructField I._entry]), field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

Lemma hrx5_B8RBN_sfind_in {A: Type} : forall (D: list (val * share * A)) x sh v,
  sfind D x = Some (sh, v) -> In (x, sh, v) D.
Proof.
  induction D as [|[[y sh0] v0] D IH]; simpl; intros x sh v Hf; [discriminate|].
  destruct (EqDec_val y x) as [<-|Hne]; [inversion Hf; subst; left; reflexivity | right; apply IH, Hf].
Qed.

Lemma hrx5_B8RBN_entry tab T x : sfind (t_D T) x = Some (Ews, t_entry_d T x) ->
  @field_compatible Noise.CS t_hs [] x ->
  itable Tsh tab T |--
  @field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x *
  (@field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x -*
   itable Tsh tab T).
Proof.
  intros Hf FC.
  change (hrx5_B8RBN_acc
    (@field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x)
    (itable Tsh tab T)).
  unfold itable. apply hrx5_B8RBN_acc_prop; intros _. apply hrx5_B8RBN_acc_r.
  apply (hrx5_B8RBN_acc_iter _ _ (x, Ews, t_entry_d T x)); [exact (hrx5_B8RBN_sfind_in _ _ _ _ Hf) |].
  apply hrx5_B8RBN_acc_eq. unfold pool_item_rep, entry_at.
  rewrite hrx5_B8RBN_entry_eq by exact FC. reflexivity.
Qed.

(* ---- the node's handshake snapshot (at s = offset_val 8 node), at W ---- *)
Definition hrx5_B8RBN_nv (N: hnode4) (nx: val) : @reptype CKS t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hrx5_B8RBN_nodes_acc (Q: mpred) N : forall NS l, In N NS ->
  (forall nx, hrx5_B8RBN_acc Q (@data_at CKS Ews t_hnode4 (hrx5_B8RBN_nv N nx) (hn_addr N))) ->
  hrx5_B8RBN_acc Q (hnodes_rep4 W l NS).
Proof.
  induction NS as [|N0 NS IH]; intros l Hin HQ; [destruct Hin|]. cbn [hnodes_rep4].
  apply hrx5_B8RBN_acc_prop; intros Hl. apply hrx5_B8RBN_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hrx5_B8RBN_acc_l, hrx5_B8RBN_acc_l, hrx5_B8RBN_acc_r. apply HQ.
  - apply hrx5_B8RBN_acc_r, IH; auto.
Qed.

Lemma hrx5_B8RBN_nfld_snap N nx :
  hrx5_B8RBN_acc (@field_at CKS Ews t_hnode4 [StructField HC._snap] (hn_snap N) (hn_addr N))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBN_nv N nx) (hn_addr N)).
Proof.
  unfold hrx5_B8RBN_acc, hrx5_B8RBN_nv.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._snap) _ (hn_snap N) (hn_addr N));
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (hn_snap N)). apply derives_refl.
Qed.

Lemma hrx5_B8RBN_snap_at (v: @reptype CKS t_hsnap) x : @field_compatible CKS t_hnode4 [] x ->
  @field_at CKS Ews t_hnode4 [StructField HC._snap] v x = @data_at W Ews t_hsnap v (offset_val 8 x).
Proof.
  intros FC. rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
  change (@nested_field_offset CKS t_hnode4 [StructField HC._snap]) with 8.
  change (@nested_field_type CKS t_hnode4 [StructField HC._snap]) with t_hsnap.
  apply (f_equal (fun f => f (offset_val 8 x))). apply (@data_at_change_composite CKS W _ Ews t_hsnap); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_B8RBN_node_snap NS l N : In N NS ->
  hnodes_rep4 W l NS |--
  @data_at W Ews t_hsnap (hn_snap N) (offset_val 8 (hn_addr N)) *
  (@data_at W Ews t_hsnap (hn_snap N) (offset_val 8 (hn_addr N)) -* hnodes_rep4 W l NS).
Proof.
  intros Hin.
  change (hrx5_B8RBN_acc (@data_at W Ews t_hsnap (hn_snap N) (offset_val 8 (hn_addr N))) (hnodes_rep4 W l NS)).
  apply (hrx5_B8RBN_nodes_acc _ N NS l Hin). intros nx.
  apply hrx5_B8RBN_acc_pure with (c := @field_compatible CKS t_hnode4 [] (hn_addr N)).
  { eapply derives_trans; [apply (@data_at_local_facts CKS)|]. apply prop_derives. intros [FC _]; exact FC. }
  intros FC. eapply hrx5_B8RBN_acc_trans; [| apply (hrx5_B8RBN_nfld_snap N nx)].
  apply hrx5_B8RBN_acc_eq. rewrite hrx5_B8RBN_snap_at by exact FC. reflexivity.
Qed.

(* only the snapshot's index field (the whole t_hsnap value in the SEP makes the kernel re-run reptype conversions) *)
Lemma hrx5_B8RBN_snap_idx sn y :
  hrx5_B8RBN_acc (@field_at W Ews t_hsnap (DOT HM._index) (Vint (e_index (sn_entry sn))) y)
    (@data_at W Ews t_hsnap (hsnap_val sn) y).
Proof.
  unfold hrx5_B8RBN_acc.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts W) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif W Ews t_hsnap [] (StructField HM._index) (hsnap_val sn)
    (Vint (e_index (sn_entry sn))) y); [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (Vint (e_index (sn_entry sn)))).
  unfold hsnap_val. apply derives_refl.
Qed.

Lemma hrx5_B8RBN_node_idx NS l x p sn r rs : In (mkHN4 x p (hsnap_val sn) r rs) NS ->
  hnodes_rep4 W l NS |--
  @field_at W Ews t_hsnap (DOT HM._index) (Vint (e_index (sn_entry sn))) (offset_val 8 x) *
  (@field_at W Ews t_hsnap (DOT HM._index) (Vint (e_index (sn_entry sn))) (offset_val 8 x) -* hnodes_rep4 W l NS).
Proof.
  intros Hin.
  change (hrx5_B8RBN_acc (@field_at W Ews t_hsnap (DOT HM._index) (Vint (e_index (sn_entry sn))) (offset_val 8 x))
    (hnodes_rep4 W l NS)).
  eapply hrx5_B8RBN_acc_trans; [apply hrx5_B8RBN_snap_idx|].
  exact (hrx5_B8RBN_node_snap NS l _ Hin).
Qed.

Lemma hrx5_B8RBN_tulong {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hrx5_B8RBN_ss sh v p : @data_at CKS sh t_shimsnap v p = @data_at W sh t_shimsnap v p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite CKS W _ sh t_shimsnap); [apply JMeq_refl | reflexivity].
Qed.

(* Q' a sublist of Q, element by element *)
Ltac hrx5_B8RBN_sub :=
  let Q0 := fresh "Q0" in let HQ := fresh "HQ" in
  intros Q0 HQ; simpl In in HQ;
  repeat (destruct HQ as [<- | HQ]; [simpl In; repeat (first [left; reflexivity | right]) | ]);
  contradiction.

Ltac hrx5_B8RBN_contra :=
  exfalso;
  match goal with
  | H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: typed_false _ (Vint Int.one) |- _ => cbv in H; discriminate H
  | H: typed_true _ _ |- _ => cbv in H; discriminate H
  end.

Ltac hrx5_B8RBN_conj :=
  first [ exact I | assumption | split; hrx5_B8RBN_conj ].

Lemma hrx5_B8RB_DEAD_ok : hrx5_B8RB_DEAD_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Sn hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_DEAD.
  abbreviate_semax.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HP end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG [HFA [Hsess _]]]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA in HFA. cbn [fold_right] in HG, HFA.
  rewrite Hsess in HFA.
  destruct HFA as (HFal & HFPS & HFT & HFKS & HFS & HFin & HFsf & HFz & HFx & _).
  destruct HG as (HG1 & HG2 & HG3 & HG4 & HG5 & HG6 & HG7 & HG8 & HG9 & HG10 & HG11 & HG12 & HG13 & HG14 & HG15
    & HGal & HGfa & HGfr & _).
  clear HP0.
  assert (HinN: In (Znth j (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)).
  { apply Znth_In. unfold hnodes_snapped4. rewrite Zlength_map, Zlength_correct, combine_length.
    assert (E: Datatypes.length NS = Datatypes.length PS).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact HG10. }
    rewrite E, Nat.min_id, <- Zlength_correct. exact HG6. }
  rewrite HG11 in HinN.
  assert (HinP: In (a, Ews, P) PS) by (rewrite <- HG7; apply Znth_In; exact HG6).
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. rewrite HFT, HFPS, HFS. rewrite Hsess. unfold shim_state4, shim_core.
  cbn [s_allocs s_fails s_frees shim_free shim_alloc_ok]. rewrite HGfr.
  Intros.
  rewrite (hrx5_B8RBN_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_B8RBN_ss Tsh _ (l_ss L)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  sep_apply (hrx5_B8RBN_peers_fc PS a Ews P (hrx5_B8RB_Pz d P M ck h) HinP). Intros.
  sep_apply (hrx5_B8RBN_entry (d_itab (rw_D (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T
    kc lul q proto ip4 ip6 port o dp d))) T (hs_addr a) HG12 H8).
  sep_apply (hrx5_B8RBN_node_idx (hnodes_snapped4 T NS PS) (hrx5_head (hnodes_snapped4 T NS PS)) _ _ _ _ _ HinN).
  rewrite HG13.
  Intros.
  unfold entry_val.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'185 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    change (e_index (sn_entry (hs_snap_cur T a P))) with (e_index (t_entry_d T (hs_addr a))).
    rewrite Int.eq_true. apply andp_left2. apply LOCALx_shuffle_derives.
    hrx5_B8RBN_sub.
  }
  { hrx5_B8RBN_contra. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'186 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    replace (Int64.repr (Int.signed (Int.repr 1))) with Int64.one by reflexivity.
    unfold Int64.cmpu. rewrite Int64.eq_true. apply andp_left2. apply LOCALx_shuffle_derives.
    hrx5_B8RBN_sub.
  }
  { hrx5_B8RBN_contra. }
  forward_if.
  { hrx5_B8RBN_contra. }
  { forward. apply andp_left2. apply LOCALx_shuffle_derives. hrx5_B8RBN_sub. }
  forward.
  { destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. unfold loop2_ret_assert. cbn [RA_break RA_normal].
    apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate, overridePost.
  destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_normal].
  match goal with |- context [SEPx (?f :: _)] => sep_apply (hrx5_B8RBN_mp f) end.
  match goal with |- context [SEPx (_ :: ?f :: _)] => sep_apply (hrx5_B8RBN_mp f) end.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. rewrite HFT, HFPS, HFS. rewrite Hsess. unfold shim_state4, shim_core.
  rewrite (prop_true_andp (shim_ok _) _ H7).
  cbn [s_allocs s_fails s_frees shim_free shim_alloc_ok]. rewrite HGfr.
  rewrite (hrx5_B8RBN_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_B8RBN_ss Tsh _ (l_ss L)).
  apply andp_left2.
  apply andp_derives; [apply prop_derives; intros _ | ].
  2: { apply andp_derives; [apply derives_refl |]. intro rho. unfold SEPx. cbn [fold_right_sepcon]. cancel. }
  unfold hrx5_B8RB_G, hrx5_B8RB_FA. cbv zeta. rewrite Hsess. cbn [fold_right app].
  hrx5_B8RBN_conj.
Qed.
