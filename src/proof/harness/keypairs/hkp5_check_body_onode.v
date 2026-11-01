(* law keypairs: the segment ONODE (one node of the others loop).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

Local Open Scope logic.

#[local] Instance hkc5o_cce_CKS : change_composite_env CKS W_keypairs.
Proof. make_cs_preserve CKS W_keypairs. Defined.
#[local] Instance hkc5o_cce_HCS : change_composite_env W_keypairs HCS.
Proof. make_cs_preserve W_keypairs HCS. Defined.
#[local] Instance hkc5o_cce_N : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Definition hkc5o_snapf (N: hnode4) (l: val) : mpred :=
  @field_at CKS Ews t_hnode4 (DOT KC._snap) (hn_snap N) l.
Definition hkc5o_restf (N: hnode4) (l: val) : mpred :=
  @field_at CKS Ews t_hnode4 (DOT KC._rest) (hn_rest N) l.

Lemma hkc5o_cell N nx l :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l =
  field_at Ews t_hnode4 (DOT KC._p) (hn_p N) l * hkc5o_snapf N l *
  field_at Ews t_hnode4 (DOT KC._refs) (hn_refs N) l * spacer Ews 300 304 l * hkc5o_restf N l *
  field_at Ews t_hnode4 (DOT KC._next) nx l.
Proof.
  unfold hkc5o_snapf, hkc5o_restf. unfold data_at. unfold_field_at 1%nat.
  change WgNoise.harness.x_cookie_mac.code._p with KC._p. change WgNoise.harness.x_cookie_mac.code._snap with KC._snap.
  change WgNoise.harness.x_cookie_mac.code._refs with KC._refs. change WgNoise.harness.x_cookie_mac.code._rest with KC._rest.
  change WgNoise.harness.x_cookie_mac.code._next with KC._next.
  rewrite (@field_at_change_composite CKS W_keypairs _ Ews t_hnode4 (DOT KC._p) (hn_p N) (hn_p N)) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_change_composite CKS W_keypairs _ Ews t_hnode4 (DOT KC._refs) (hn_refs N) (hn_refs N)) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_change_composite CKS W_keypairs _ Ews t_hnode4 (DOT KC._next) nx nx) by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hkc5o_fa f l :
  In f [KC._snap; KC._rest] ->
  @field_address CKS t_hnode4 (DOT f) l = @field_address W_keypairs t_hnode4 (DOT f) l.
Proof.
  intros Hf. unfold field_address.
  assert (Hc: @field_compatible CKS t_hnode4 (DOT f) l <-> @field_compatible W_keypairs t_hnode4 (DOT f) l)
    by (apply (@field_compatible_change_composite CKS W_keypairs hkc5o_cce_CKS); reflexivity).
  destruct (@field_compatible_dec CKS t_hnode4 (DOT f) l) as [H1|H1];
  destruct (@field_compatible_dec W_keypairs t_hnode4 (DOT f) l) as [H2|H2]; try tauto.
Qed.

Lemma hkc5o_snap N sn l :
  @eq (@reptype CKS t_hsnap) (hn_snap N) (hsnap_val sn) ->
  hkc5o_snapf N l = @data_at HCS Ews t_hsnap (hsnap_val sn) (field_address t_hnode4 (DOT KC._snap) l).
Proof.
  unfold hkc5o_snapf. intros E. rewrite E.
  rewrite (@field_at_data_at CKS), hkc5o_fa by (simpl; auto).
  change (@nested_field_type CKS t_hnode4 (DOT KC._snap)) with t_hsnap.
  rewrite (@data_at_change_composite CKS W_keypairs _ Ews t_hsnap (hsnap_val sn) (hsnap_val sn)) by (apply JMeq_refl || reflexivity).
  apply equal_f. apply (@data_at_change_composite W_keypairs HCS _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hkc5o_rest N P0 l :
  hn_rest N = prsnap_val P0 ->
  hkc5o_restf N l = @data_at CKS Ews t_prsnap (prsnap_val P0) (field_address t_hnode4 (DOT KC._rest) l).
Proof.
  unfold hkc5o_restf. intros E. rewrite E.
  rewrite (@field_at_data_at CKS), hkc5o_fa by (simpl; auto).
  change (@nested_field_type CKS t_hnode4 (DOT KC._rest)) with t_prsnap. reflexivity.
Qed.

Lemma hkc5o_snapW N sn l :
  @eq (@reptype CKS t_hsnap) (hn_snap N) (hsnap_val sn) ->
  hkc5o_snapf N l = field_at Ews t_hnode4 (DOT KC._snap) (hsnap_val sn) l.
Proof.
  unfold hkc5o_snapf. intros E. rewrite E.
  apply equal_f. apply (@field_at_change_composite CKS W_keypairs _); [apply JMeq_refl | reflexivity].
Qed.

Definition hkc5o_acc (Q P: mpred) : Prop := (P |-- Q * (Q -* P))%logic.

Lemma hkc5o_mp (Q P: mpred) : (Q * (Q -* P) |-- P)%logic.
Proof. apply wand_frame_elim. Qed.

Lemma hkc5o_acc_refl Q : hkc5o_acc Q Q.
Proof.
  unfold hkc5o_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon.
  apply derives_refl.
Qed.

Lemma hkc5o_acc_eq Q A : Q = A -> hkc5o_acc Q A.
Proof. intros ->. apply hkc5o_acc_refl. Qed.

Lemma hkc5o_acc_l Q A F : hkc5o_acc Q A -> hkc5o_acc Q (A * F)%logic.
Proof.
  unfold hkc5o_acc. intros H. apply derives_trans with (Q * (Q -* A) * F)%logic.
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)%logic), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)%logic),
    (sepcon_comm (Q -* A)%logic Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hkc5o_acc_r Q A F : hkc5o_acc Q A -> hkc5o_acc Q (F * A)%logic.
Proof. intros H. rewrite sepcon_comm. apply hkc5o_acc_l, H. Qed.

Lemma hkc5o_acc_prop Q (c: Prop) A : (c -> hkc5o_acc Q A) -> hkc5o_acc Q (!! c && A)%logic.
Proof.
  unfold hkc5o_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm.
  apply modus_ponens_wand.
Qed.

(* P's reference count at W_keypairs *)
Lemma hkc5o_peer_refs sh p P :
  hkc5o_acc (field_at sh (Tstruct KC._wg_peer noattr) [StructField KC._refcount] (Vint (p_refs P)) p)
    (peer_rep sh p P).
Proof.
  unfold peer_rep. apply hkc5o_acc_prop; intros _.
  do 4 apply hkc5o_acc_l. apply hkc5o_acc_r. apply hkc5o_acc_eq.
  rewrite (@field_at_change_composite Noise.CS W_keypairs _ sh t_peer [StructField I._refcount]
    (Vint (p_refs P)) (Vint (p_refs P)) (JMeq_refl _)) by prove_cs_preserve_type.
  reflexivity.
Qed.

Lemma hkc5o_vo_it sh t T VO :
  vobjs W_keypairs (VItab sh t T :: VO) = itable sh t T * vobjs W_keypairs VO.
Proof. reflexivity. Qed.

Lemma hkc5_onode_ok : hkc5_onode_stmt.
Proof.
  intros Espec F T N nx q sh Q VO n FR R Hok.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost, hkc5_PON, hkc5_lv, hkc5_onode, hkc5_Delta, hkc5_G.
  abbreviate_semax.
  destruct Hok as (sn & Hp & Hsn & Hr & Hrest & Hsh & Hvo & Hin & Hv1 & Hv2 & Heq1 & Heq2 & Hh).
  assert_PROP (@field_compatible W_keypairs t_hnode4 [] (hn_addr N)) as FCo.
  { entailer!. apply (@field_compatible_change_composite CKS W_keypairs hkc5o_cce_CKS); [reflexivity | auto]. }
  assert (FCs: field_compatible t_hnode4 (DOT KC._snap) (hn_addr N)) by auto with field_compatible.
  assert (FCr: field_compatible t_hnode4 (DOT KC._rest) (hn_addr N)) by auto with field_compatible.
  rewrite hkc5o_cell. rewrite Hp, Hr. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Noise.CS t_peer [] q) as FCq by (unfold peer_rep; entailer!).
  assert (Pq: isptr q) by (destruct FCq; auto).
  forward.
  rewrite (hkc5o_snap N sn (hn_addr N) Hsn).
  change (peer_rep sh q Q) with (hs_mem true sh q Q).
  forward_call (Ews, field_address t_hnode4 (DOT KC._snap) (hn_addr N), sn, sh, q, Q, true, Tsh, f_t F, T, VO).
  rewrite Heq1. change (hs_mem true sh q Q) with (peer_rep sh q Q).
  rewrite <- (hkc5o_snap N sn (hn_addr N) Hsn).
  forward_if (temp KC._t'38 (Vint Int.zero)).
  { exfalso. first [discriminate | congruence | lia]. }
  { forward.
    pose proof (hkc5o_peer_refs sh q Q) as Acc. unfold hkc5o_acc in Acc. sep_apply Acc. Intros.
    forward. forward. forward.
    sep_apply (hkc5o_mp (field_at sh (Tstruct KC._wg_peer noattr) [StructField KC._refcount] (Vint (p_refs Q)) q)).
    entailer!.
    rewrite Int.eq_true. reflexivity. }
  forward_if (temp KC._t'39 (Vint Int.zero)).
  { exfalso. first [discriminate | congruence | lia]. }
  { forward.
    rewrite (hkc5o_rest N Q (hn_addr N) Hrest).
    gather_SEP (itable Tsh (f_t F) T) (vobjs W_keypairs VO). rewrite <- hkc5o_vo_it.
    forward_call (Ews, field_address t_hnode4 (DOT KC._rest) (hn_addr N), Q, sh, q, Q, VItab Tsh (f_t F) T :: VO).
    { constructor; auto. simpl. auto. }
    rewrite hkc5o_vo_it, Heq2. repeat flatten_sepcon_in_SEP.
    rewrite <- (hkc5o_rest N Q (hn_addr N) Hrest).
    forward. entailer!. }
  forward_if.
  { exfalso. first [discriminate | congruence | lia]. }
  rewrite (hkc5o_snapW N sn (hn_addr N) Hsn).
  forward.
  { entailer!. destruct (sn_hashed sn); cbv; auto. }
  match goal with |- context [temp KC._t'47 ?v] => change v with (Val.of_bool (sn_hashed sn)) end.
  rewrite Hh. rewrite <- (hkc5o_snapW N sn (hn_addr N) Hsn).
  destruct (vin (hs_addr q) (t_L T)) eqn:HV.
  - forward_if.
    2: { exfalso. first [discriminate | congruence | lia]. }
    forward.
    forward_call (Tsh, f_t F, T, hs_addr q).
    rewrite HV.
    forward_if.
    { exfalso. first [discriminate | congruence | lia]. }
    forward.
    rewrite (hkc5o_cell N nx (hn_addr N)). rewrite Hp, Hr. entailer!.
  - forward_if.
    { exfalso. first [discriminate | congruence | lia]. }
    forward.
    rewrite (hkc5o_cell N nx (hn_addr N)). rewrite Hp, Hr. entailer!.
Qed.
