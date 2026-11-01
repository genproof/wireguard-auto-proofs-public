(* law handshake_receive, B4 segment R: separation-logic access for the response
   model block (node, snapshot fields, message halves, id.priv, m_state halves, peers field_compatible).
   Rename-port of consume_response_any's hcr5_q3_sep.v (offsets there). *)
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
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.
Definition hrx5_B4_R_sep_stmt : Prop :=
  (* 1: a node of the list (at W, for main's loads) *)
  (forall NS1 N NS2,
     hnodes_rep4 W (hrx5_head (NS1 ++ N :: NS2)) (NS1 ++ N :: NS2) |--
     @data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) -*
      hnodes_rep4 W (hrx5_head (NS1 ++ N :: NS2)) (NS1 ++ N :: NS2))) /\
  (* 2: the snapshot's ephemeral private key, preshared key, hash and chaining key of a node *)
  (forall sh pp sn r (rs: @reptype CKS t_prsnap) nx x, hs_ok (sn_hs sn) ->
     @data_at W sh t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x |--
     hbytes sh (hs_eph (sn_hs sn)) (offset_val 56 x) * hbytes sh (hs_psk (sn_hs sn)) (offset_val 184 x) *
     hbytes sh (hs_hash (sn_hs sn)) (offset_val 216 x) * hbytes sh (hs_ck (sn_hs sn)) (offset_val 248 x) *
     (hbytes sh (hs_eph (sn_hs sn)) (offset_val 56 x) * hbytes sh (hs_psk (sn_hs sn)) (offset_val 184 x) *
      hbytes sh (hs_hash (sn_hs sn)) (offset_val 216 x) * hbytes sh (hs_ck (sn_hs sn)) (offset_val 248 x) -*
      @data_at W sh t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x)) /\
  (* 3: the nodes: valid pointers, pointers, the head pointer or null *)
  (forall l NS a, In a (map hn_addr NS) -> hnodes_rep4 W l NS |-- valid_pointer a) /\
  (forall l NS, hnodes_rep4 W l NS |-- !! (Forall isptr (map hn_addr NS) /\ is_pointer_or_null l)) /\
  (* 4: the message's ephemeral and encrypted empty payload *)
  (forall sh m M, rm_ok M ->
     @data_at W sh t_resp (resp_val M) m |--
     hbytes sh (rm_eph M) (offset_val 12 m) * hbytes sh (rm_encn M) (offset_val 44 m) *
     (hbytes sh (rm_eph M) (offset_val 12 m) * hbytes sh (rm_encn M) (offset_val 44 m) -*
      @data_at W sh t_resp (resp_val M) m)) /\
  (* 5: ia.priv *)
  (forall sh I p, Zlength (mi_priv I) = 32 ->
     @data_at HCS sh t_mident (mident_val I) p |--
     hbytes sh (mi_priv I) p * (hbytes sh (mi_priv I) p -* @data_at HCS sh t_mident (mident_val I) p)) /\
  (* 6: a struct m_state as its two halves *)
  (forall sh p, @data_at_ HCS sh t_mstate p |--
     !! @field_compatible HCS t_mstate [] p && (hout sh 32 p * hout sh 32 (offset_val 32 p))) /\
  (forall sh ck h p, @field_compatible HCS t_mstate [] p -> Zlength ck = 32 -> Zlength h = 32 ->
     hbytes sh ck p * hbytes sh h (offset_val 32 p) |-- @data_at HCS sh t_mstate (mstate_val ck h) p) /\
  (* 7: the peers are field_compatible (at W) *)
  (forall PS, peers_rep PS |--
     !! Forall (fun x => @field_compatible W t_peer [] (peer_addr4 x)) PS).

(* ---- helpers ---- *)
Definition hrx5_B4_Rs_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B4_Rs_acc_refl Q : hrx5_B4_Rs_acc Q Q.
Proof.
  unfold hrx5_B4_Rs_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B4_Rs_acc_eq Q A : Q = A -> hrx5_B4_Rs_acc Q A.
Proof. intros ->. apply hrx5_B4_Rs_acc_refl. Qed.

Lemma hrx5_B4_Rs_acc_l Q A F : hrx5_B4_Rs_acc Q A -> hrx5_B4_Rs_acc Q (A * F).
Proof.
  unfold hrx5_B4_Rs_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B4_Rs_acc_r Q A F : hrx5_B4_Rs_acc Q A -> hrx5_B4_Rs_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B4_Rs_acc_l, H. Qed.

Lemma hrx5_B4_Rs_acc_prop Q (c: Prop) A : (c -> hrx5_B4_Rs_acc Q A) -> hrx5_B4_Rs_acc Q (!! c && A).
Proof.
  unfold hrx5_B4_Rs_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B4_Rs_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B4_Rs_acc Q (A x)) -> hrx5_B4_Rs_acc Q (EX x, A x).
Proof.
  unfold hrx5_B4_Rs_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hrx5_B4_Rs_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B4_Rs_acc Q A) -> hrx5_B4_Rs_acc Q A.
Proof.
  unfold hrx5_B4_Rs_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

(* compspecs conversions *)
#[local] Instance hrx5_B4_Rs_cce_KW : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.
#[local] Instance hrx5_B4_Rs_cce_HW : change_composite_env HCS W.
Proof. make_cs_preserve HCS W. Defined.
#[local] Instance hrx5_B4_Rs_cce_NW : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.

Lemma hrx5_B4_Rs_KW sh (v: @reptype CKS t_hnode4) x :
  @data_at CKS sh t_hnode4 v x = @data_at W sh t_hnode4 v x.
Proof.
  rewrite (@data_at_change_composite CKS W _ sh t_hnode4 v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_B4_Rs_HW sh (v: @reptype HCS t_hsnap) y :
  @data_at HCS sh t_hsnap v y = @data_at W sh t_hsnap v y.
Proof.
  rewrite (@data_at_change_composite HCS W _ sh t_hsnap v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_B4_Rs_HWa sh n (v: list val) y :
  @data_at HCS sh (tarray tuchar n) v y = @data_at W sh (tarray tuchar n) v y.
Proof.
  rewrite (@data_at_change_composite HCS W _ sh (tarray tuchar n) v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type].
Qed.

(* 1 *)
Lemma hrx5_B4_Rs_head l NS : hnodes_rep4 W l NS |-- !! (l = hrx5_head NS).
Proof. destruct NS as [|N NS]; simpl; entailer!. Qed.

Lemma hrx5_B4_Rs_c1 NS1 N NS2 l :
  hrx5_B4_Rs_acc (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))
    (hnodes_rep4 W l (NS1 ++ N :: NS2)).
Proof.
  revert l; induction NS1 as [|M NS1 IH]; intros l; simpl.
  - apply hrx5_B4_Rs_acc_prop; intros ->. apply hrx5_B4_Rs_acc_ex; intros nx.
    apply hrx5_B4_Rs_acc_pure with (c := nx = hrx5_head NS2).
    { sep_apply (hrx5_B4_Rs_head nx NS2). entailer!. }
    intros ->. do 2 apply hrx5_B4_Rs_acc_l. apply hrx5_B4_Rs_acc_r, hrx5_B4_Rs_acc_refl.
  - apply hrx5_B4_Rs_acc_prop; intros _. apply hrx5_B4_Rs_acc_ex; intros nx.
    apply hrx5_B4_Rs_acc_r, IH.
Qed.

(* 2 *)
Section hrx5_B4_Rs_H.
#[local] Existing Instance HCS.

Lemma hrx5_B4_Rs_snap sh sn y : hs_ok (sn_hs sn) ->
  hrx5_B4_Rs_acc
    (hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 y) * hbytes sh (hs_psk (sn_hs sn)) (offset_val 176 y) *
     hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 y) * hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 y))
    (data_at sh t_hsnap (hsnap_val sn) y).
Proof.
  intros (L1 & _ & _ & _ & L5 & L6 & L7 & _). unfold hrx5_B4_Rs_acc.
  assert_PROP (field_compatible t_hsnap [] y) by entailer!.
  unfold hsnap_val. unfold_data_at (data_at _ _ _ y).
  rewrite (field_at_data_at sh t_hsnap [StructField HH._ephemeral_private]),
          (field_at_data_at sh t_hsnap [StructField HH._preshared_key]),
          (field_at_data_at sh t_hsnap [StructField HH._hash]),
          (field_at_data_at sh t_hsnap [StructField HH._chaining_key]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L1, L5, L6, L7. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

(* 5 *)
Lemma hrx5_B4_Rs_c5 sh I p : Zlength (mi_priv I) = 32 ->
     data_at sh t_mident (mident_val I) p |--
     hbytes sh (mi_priv I) p * (hbytes sh (mi_priv I) p -* data_at sh t_mident (mident_val I) p).
Proof.
  intros L. assert_PROP (field_compatible t_mident [] p) by entailer!.
  unfold mident_val. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident [StructField HH._priv]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L.
  rewrite isptr_offset_val_zero by auto. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

(* 6 *)
Lemma hrx5_B4_Rs_c6a sh p : data_at_ sh t_mstate p |--
     !! field_compatible t_mstate [] p && (hout sh 32 p * hout sh 32 (offset_val 32 p)).
Proof.
  assert_PROP (field_compatible t_mstate [] p) by entailer!.
  apply andp_right; [apply prop_right; auto|].
  rewrite data_at__eq.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HH._ck]),
          (field_at_data_at sh t_mstate [StructField HH._h]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hout.
  rewrite isptr_offset_val_zero by auto. cancel.
Qed.

Lemma hrx5_B4_Rs_c6b sh ck h p : field_compatible t_mstate [] p -> Zlength ck = 32 -> Zlength h = 32 ->
     hbytes sh ck p * hbytes sh h (offset_val 32 p) |-- data_at sh t_mstate (mstate_val ck h) p.
Proof.
  intros FC L1 L2. unfold mstate_val. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HH._ck]),
          (field_at_data_at sh t_mstate [StructField HH._h]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L1, L2.
  rewrite isptr_offset_val_zero by auto. cancel.
Qed.

End hrx5_B4_Rs_H.

Section hrx5_B4_Rs_W.
#[local] Existing Instance W.

Lemma hrx5_B4_Rs_c2 sh (pp: val) sn (r: val) (rs: @reptype CKS t_prsnap) (nx x: val) : hs_ok (sn_hs sn) ->
  hrx5_B4_Rs_acc
    (hbytes sh (hs_eph (sn_hs sn)) (offset_val 56 x) * hbytes sh (hs_psk (sn_hs sn)) (offset_val 184 x) *
     hbytes sh (hs_hash (sn_hs sn)) (offset_val 216 x) * hbytes sh (hs_ck (sn_hs sn)) (offset_val 248 x))
    (@data_at W sh t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x).
Proof.
  intros L. apply hrx5_B4_Rs_acc_pure with (c := field_compatible t_hnode4 [] x); [entailer! | intros FC].
  unfold_data_at (data_at _ _ _ x).
  apply hrx5_B4_Rs_acc_r, hrx5_B4_Rs_acc_l.
  rewrite (field_at_data_at sh t_hnode4 [StructField HC._snap]), field_address_offset by auto with field_compatible.
  change (nested_field_type t_hnode4 [StructField HC._snap]) with t_hsnap.
  rewrite <- hrx5_B4_Rs_HW. simpl (offset_val _ _).
  replace (offset_val 56 x) with (offset_val 48 (offset_val 8 x)) by (rewrite offset_offset_val; reflexivity).
  replace (offset_val 184 x) with (offset_val 176 (offset_val 8 x)) by (rewrite offset_offset_val; reflexivity).
  replace (offset_val 216 x) with (offset_val 208 (offset_val 8 x)) by (rewrite offset_offset_val; reflexivity).
  replace (offset_val 248 x) with (offset_val 240 (offset_val 8 x)) by (rewrite offset_offset_val; reflexivity).
  apply hrx5_B4_Rs_snap, L.
Qed.

(* 4 *)
Lemma hrx5_B4_Rs_c4 sh m M : rm_ok M ->
     @data_at W sh t_resp (resp_val M) m |--
     hbytes sh (rm_eph M) (offset_val 12 m) * hbytes sh (rm_encn M) (offset_val 44 m) *
     (hbytes sh (rm_eph M) (offset_val 12 m) * hbytes sh (rm_encn M) (offset_val 44 m) -*
      @data_at W sh t_resp (resp_val M) m).
Proof.
  intros (L1 & L2 & _). assert_PROP (field_compatible t_resp [] m) by entailer!.
  unfold resp_val. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_resp [StructField I._unencrypted_ephemeral]),
          (field_at_data_at sh t_resp [StructField I._encrypted_nothing]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes.
  rewrite L1, L2, !hrx5_B4_Rs_HWa. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

End hrx5_B4_Rs_W.

(* 3 *)
Lemma hrx5_B4_Rs_c3a l NS a : In a (map hn_addr NS) -> hnodes_rep4 W l NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [|N NS IH]; intros l Hin; simpl in *; [contradiction|].
  Intros nx. destruct Hin as [<-|Hin].
  - subst l. auto with valid_pointer.
  - apply sepcon_valid_pointer2, IH, Hin.
Qed.

Lemma hrx5_B4_Rs_c3b l NS : hnodes_rep4 W l NS |-- !! (Forall isptr (map hn_addr NS) /\ is_pointer_or_null l).
Proof.
  revert l; induction NS as [|N NS IH]; intros l; simpl; [entailer!|].
  Intros nx. subst l. sep_apply (IH nx). Intros. entailer!.
  match goal with Hf: field_compatible t_hnode4 [] (hn_addr N) |- _ => destruct Hf as [HpN _] end.
  split; [constructor; auto | destruct (hn_addr N); try contradiction; simpl; auto].
Qed.

(* 7 *)
Lemma hrx5_B4_Rs_c7 PS : peers_rep PS |-- !! Forall (fun x => @field_compatible W t_peer [] (peer_addr4 x)) PS.
Proof.
  induction PS as [|[[a sh] P] PS IH]; unfold peers_rep in *; simpl; [entailer!|].
  sep_apply IH. unfold peer_rep. Intros.
  apply prop_right. constructor; auto.
  apply (@field_compatible_change_composite Noise.CS W _ t_peer); [prove_cs_preserve_type | auto].
Qed.

Lemma hrx5_B4_R_sep_ok : hrx5_B4_R_sep_stmt.
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - intros NS1 N NS2. rewrite <- !hrx5_B4_Rs_KW. apply hrx5_B4_Rs_c1.
  - intros sh pp sn r rs nx x L. apply hrx5_B4_Rs_c2, L.
  - apply hrx5_B4_Rs_c3a.
  - apply hrx5_B4_Rs_c3b.
  - apply hrx5_B4_Rs_c4.
  - apply hrx5_B4_Rs_c5.
  - apply hrx5_B4_Rs_c6a.
  - apply hrx5_B4_Rs_c6b.
  - apply hrx5_B4_Rs_c7.
Qed.
