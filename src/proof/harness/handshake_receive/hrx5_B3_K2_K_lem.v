(* law handshake_receive, B3 K2 segment K: helpers of hrx5_B3_K2_K.v,
   copied from of the hrx5_B3_K0_I2_lem.v (the node of nk focused on its field p, the peer split / rejoin
   over supd, the new world after k_response). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

Notation W := W_handshake_receive.
#[local] Existing Instance W_handshake_receive.

#[local] Instance hrx5_k2k_cceK : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.
#[local] Instance hrx5_k2k_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.

(* ---- the field p of the node of nk: focus with a wand (port of cookie_reply's hcy5_p11_B_node) ---- *)
Lemma hrx5_k2k_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_k2k_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hrx5_k2k_node h NS N v :
  In N NS -> hn_p N = v ->
  hnodes_rep4 W h NS |--
  @field_at W Ews t_hnode4 (DOT HC._p) v (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HC._p) v (hn_addr N) -* hnodes_rep4 W h NS).
Proof.
  intros Hin <-. revert h. induction NS as [| N0 NS IH]; intros h; [contradiction |].
  destruct Hin as [-> | Hin].
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N) * @malloc_token W Ews t_peer (hn_p N) *
       hnodes_rep4 W nx NS *
       (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N))))%logic.
    + sep_apply (hrx5_k2k_node1 N nx). cancel.
    + apply hrx5_k2k_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hrx5_k2k_wand_frame. Exists nx. entailer!.
Qed.

(* ---- the peers: split at p, rejoin over supd ---- *)
Lemma hrx5_k2k_supd {A: Type} (D: list (val * share * A)) a sh E E' (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f (supd D a E') = f (a, sh, E') * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] y] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  simpl. rewrite (IH H). rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

(* ---- the response struct at the world compspecs ---- *)
Lemma hrx5_k2k_resp_W sh m M :
  resp_rep sh m M = !! rm_ok M && @data_at W sh t_resp (resp_val M) m.
Proof.
  unfold resp_rep.
  rewrite (@data_at_change_composite Noise.CS W _ sh t_resp _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  reflexivity.
Qed.

(* ---- the new world after k_response ---- *)
Lemma hrx5_k2k_sfind_supd {A: Type} (D: list (val * share * A)) a sh E E' :
  sfind D a = Some (sh, E) -> sfind (supd D a E') a = Some (sh, E').
Proof.
  induction D as [|[[x shx] y] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a).
  - inv H. simpl. destruct (EqDec_val a a); [reflexivity | contradiction].
  - simpl. destruct (EqDec_val x a); [contradiction|]. auto.
Qed.

Lemma hrx5_k2k_world x25519 R L NS PS KE T head nk sec birth S p P (b: bool) idx :
  hrx5_B3_lem_stmt x25519 -> hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk ->
  sfind PS p = Some (Ews, P) -> hrx5_pok x25519 R L (p, Ews, P) ->
  hrx5_base_ok R sec birth
    (if (b && negb (vin (hs_addr p) (t_L T)))%bool then shim_u32 S idx else S) /\
  hrx5_inv x25519 R L NS
    (supd PS p (if b then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P)) KE
    (if (b && negb (vin (hs_addr p) (t_L T)))%bool then t_insert T (hs_addr p) idx else T) head nk.
Proof.
  intros (HL1 & HL2 & _ & _ & HL5 & _) HB HI HP HOK.
  set (P' := if b then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P).
  assert (HOK': hrx5_pok x25519 R L (p, Ews, P')).
  { subst P'; destruct b; [| exact HOK]. exact HOK. }
  assert (HKN: p_pknext P' = p_pknext P) by (subst P'; destruct b; reflexivity).
  assert (HI' := HL1 _ _ _ _ _ _ _ _ _ _ _ _ HI HP HOK' HKN).
  assert (HP' := hrx5_k2k_sfind_supd PS p Ews P P' HP).
  split.
  - destruct (_ && _)%bool; [apply HL5 |]; exact HB.
  - destruct (_ && _)%bool; [eapply HL2; eauto | exact HI'].
Qed.

(* ---- the nodes: valid and proper pointers ---- *)
Lemma hrx5_k2k_vp NS : forall l N, In N NS -> hnodes_rep4 W l NS |-- valid_pointer (hn_addr N).
Proof.
  induction NS as [|N0 NS IH]; intros l N HIn; [destruct HIn |].
  simpl hnodes_rep4. Intros nx. destruct HIn as [<- | HIn].
  - subst l. entailer!.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hrx5_k2k_isptr NS : forall l N, In N NS -> hnodes_rep4 W l NS |-- !! isptr (hn_addr N).
Proof.
  induction NS as [|N0 NS IH]; intros l N HIn; [destruct HIn |].
  simpl hnodes_rep4. Intros nx. destruct HIn as [<- | HIn].
  - subst l. entailer!. match goal with Hf: field_compatible _ _ _ |- _ => apply Hf end.
  - sep_apply (IH nx N HIn). entailer!.
Qed.

(* ---- D's identity: 32-byte keys ---- *)
Lemma hrx5_k2k_id_len x25519 R :
  x25519_props x25519 -> hrx5_run_ok R ->
  Zlength (mi_priv (hrx5_ID x25519 R)) = 32 /\ Zlength (mi_pub (hrx5_ID x25519 R)) = 32.
Proof.
  intros HX (HB & _). unfold hrx5_ID, mident_of; cbn [mi_priv mi_pub]. split; [| apply HX].
  unfold clamp. rewrite !upd_Znth_Zlength; auto; try rewrite upd_Znth_Zlength; lia.
Qed.
