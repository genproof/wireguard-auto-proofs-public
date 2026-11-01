(* law consume_initiation_any: helpers of
   hci5_p5_B.v (statement 18, the replay boundary).  Accessors copied from hci5_P6.v under the prefix
   hci5_p5B_; the latest_timestamp field of a peer split off peer_rep (so that ANY 12 bytes can be put back), one
   peer of peers_rep split off, and the invariant hci5_inv after A's latest timestamp changed. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

#[local] Instance hci5_p5B_cceK : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.
#[local] Instance hci5_p5B_cceNH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Section hci5_p5B_helpers.
Local Open Scope logic.
(* ---- accessors: P |-- Q * (Q -* P) ---- *)
Definition hci5_p5B_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hci5_p5B_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hci5_p5B_acc_refl Q : hci5_p5B_acc Q Q.
Proof.
  unfold hci5_p5B_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hci5_p5B_acc_l Q A F : hci5_p5B_acc Q A -> hci5_p5B_acc Q (A * F).
Proof.
  unfold hci5_p5B_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hci5_p5B_acc_r Q A F : hci5_p5B_acc Q A -> hci5_p5B_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hci5_p5B_acc_l, H. Qed.

Lemma hci5_p5B_acc_prop Q (c: Prop) A : (c -> hci5_p5B_acc Q A) -> hci5_p5B_acc Q (!! c && A).
Proof.
  unfold hci5_p5B_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hci5_p5B_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hci5_p5B_acc Q (A x)) -> hci5_p5B_acc Q (EX x, A x).
Proof.
  unfold hci5_p5B_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

(* the node's field p, at the world *)
Lemma hci5_p5B_node_split p sn r rs nx x :
  @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x |--
  @field_at W Ews t_hnode4 [StructField HC._p] p x *
  (@field_at W Ews t_hnode4 [StructField HC._p] p x -* @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ p x); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

Lemma hci5_p5B_node_acc l NS N : In N NS ->
  hci5_p5B_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) (hnodes_rep4 W l NS).
Proof.
  revert l; induction NS as [|N0 NS IH]; intros l Hin; [destruct Hin|]. cbn [hnodes_rep4].
  apply hci5_p5B_acc_prop; intros Hl. apply hci5_p5B_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hci5_p5B_acc_l, hci5_p5B_acc_l, hci5_p5B_acc_r. apply hci5_p5B_node_split.
  - apply hci5_p5B_acc_r, IH, Hin.
Qed.

End hci5_p5B_helpers.

(* ---- A's latest timestamp ---- *)
Definition hci5_p5B_hs (H: handshake) (t: list byte) : handshake :=
  mkHS (hs_state H) (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_reph H) (hs_ss H) (hs_psk H)
       (hs_hash H) (hs_ck H) t (hs_rindex H).
Definition hci5_p5B_set (P: peer) (t: list byte) : peer := p_set_hs P (hci5_p5B_hs (p_hs P) t).

Lemma hci5_p5B_set_same P : hci5_p5B_set P (hs_ts (p_hs P)) = P.
Proof. destruct P as [? ? ? ? ? H ? ? ? ? ?]; destruct H; reflexivity. Qed.

Section hci5_p5B_N.
#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* the handshake without its latest timestamp *)
Definition hci5_p5B_hsr (sh: share) (h: val) (H: handshake) : mpred :=
  !! (field_compatible t_hs [StructField I._latest_timestamp] h /\
      Zlength (hs_eph H) = 32 /\ Zlength (hs_rstatic H) = 32 /\ Zlength (hs_reph H) = 32 /\
      Zlength (hs_ss H) = 32 /\ Zlength (hs_psk H) = 32 /\ Zlength (hs_hash H) = 32 /\
      Zlength (hs_ck H) = 32) &&
  (field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
   field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
   field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   field_at sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
   field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
   field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
   field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h).

Lemma hci5_p5B_ts_field sh h t : Zlength t = 12 ->
  field_compatible t_hs [StructField I._latest_timestamp] h ->
  field_at sh t_hs [StructField I._latest_timestamp] (bytes t) h = hbytes sh t (offset_val 280 h).
Proof.
  intros Hl FC. rewrite field_at_data_at, field_address_offset by auto. unfold hbytes. rewrite Hl.
  change (nested_field_type t_hs [StructField I._latest_timestamp]) with (tarray tuchar 12).
  exact (f_equal (fun f => f _) (@data_at_change_composite Noise.CS HCS _ sh (tarray tuchar 12) _ _ (JMeq_refl _) eq_refl)).
Qed.

Lemma hci5_p5B_hs_split sh h H t : Zlength t = 12 ->
  hs_rep sh h (hci5_p5B_hs H t) = hbytes sh t (offset_val 280 h) * hci5_p5B_hsr sh h H.
Proof.
  intros Hl. unfold hs_rep, hci5_p5B_hsr, hs_ok, hci5_p5B_hs. cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph
    hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  apply pred_ext.
  - Intros. assert_PROP (field_compatible t_hs [StructField I._latest_timestamp] h) as FC by entailer!.
    rewrite (hci5_p5B_ts_field sh h t Hl FC). Intros lk. Exists lk. entailer!.
  - Intros lk. rewrite <- (hci5_p5B_ts_field sh h t) by tauto. Exists lk. entailer!.
Qed.

(* the peer without its handshake's latest timestamp *)
Definition hci5_p5B_pr (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hci5_p5B_hsr sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hci5_p5B_peer_split sh p P t : Zlength t = 12 -> isptr p ->
  peer_rep sh p (hci5_p5B_set P t) = hbytes sh t (offset_val 328 p) * hci5_p5B_pr sh p P.
Proof.
  intros Hl Hp. unfold peer_rep, hci5_p5B_pr, hci5_p5B_set, p_set_hs.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  rewrite (hci5_p5B_hs_split sh (hs_addr p) (p_hs P) t Hl).
  replace (offset_val 280 (hs_addr p)) with (offset_val 328 p)
    by (unfold hs_addr; rewrite offset_offset_val; reflexivity).
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hci5_p5B_peer_ok sh p P : peer_rep sh p P |-- !! (hs_ok (p_hs P) /\ isptr p).
Proof. unfold peer_rep, hs_rep. Intros. entailer!. Qed.

End hci5_p5B_N.

(* ---- one peer of peers_rep ---- *)
Definition hci5_p5B_dpeer : peer :=
  mkPeer Vundef false Vundef Vundef Vundef (mkHS Int.zero Int64.zero Vundef [] [] [] [] [] [] [] [] Int.zero)
         Int64.zero (mkCookie Int64.zero false [] false [] [] []) Int.zero Int64.zero Vundef.
#[export] Instance hci5_p5B_inh : Inhabitant (val * share * peer) := (Vundef, Share.bot, hci5_p5B_dpeer).

Definition hci5_p5B_fr (i: Z) (PS: list (val * share * peer)) : mpred :=
  (iter_sepcon peer_item_rep (sublist 0 i PS) * iter_sepcon peer_item_rep (sublist (i + 1) (Zlength PS) PS))%logic.

Lemma hci5_p5B_peers_upd PS i y : 0 <= i < Zlength PS ->
  peers_rep (upd_Znth i PS y) = (peer_item_rep y * hci5_p5B_fr i PS)%logic.
Proof.
  intros Hi. unfold peers_rep, hci5_p5B_fr. rewrite upd_Znth_unfold by auto.
  rewrite !iter_sepcon_app. simpl. rewrite sepcon_emp.
  apply pred_ext; cancel.
Qed.

Lemma hci5_p5B_peers_at PS i : 0 <= i < Zlength PS ->
  peers_rep PS = (peer_item_rep (Znth i PS) * hci5_p5B_fr i PS)%logic.
Proof.
  intros Hi. rewrite <- hci5_p5B_peers_upd by auto. rewrite upd_Znth_triv by auto. reflexivity.
Qed.

(* ---- the invariant after A's latest timestamp changed ---- *)
Lemma hci5_p5B_chain PS : forall head i a sh P sh' P',
  pk_chain head PS -> 0 <= i < Zlength PS -> Znth i PS = (a, sh, P) -> p_pknext P' = p_pknext P ->
  pk_chain head (upd_Znth i PS (a, sh', P')).
Proof.
  induction PS as [| [[a0 sh0] P0] PS IH]; intros head i a sh P sh' P' Hc Hi Hz Hn.
  - rewrite Zlength_nil in Hi; lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite upd_Znth0. rewrite Znth_0_cons in Hz. inversion Hz; subst. cbn in *. rewrite Hn. exact Hc.
    + rewrite upd_Znth_cons by lia. rewrite Znth_pos_cons in Hz by lia. rewrite Zlength_cons in Hi.
      cbn in *. destruct Hc as [Hh Hc]. split; [exact Hh |]. eapply IH; eauto. lia.
Qed.

Lemma hci5_p5B_addrs PS i a sh P y : 0 <= i < Zlength PS -> Znth i PS = (a, sh, P) -> peer_addr4 y = a ->
  map peer_addr4 (upd_Znth i PS y) = map peer_addr4 PS.
Proof.
  intros Hi Hz Hy. rewrite <- upd_Znth_map. apply upd_Znth_triv.
  - rewrite Zlength_map; auto.
  - rewrite Znth_map by auto. rewrite Hz, Hy. reflexivity.
Qed.

Lemma hci5_p5B_T_ok PS PS' KE T : map peer_addr4 PS' = map peer_addr4 PS -> hci5_T_ok PS KE T -> hci5_T_ok PS' KE T.
Proof.
  intros Hm (H1 & H2 & H3 & H4). unfold hci5_T_ok.
  replace (map (fun x => hs_addr (peer_addr4 x)) PS') with (map (fun x => hs_addr (peer_addr4 x)) PS)
    by (rewrite <- !(map_map peer_addr4 hs_addr), Hm; reflexivity).
  rewrite Hm. split; [exact H1 | split; [exact H2 | split; [| exact H4]]].
  rewrite Forall_forall in *. intros x Hx.
  assert (Hin: In (peer_addr4 x) (map peer_addr4 PS)) by (rewrite <- Hm; apply in_map; auto).
  apply in_map_iff in Hin. destruct Hin as (y & Hy & Hy'). rewrite <- Hy. apply H3; auto.
Qed.

Lemma hci5_p5B_inv x25519 R L NS PS KE T head na i a sh P t :
  hci5_inv x25519 R L NS PS KE T head na -> 0 <= i < Zlength PS -> Znth i PS = (a, sh, P) -> Zlength t = 12 ->
  hci5_inv x25519 R L NS (upd_Znth i PS (a, sh, hci5_p5B_set P t)) KE T head na.
Proof.
  intros (Hpok & Hwf & Hch & Hnp & Hna & HT & Hsl) Hi Hz Hl.
  assert (Hm: map peer_addr4 (upd_Znth i PS (a, sh, hci5_p5B_set P t)) = map peer_addr4 PS)
    by (eapply hci5_p5B_addrs; eauto).
  assert (Hx: hci5_pok x25519 R L (a, sh, P)) by (rewrite <- Hz; exact (proj1 (Forall_Znth _ _) Hpok i Hi)).
  unfold hci5_inv. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply Forall_upd_Znth; [exact Hpok |].
    destruct Hx as (? & ? & ? & Hok & ? & ? & ? & ?). cbn.
    unfold hs_ok in *. cbn. repeat split; tauto.
  - unfold peers_wf in *. apply Forall_upd_Znth; [exact Hwf |].
    pose proof (proj1 (Forall_Znth _ _) Hwf i Hi) as Hw. rewrite Hz in Hw. exact Hw.
  - eapply hci5_p5B_chain; eauto.
  - unfold hnodes_peers4 in *. rewrite Hm. exact Hnp.
  - exact Hna.
  - eapply hci5_p5B_T_ok; eauto.
  - unfold hci5_slots_ok in *. apply Forall_upd_Znth; [exact Hsl |].
    pose proof (proj1 (Forall_Znth _ _) Hsl i Hi) as Hw. rewrite Hz in Hw. exact Hw.
Qed.

(* a node index and its peer *)
Lemma hci5_p5B_find NS PS N : hnodes_peers4 NS PS -> In N NS ->
  exists i, 0 <= i < Zlength PS /\ peer_addr4 (Znth i PS) = hn_p N.
Proof.
  intros Hnp HN. apply In_Znth in HN. destruct HN as (i & Hi & Hz).
  assert (HL: Zlength NS = Zlength PS)
    by (rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS), Hnp; reflexivity).
  exists i. split; [lia |].
  rewrite <- Znth_map by lia. rewrite <- Hnp, Znth_map by lia. rewrite Hz. reflexivity.
Qed.
