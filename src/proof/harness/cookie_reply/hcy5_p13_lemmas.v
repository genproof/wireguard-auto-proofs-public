(* law cookie_reply, phase P13: the separation facts of the
   frees (port of v1's hcy4_p13_lemmas.v).  A cnode back to its whole struct (data_at_ at the world W, for free),
   the kents' entries (A's pool) as kents_free4's data_at_, the peers (peers_rep plus their handshake entries from
   A's pool) back to whole struct wg_peer at W (hnodes_free4), the snapshot locals back to data_at_ W. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.

Local Open Scope logic.

#[local] Instance hcy5_p13_cn_cce : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p13_cn_conv p : @data_at_ CKS Ews t_cksnap p = @data_at_ W Ews t_cksnap p.
Proof. rewrite (@data_at__change_composite CKS W _ Ews t_cksnap); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hcy5_p13_cn_rep o p : hcy5_cs_rep o p |-- @data_at_ W Ews t_cksnap p.
Proof.
  destruct o; unfold hcy5_cs_rep; rewrite <- hcy5_p13_cn_conv; [apply data_at_data_at_ | apply derives_refl].
Qed.

(* the snapshot locals (taken at CKS) back to the stack frame's data_at_ W *)
Lemma hcy5_p13_devsnap sh v p : @data_at CKS sh t_devsnap v p |-- @data_at_ W sh t_devsnap p.
Proof.
  sep_apply (@data_at_data_at_ CKS sh t_devsnap v p).
  rewrite (@data_at__change_composite CKS W _ sh t_devsnap); [apply derives_refl | prove_cs_preserve_type].
Qed.

Lemma hcy5_p13_shimsnap sh v p : @data_at CKS sh t_shimsnap v p |-- @data_at_ W sh t_shimsnap p.
Proof.
  sep_apply (@data_at_data_at_ CKS sh t_shimsnap v p).
  rewrite (@data_at__change_composite CKS W _ sh t_shimsnap); [apply derives_refl | prove_cs_preserve_type].
Qed.

Section hcy5_p13_cn.
#[local] Existing Instance W_cookie_reply.
Lemma hcy5_p13_cn_split c :
  field_compatible t_cnode5 [] c ->
  data_at_ Ews t_cksnap (offset_val 8 c) * field_at_ Ews t_cnode5 [StructField HY._n] c *
  field_at_ Ews t_cnode5 [StructField HY._next] c |-- data_at_ Ews t_cnode5 c.
Proof.
  intros Hc. unfold t_cnode5 in *. unfold_data_at (data_at_ Ews (Tstruct HY._cnode noattr) c).
  unfold field_at_. rewrite (field_at_data_at Ews (Tstruct HY._cnode noattr) [StructField HY._cs]).
  rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_offset. simpl nested_field_type. unfold data_at_, field_at_. cancel.
Qed.
End hcy5_p13_cn.

(* a cnode {n; cs (offset 8); next}: its three fields as the state hcy5_cns keeps them -> the whole struct *)
Lemma hcy5_p13_cnode_whole c nd o nx :
  @field_at W Ews t_cnode5 [StructField HY._n] nd c *
  hcy5_cs_rep o (offset_val 8 c) *
  @field_at W Ews t_cnode5 [StructField HY._next] nx c
  |-- @data_at_ W Ews t_cnode5 c.
Proof.
  assert_PROP (@field_compatible W t_cnode5 [] c) as Hc.
  { entailer!. match goal with H: @field_compatible W t_cnode5 [StructField HY._n] c |- _ =>
      destruct H as (? & ? & ? & ? & ?) end. repeat split; auto. }
  sep_apply (hcy5_p13_cn_rep o (offset_val 8 c)).
  sep_apply (@field_at_field_at_ W Ews t_cnode5 [StructField HY._n] nd c).
  sep_apply (@field_at_field_at_ W Ews t_cnode5 [StructField HY._next] nx c).
  eapply derives_trans; [| apply (hcy5_p13_cn_split c Hc)]. cancel.
Qed.

(* the kents' entries (the first items of A's pool, any owners and indices) -> kents_free4's precondition *)
Lemma hcy5_p13_kents own ix (KE: list kent4) :
  iter_sepcon hcy5_pool_item (map (hcy5_kentry own ix) (map ke_addr KE)) |--
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  induction KE as [| e KE IH]; simpl.
  - apply derives_refl.
  - unfold hcy5_kentry at 1, hcy5_pool_item at 1. Intros n h.
    unfold entry_at. sep_apply (@data_at_data_at_ Noise.CS Ews t_entry_s).
    apply sepcon_derives; [apply derives_refl | exact IH].
Qed.

Lemma hcy5_p13_kents_snapped T (KE: list kent4) :
  map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. induction KE as [| e KE IH]; simpl; [reflexivity | f_equal; exact IH]. Qed.

Lemma hcy5_p13_khead T (KE: list kent4) : hcy5_khead (map (kent_snapped T) KE) = hcy5_khead KE.
Proof. destruct KE; reflexivity. Qed.

Lemma hcy5_p13_kents_ptr l KE : kents_rep W l KE |-- !! is_pointer_or_null l.
Proof.
  destruct KE as [| e KE]; simpl.
  - entailer!.
  - Intros nx. unfold kent_cell. Intros. subst l. entailer!.
Qed.

#[local] Instance hcy5_p13_pe_cce : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Lemma hcy5_p13_pe_conv sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_cookie_reply sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.

(* the peers PS (share Ews) with their handshake entries (the peers' part of A's pool, any indices) -> each node's
   peer as a whole struct wg_peer at W (hnodes_free4's precondition) *)
Lemma hcy5_p13_peers ix (NS: list hnode4) (AS: list val) (PS: list (val * share * peer)) :
  map hn_p NS = AS -> map peer_addr4 PS = AS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  iter_sepcon hcy5_pool_item (map (hcy5_hent ix) AS) * peers_rep PS |--
  iter_sepcon (fun N => @data_at_ W Ews t_peer (hn_p N)) NS.
Proof.
  revert AS PS. induction NS as [| N NS IH]; intros AS PS HN HP HF;
    destruct AS as [| a AS]; try discriminate HN;
    destruct PS as [| [[a' sh] P] PS]; try discriminate HP.
  - simpl. unfold peers_rep. simpl. rewrite sepcon_emp. apply derives_refl.
  - simpl in HN, HP. inv HN. inv HP. inv HF.
    unfold peers_rep. simpl. unfold hcy5_hent at 1, hcy5_pool_item at 1. Intros n h.
    rewrite <- hcy5_p13_pe_conv.
    sep_apply (prot_rep3_peer_whole Ews (hn_p N) P
      (mkEntry (hn_p N) IDX_HANDSHAKE (ix (hs_addr (hn_p N)))) n h).
    cancel. eapply IH; eauto.
Qed.

(* the nodes after hnodes_snap4: the same peers *)
Lemma hcy5_p13_snap_p T NS PS :
  length NS = length PS -> map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  unfold hnodes_snapped4. revert PS.
  induction NS as [| N NS IH]; intros [| x PS] Hl; simpl in *; try discriminate; auto.
  f_equal; [| apply IH; lia].
  destruct x as [[p sh] P]. reflexivity.
Qed.

Lemma hcy5_p13_supd_addr (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [| [[x sh] w] PS IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hcy5_p13_supd_sh (PS: list (val * share * peer)) a P' :
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (supd PS a P').
Proof.
  induction PS as [| [[x sh] w] PS IH]; intros HF; simpl; auto.
  inv HF. destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hcy5_p13_pure L KS T NS PS res :
  hcy5_lists_ok L KS NS PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map peer_addr4 PS /\
  map peer_addr4 (peers_after PS res) = map peer_addr4 PS /\
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (peers_after PS res).
Proof.
  intros (Hpok & Hhp & _ & _).
  assert (HF: Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS).
  { eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hx. exact (proj1 Hx). }
  unfold hnodes_peers4 in Hhp.
  split; [| split].
  - rewrite hcy5_p13_snap_p; [exact Hhp |].
    rewrite <- (map_length hn_p NS), <- (map_length peer_addr4 PS), Hhp. reflexivity.
  - destruct res as [[a P'] |]; simpl; [apply hcy5_p13_supd_addr | reflexivity].
  - destruct res as [[a P'] |]; simpl; [apply hcy5_p13_supd_sh |]; exact HF.
Qed.
