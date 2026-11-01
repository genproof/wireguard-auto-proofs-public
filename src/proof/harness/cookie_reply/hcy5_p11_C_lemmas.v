(* (port of v1 hcy4_p11_C_lemmas.v), law cookie_reply, phase P11, segment C:
   separation-logic helpers of hcy5_p11_C.v (statement 69: the decryption with the target cnode's snapshot,
   the CHECK of the accepted peer's cookie).  Prefix hcy5_p11_C_. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

#[local] Instance hcy5_p11_C_cce_K : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p11_C_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p11_C_cce_S : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

(* struct cookie of the harness unit *)
Definition hcy5_p11_C_tck := Tstruct HY._cookie noattr.

(* ---------------------------------------------------------------------- *)
(* small facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p11_C_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p11_C_supd_in (PS: list (val * share * peer)) a sh P P' :
  sfind PS a = Some (sh, P) -> In (a, sh, P') (supd PS a P').
Proof.
  induction PS as [| [[x shx] Px] PS IH]; simpl; [discriminate |].
  match goal with |- context [if ?d then _ else _] => destruct d as [-> | Hne] end; intros Hs.
  - inv Hs. left. reflexivity.
  - right. apply IH. exact Hs.
Qed.

Lemma hcy5_p11_C_sfind_in (PS: list (val * share * peer)) a sh P :
  sfind PS a = Some (sh, P) -> In (a, sh, P) PS.
Proof.
  induction PS as [| [[x shx] Px] PS IH]; simpl; [discriminate |].
  match goal with |- context [if ?d then _ else _] => destruct d as [-> | Hne] end; intros Hs.
  - inv Hs. left. reflexivity.
  - right. apply IH. exact Hs.
Qed.

(* ---------------------------------------------------------------------- *)
(* byte buffers at the world (the AEAD's specification is at W)            *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p11_C_hW sh bs p :
  hbytes sh bs p = @data_at W_cookie_reply sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. unfold hbytes, bytes. apply data_at_tarray_tuchar_cs. Qed.

Lemma hcy5_p11_C_hprim sh bs p : 0 < Zlength bs -> hbytes sh bs p = @prim_bytes W_cookie_reply sh bs p.
Proof.
  intros Hl. unfold prim_bytes. rewrite if_false by lia. apply hcy5_p11_C_hW.
Qed.

Lemma hcy5_p11_C_zp gv : @zero_page Noise.CS gv = @zero_page W_cookie_reply gv.
Proof. unfold zero_page. apply data_at_tarray_tuchar_cs. Qed.

(* the output buffer pt: hout <-> prim_out of its default contents *)
Lemma hcy5_p11_C_hout16 sh p : hout sh 16 p = @prim_out W_cookie_reply sh (Zrepeat Vundef 16) p.
Proof.
  unfold hout, prim_out. rewrite if_false by (cbv; discriminate).
  unfold data_at_. rewrite <- (@data_at_tarray_tuchar_cs HCS W_cookie_reply).
  reflexivity.
Qed.

Lemma hcy5_p11_C_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* ---------------------------------------------------------------------- *)
(* the reply at the world (copy of hcy5_p5_c_cm_open)                      *)
(* ---------------------------------------------------------------------- *)

Definition hcy5_p11_C_cm (sh: share) (rp: val) (CM: cookie_msg) : mpred :=
  (field_at sh t_cmsg (DOT HY._header DOT HY._type) (Vint (cm_type CM)) rp *
   field_at sh t_cmsg (DOT HY._receiver_index) (Vint (cm_receiver CM)) rp *
   hbytes sh (cm_nonce CM) (offset_val 8 rp) *
   hbytes sh (cm_enc CM) (offset_val 32 rp))%logic.

Lemma hcy5_p11_C_cm_open sh rp CM :
  cmsg_rep sh rp CM = (!! (cm_ok CM /\ field_compatible t_cmsg [] rp) && hcy5_p11_C_cm sh rp CM)%logic.
Proof.
  unfold cmsg_rep, hcy5_p11_C_cm, cmsg_val.
  erewrite (@data_at_change_composite Cookie.CS W_cookie_reply _ sh t_cmsg _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  apply pred_ext.
  - Intros. pose proof H as (L1 & L2).
    assert_PROP (field_compatible t_cmsg [] rp) as FC by entailer!.
    unfold hbytes. rewrite L1, L2. rewrite !(@data_at_tarray_tuchar_cs HCS W_cookie_reply).
    unfold_data_at (data_at _ t_cmsg _ rp).
    rewrite (field_at_data_at sh t_cmsg (DOT HY._nonce)), (field_at_data_at sh t_cmsg (DOT HY._encrypted_cookie)).
    rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 1%nat.
    entailer!.
  - Intros. pose proof H as (L1 & L2).
    unfold hbytes. rewrite L1, L2. rewrite !(@data_at_tarray_tuchar_cs HCS W_cookie_reply).
    unfold_data_at (data_at _ t_cmsg _ rp).
    rewrite (field_at_data_at sh t_cmsg (DOT HY._nonce)), (field_at_data_at sh t_cmsg (DOT HY._encrypted_cookie)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 3%nat.
    entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* the cnodes: focus on one                                                *)
(* ---------------------------------------------------------------------- *)

Definition hcy5_p11_C_cn1 (c nd: val) (o: option cookie) : mpred :=
  (@field_at W_cookie_reply Ews t_cnode5 (DOT HY._n) nd c * hcy5_cs_rep o (offset_val 8 c))%logic.

Lemma hcy5_p11_C_wand_split (X F G: mpred) : (X |-- F * G) -> (F * G |-- X) -> X |-- F * (F -* X).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hcy5_p11_C_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p11_C_cns_cons l c nd o B :
  hcy5_cns l ((c, nd, o) :: B) =
  (!! (l = c) &&
   (@malloc_token W_cookie_reply Ews t_cnode5 c *
    @field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd c *
    hcy5_cs_rep o (offset_val 8 c) *
    @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c *
    hcy5_cns (hcy5_chead B) B))%logic.
Proof. reflexivity. Qed.

Lemma hcy5_p11_C_cn l CL1 c nd o CL2 :
  hcy5_cns l (CL1 ++ (c, nd, o) :: CL2) |--
  hcy5_p11_C_cn1 c nd o * (hcy5_p11_C_cn1 c nd o -* hcy5_cns l (CL1 ++ (c, nd, o) :: CL2)).
Proof.
  revert l. induction CL1 as [| [[c1 nd1] o1] CL1 IH]; intros l.
  - simpl app. apply hcy5_p11_C_wand_split with
      (G := (!! (l = c) && (@malloc_token W_cookie_reply Ews t_cnode5 c *
              @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] (hcy5_chead CL2) c *
              hcy5_cns (hcy5_chead CL2) CL2))%logic).
    + rewrite hcy5_p11_C_cns_cons. unfold hcy5_p11_C_cn1. Intros. subst. entailer!.
    + rewrite hcy5_p11_C_cns_cons. unfold hcy5_p11_C_cn1. Intros. subst. entailer!.
  - simpl app. rewrite (hcy5_p11_C_cns_cons l c1 nd1 o1 (CL1 ++ (c, nd, o) :: CL2)) at 1. Intros. subst l.
    sep_apply (IH (hcy5_chead (CL1 ++ (c, nd, o) :: CL2))).
    eapply derives_trans; [| apply (hcy5_p11_C_wand_frame
      (@malloc_token W_cookie_reply Ews t_cnode5 c1 * @field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd1 c1 *
       hcy5_cs_rep o1 (offset_val 8 c1) *
       @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] (hcy5_chead (CL1 ++ (c, nd, o) :: CL2)) c1)%logic
      (hcy5_cns (hcy5_chead (CL1 ++ (c, nd, o) :: CL2)) (CL1 ++ (c, nd, o) :: CL2)))].
    + cancel.
    + rewrite hcy5_p11_C_cns_cons. entailer!.
Qed.

(* the snapshot of a cnode c (field cs, offset 8) at the world: have_sent_mac1 as a field of the cnode (for
   the load target->cs.have_sent_mac1), the three key arrays as byte buffers at their addresses *)
Definition hcy5_p11_C_snrest (C: cookie) (s: val) : mpred :=
  (@field_at CKS Ews t_cksnap (DOT HY._birthdate) (Vlong (ck_birth C)) s *
   @field_at CKS Ews t_cksnap (DOT HY._is_valid) (Val.of_bool (ck_valid C)) s *
   hbytes Ews (ck_cookie C) (offset_val 9 s) *
   spacer Ews 106 112 s)%logic.

Lemma hcy5_p11_C_snap_ok sh C s : @data_at CKS sh t_cksnap (cksnap_val C) s |-- !! cookie_ok C.
Proof.
  entailer!. unfold cksnap_val in H0. simplify_value_fits in H0.
  destruct H0 as (_ & _ & A1 & _ & A2 & A3 & A4). rewrite value_fits_eq in A1, A2, A3, A4.
  simpl in A1, A2, A3, A4. destruct A1 as [A1 _], A2 as [A2 _], A3 as [A3 _], A4 as [A4 _].
  unfold cookie_ok. unfold bytes in *.
  rewrite <- (Zlength_map _ _ Vubyte (ck_cookie C)), <- (Zlength_map _ _ Vubyte (ck_last_mac1 C)),
    <- (Zlength_map _ _ Vubyte (ck_dkey C)), <- (Zlength_map _ _ Vubyte (ck_mkey C)).
  auto.
Qed.

Lemma hcy5_p11_C_snap_split C c :
  cookie_ok C -> @field_compatible W_cookie_reply t_cnode5 [] c ->
  @data_at CKS Ews t_cksnap (cksnap_val C) (offset_val 8 c) =
  (@field_at W_cookie_reply Ews t_cnode5 (DOT HY._cs DOT HY._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
   hbytes Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 c)) *
   hbytes Ews (ck_dkey C) (offset_val 42 (offset_val 8 c)) *
   hbytes Ews (ck_mkey C) (offset_val 74 (offset_val 8 c)) *
   hcy5_p11_C_snrest C (offset_val 8 c))%logic.
Proof.
  intros (L1 & L2 & L3 & L4) FC.
  assert (FC8: @field_compatible W_cookie_reply t_cnode5 (DOT HY._cs) c)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  assert (E8: @field_address W_cookie_reply t_cnode5 (DOT HY._cs) c = offset_val 8 c)
    by (rewrite field_address_offset by exact FC8; reflexivity).
  assert (FCs: @field_compatible W_cookie_reply t_cksnap [] (offset_val 8 c)).
  { exact (field_compatible_nested_field _ _ _ FC8). }
  erewrite (@data_at_change_composite CKS W_cookie_reply _ Ews t_cksnap _ _ (JMeq_refl _)) by reflexivity.
  unfold hcy5_p11_C_snrest.
  erewrite (@field_at_change_composite CKS W_cookie_reply _ Ews t_cksnap (DOT HY._birthdate) _ _ (JMeq_refl _))
    by reflexivity.
  erewrite (@field_at_change_composite CKS W_cookie_reply _ Ews t_cksnap (DOT HY._is_valid) _ _ (JMeq_refl _))
    by reflexivity.
  change [StructField HY._have_sent_mac1; StructField HY._cs] with ([StructField HY._have_sent_mac1] ++ [StructField HY._cs]).
  rewrite (@field_at_app W_cookie_reply Ews t_cnode5 [StructField HY._have_sent_mac1] [StructField HY._cs] _
             (Val.of_bool (ck_sent C)) c (JMeq_refl _)).
  rewrite E8. change (nested_field_type t_cnode5 (DOT HY._cs)) with t_cksnap.
  unfold t_cksnap. unfold_data_at (data_at _ _ _ (offset_val 8 c)).
  rewrite (field_at_data_at Ews (Tstruct HY._ck_snap noattr) (DOT HY._cookie)),
    (field_at_data_at Ews (Tstruct HY._ck_snap noattr) (DOT HY._last_mac1_sent)),
    (field_at_data_at Ews (Tstruct HY._ck_snap noattr) (DOT HY._cookie_decryption_key)),
    (field_at_data_at Ews (Tstruct HY._ck_snap noattr) (DOT HY._message_mac1_key)).
  rewrite !field_address_offset by (destruct FCs as (?&?&?&?&?); repeat split; auto; compute; tauto).
  unfold hbytes. rewrite L1, L2, L3, L4. rewrite !(@data_at_tarray_tuchar_cs HCS W_cookie_reply).
  unfold cksnap_val. cbn [fst snd]. simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.

(* closing the cnode after the snapshot's split (b = the loaded have_sent_mac1) *)
Lemma hcy5_p11_C_cn_close C c nd b X :
  cookie_ok C -> @field_compatible W_cookie_reply t_cnode5 [] c -> ck_sent C = b ->
  (@field_at W_cookie_reply Ews t_cnode5 (DOT HY._n) nd c *
   @field_at W_cookie_reply Ews t_cnode5 (DOT HY._cs DOT HY._have_sent_mac1) (Val.of_bool b) c *
   hbytes Ews (ck_last_mac1 C) (offset_val 26 (offset_val 8 c)) *
   hbytes Ews (ck_dkey C) (offset_val 42 (offset_val 8 c)) *
   hbytes Ews (ck_mkey C) (offset_val 74 (offset_val 8 c)) *
   hcy5_p11_C_snrest C (offset_val 8 c) *
   (hcy5_p11_C_cn1 c nd (Some C) -* X) |-- X)%logic.
Proof.
  intros Hok FC <-.
  eapply derives_trans; [| apply (modus_ponens_wand (hcy5_p11_C_cn1 c nd (Some C)) X)].
  apply sepcon_derives; [| apply derives_refl].
  unfold hcy5_p11_C_cn1, hcy5_cs_rep. rewrite (hcy5_p11_C_snap_split C c Hok FC).
  cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* a node's field p: focus with a wand (copy of hcy5_p10_b_node)           *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p11_C_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
  (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W_cookie_reply _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W_cookie_reply Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hcy5_p11_C_node h NS N v :
  In N NS -> hn_p N = v ->
  hnodes_rep4 W_cookie_reply h NS |--
  @field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) v (hn_addr N) *
  (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) v (hn_addr N) -* hnodes_rep4 W_cookie_reply h NS).
Proof.
  intros Hin <-. revert h. induction NS as [| N0 NS IH]; intros h; [contradiction |].
  destruct Hin as [-> | Hin].
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W_cookie_reply Ews t_hnode4 (hn_addr N) * @malloc_token W_cookie_reply Ews t_peer (hn_p N) *
       hnodes_rep4 W_cookie_reply nx NS *
       (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N))))%logic.
    + sep_apply (hcy5_p11_C_node1 N nx). cancel.
    + apply hcy5_p11_C_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W_cookie_reply Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W_cookie_reply Ews t_peer (hn_p N0) *
       (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W_cookie_reply nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hcy5_p11_C_wand_frame. Exists nx. entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* a peer's cookie: focus with a wand (copy of hcy5_p10_b_peer / _pfc)     *)
(* ---------------------------------------------------------------------- *)

Definition hcy5_p11_C_prest (sh: share) (p: val) (P: peer) : mpred :=
  (!! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p))%logic.

Lemma hcy5_p11_C_peer_split sh a P :
  peer_rep sh a P = (cookie_rep sh (cookie_addr a) (p_cookie P) * hcy5_p11_C_prest sh a P)%logic.
Proof.
  unfold peer_rep, hcy5_p11_C_prest. apply pred_ext; entailer!; cancel.
Qed.

Lemma hcy5_p11_C_wand_eq (X F G: mpred) : X = (F * G)%logic -> X |-- F * (F -* X).
Proof.
  intros E. rewrite E at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm, <- E. apply derives_refl.
Qed.

Lemma hcy5_p11_C_peer PS a sh P :
  In (a, sh, P) PS ->
  peers_rep PS |-- cookie_rep sh (cookie_addr a) (p_cookie P) *
                   (cookie_rep sh (cookie_addr a) (p_cookie P) -* peers_rep PS).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  apply hcy5_p11_C_wand_eq with (G := (hcy5_p11_C_prest sh a P * iter_sepcon peer_item_rep l1 *
                                         iter_sepcon peer_item_rep l2)%logic).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  rewrite hcy5_p11_C_peer_split. apply pred_ext; cancel.
Qed.

Lemma hcy5_p11_C_pfc PS a sh P :
  In (a, sh, P) PS -> peers_rep PS |-- !! (@field_compatible Noise.CS t_peer [] a).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1. entailer!.
Qed.

(* the cookie at the world: the loaded fields, the arrays as byte buffers (copy of hc3b_ck_cookie_split_q
   at W) *)
Lemma hcy5_p11_C_cookie_split sh C lk c : cookie_ok C ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) c =
  (field_at sh hcy5_p11_C_tck (DOT HY._birthdate) (Vlong (ck_birth C)) c *
   field_at sh hcy5_p11_C_tck (DOT HY._is_valid) (Val.of_bool (ck_valid C)) c *
   hbytes sh (ck_cookie C) (field_address hcy5_p11_C_tck (DOT HY._cookie) c) *
   field_at sh hcy5_p11_C_tck (DOT HY._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
   hbytes sh (ck_last_mac1 C) (field_address hcy5_p11_C_tck (DOT HY._last_mac1_sent) c) *
   hbytes sh (ck_dkey C) (field_address hcy5_p11_C_tck (DOT HY._cookie_decryption_key) c) *
   hbytes sh (ck_mkey C) (field_address hcy5_p11_C_tck (DOT HY._message_mac1_key) c) *
   spacer sh 106 108 c * field_at sh hcy5_p11_C_tck (DOT HY._lock) lk c)%logic.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite Noise.CS W_cookie_reply _ sh t_cookie _ _ (JMeq_refl _)) by reflexivity.
  unfold t_cookie. unfold_data_at (data_at _ _ _ c).
  rewrite !(field_at_data_at sh (Tstruct I._cookie noattr) (DOT HY._cookie)).
  rewrite (field_at_data_at sh (Tstruct I._cookie noattr) (DOT HY._last_mac1_sent)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT HY._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT HY._message_mac1_key)).
  unfold hbytes. rewrite L1, L2, L3, L4.
  rewrite !(@data_at_tarray_tuchar_cs HCS W_cookie_reply).
  unfold hcy5_p11_C_tck, cookie_val. cbn [fst snd]. simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

(* the bundle: every lemma above is proved *)
Lemma hcy5_p11_C_all : True.
Proof.
  pose proof hcy5_p11_C_cm_open as X1. pose proof hcy5_p11_C_cn as X2. pose proof hcy5_p11_C_snap_ok as X3.
  pose proof hcy5_p11_C_snap_split as X4. pose proof hcy5_p11_C_node as X5. pose proof hcy5_p11_C_peer as X6.
  pose proof hcy5_p11_C_pfc as X7. pose proof hcy5_p11_C_cookie_split as X8. pose proof hcy5_p11_C_cn_close as X9.
  exact I.
Qed.
