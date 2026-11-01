(* law handshake_receive, B3 K3 segment P part P2: helpers of
   hrx5_B3_K3_P_2.v: the node's field p (focus with a wand, port of K0 I2's hrx5_k0i2_node), the peers split at p and
   rejoined over supd, the peer's cookie at the world (have_sent_mac1, last_mac1_sent at 386, cookie_decryption_key at
   402 apart; port of cookie_reply's hcy5_p9_BA2b_lemmas), the cookie message's fields at the world (port of
   hrx5_B4_C_D_cm_open), byte arrays across compspecs. *)
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
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Module HRM := WgNoise.harness.x_handshake_receive.code.
Notation W := W_handshake_receive.

#[local] Instance hrx5_k3p2_cceK : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.
#[local] Instance hrx5_k3p2_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_k3p2_cceC : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.

(* ---- byte arrays across compspecs ---- *)
Lemma hrx5_k3p2_align_tuchar_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuchar n) z -> align_compatible_rec ce2 (tarray tuchar n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma hrx5_k3p2_fc_tuchar_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (hrx5_k3p2_align_tuchar_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (hrx5_k3p2_align_tuchar_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma hrx5_k3p2_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply hrx5_k3p2_fc_tuchar_cs.
Qed.

Lemma hrx5_k3p2_zero_page gv : @zero_page Noise.CS gv = @zero_page W gv.
Proof. unfold zero_page. apply hrx5_k3p2_tuchar_cs. Qed.

Lemma hrx5_k3p2_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  @data_at W sh (tarray tuchar n) (bytes (map Byte.repr bs)) p.
Proof.
  intros <- HB. f_equal.
  unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [|exact HB]. intros b Hb.
  unfold Vubyte. rewrite Byte.unsigned_repr by exact Hb. reflexivity.
Qed.

(* ---- the field p of a node: focus with a wand ---- *)
Lemma hrx5_k3p2_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Section WN.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_k3p2_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hrx5_k3p2_node h NS N v :
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
    + sep_apply (hrx5_k3p2_node1 N nx). cancel.
    + apply hrx5_k3p2_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hrx5_k3p2_wand_frame. Exists nx. entailer!.
Qed.
End WN.

(* ---- the peers: split at p, rejoin over supd ---- *)
Lemma hrx5_k3p2_split {A: Type} (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] y] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hrx5_k3p2_supd {A: Type} (D: list (val * share * A)) a sh E E' (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f (supd D a E') = f (a, sh, E') * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] y] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  simpl. rewrite (IH H). rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hrx5_k3p2_sfind_supd {A: Type} (D: list (val * share * A)) a sh E E' :
  sfind D a = Some (sh, E) -> sfind (supd D a E') a = Some (sh, E').
Proof.
  induction D as [|[[x shx] y] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a).
  - inv H. simpl. destruct (EqDec_val a a); [reflexivity | contradiction].
  - simpl. destruct (EqDec_val x a); [contradiction|]. auto.
Qed.

(* ---- a peer without its cookie (Noise.CS) ---- *)
Section NoiseCS.
#[local] Existing Instance Noise.CS.
Definition hrx5_k3p2_prest (sh: share) (p: val) (P: peer) : mpred :=
  (!! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p))%logic.

Lemma hrx5_k3p2_peer_split sh p P :
  peer_rep sh p P = (hrx5_k3p2_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P))%logic.
Proof.
  unfold peer_rep, hrx5_k3p2_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Lemma hrx5_k3p2_peer_fold sh p P C :
  (hrx5_k3p2_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic |-- peer_rep sh p (p_set_cookie P C).
Proof.
  unfold peer_rep, hrx5_k3p2_prest, p_set_cookie.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  Intros. entailer!.
Qed.
End NoiseCS.

(* ---- the cookie at the world ---- *)
Section W.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_k3p2_test sh p v :
  field_compatible t_peer [] p ->
  data_at sh t_cookie v (cookie_addr p) = field_at sh t_peer (DOT HRM._latest_cookie) v p.
Proof.
  intros Hfc.
  rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Definition hrx5_k3p2_ckrest (sh: share) (p: val) (C: cookie) (lk: val) : mpred :=
  (field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._birthdate) (Vlong (ck_birth C)) p *
   field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._is_valid) (Val.of_bool (ck_valid C)) p *
   field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._cookie) (bytes (ck_cookie C)) p *
   field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._message_mac1_key) (bytes (ck_mkey C)) p *
   spacer sh 466 468 p *
   field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._lock) lk p)%logic.

Lemma hrx5_k3p2_ck_open sh p C lk :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) (cookie_addr p) =
  (field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
   data_at sh (tarray tuchar 16) (bytes (ck_last_mac1 C)) (offset_val 386 p) *
   data_at sh (tarray tuchar 32) (bytes (ck_dkey C)) (offset_val 402 p) *
   hrx5_k3p2_ckrest sh p C lk)%logic.
Proof.
  intros Hfc0.
  assert (Hfc: field_compatible t_peer [] p).
  { revert Hfc0. apply field_compatible_change_composite. reflexivity. }
  rewrite (@data_at_change_composite Noise.CS W _ sh t_cookie (cookie_val C lk) (cookie_val C lk)
             (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite hrx5_k3p2_test by auto.
  unfold_field_at 1%nat.
  rewrite (field_at_data_at sh t_peer (DOT HRM._latest_cookie DOT HRM._last_mac1_sent)).
  rewrite (field_at_data_at sh t_peer (DOT HRM._latest_cookie DOT HRM._cookie_decryption_key)).
  rewrite !field_address_offset by auto with field_compatible.
  unfold hrx5_k3p2_ckrest. simpl. apply pred_ext; cancel.
Qed.

(* the peer at the world: everything but have_sent_mac1, last_mac1_sent, cookie_decryption_key *)
Definition hrx5_k3p2_rest (sh: share) (p: val) (P: peer) (lk: val) : mpred :=
  (hrx5_k3p2_prest sh p P * hrx5_k3p2_ckrest sh p (p_cookie P) lk)%logic.

Lemma hrx5_k3p2_peer_open sh p P :
  peer_rep sh p P |--
  EX lk: val, (!! cookie_ok (p_cookie P) &&
  (field_at_ sh t_peer (DOT HRM._latest_cookie DOT HRM._have_sent_mac1) p *
   data_at sh (tarray tuchar 16) (bytes (ck_last_mac1 (p_cookie P))) (offset_val 386 p) *
   data_at sh (tarray tuchar 32) (bytes (ck_dkey (p_cookie P))) (offset_val 402 p) *
   hrx5_k3p2_rest sh p P lk))%logic.
Proof.
  rewrite hrx5_k3p2_peer_split.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfc.
  { unfold hrx5_k3p2_prest. entailer!. }
  unfold cookie_rep. Intros lk. Exists lk.
  rewrite (hrx5_k3p2_ck_open sh p (p_cookie P) lk Hfc).
  unfold hrx5_k3p2_rest.
  sep_apply (field_at_field_at_ sh t_peer (DOT HRM._latest_cookie DOT HRM._have_sent_mac1)).
  entailer!.
Qed.

Lemma hrx5_k3p2_peer_close sh p P lk :
  cookie_ok (p_cookie P) ->
  (field_at sh t_peer (DOT HRM._latest_cookie DOT HRM._have_sent_mac1) (Vint Int.one) p *
   data_at sh (tarray tuchar 16) (bytes (ck_last_mac1 (p_cookie P))) (offset_val 386 p) *
   data_at sh (tarray tuchar 32) (bytes (ck_dkey (p_cookie P))) (offset_val 402 p) *
   hrx5_k3p2_rest sh p P lk)%logic
  |-- peer_rep sh p (p_set_cookie P (mkCookie (ck_birth (p_cookie P)) (ck_valid (p_cookie P)) (ck_cookie (p_cookie P))
                       true (ck_last_mac1 (p_cookie P)) (ck_dkey (p_cookie P)) (ck_mkey (p_cookie P)))).
Proof.
  intros Hok.
  unfold hrx5_k3p2_rest.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfc.
  { unfold hrx5_k3p2_prest. entailer!. }
  eapply derives_trans; [| apply hrx5_k3p2_peer_fold].
  unfold cookie_rep.
  set (C' := mkCookie _ _ _ _ _ _ _).
  assert (Hok': cookie_ok C') by exact Hok.
  apply derives_trans with (hrx5_k3p2_prest sh p P *
    (!! cookie_ok C' && @data_at Noise.CS sh t_cookie (cookie_val C' lk) (cookie_addr p)))%logic.
  2: { apply sepcon_derives; [apply derives_refl |].
       apply andp_derives; [apply derives_refl |]. apply (exp_right lk). apply derives_refl. }
  rewrite (hrx5_k3p2_ck_open sh p C' lk Hfc).
  subst C'. unfold hrx5_k3p2_ckrest.
  cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey].
  change (Val.of_bool true) with (Vint Int.one).
  entailer!.
Qed.

(* ---- the cookie message at the world (port of hrx5_B4_C_D_cm_open) ---- *)
Definition hrx5_k3p2_cm (sh: share) (rp: val) (CM: cookie_msg) : mpred :=
  (@field_at W sh t_cmsg (DOT HRM._header DOT HRM._type) (Vint (cm_type CM)) rp *
   @field_at W sh t_cmsg (DOT HRM._receiver_index) (Vint (cm_receiver CM)) rp *
   @data_at W sh (tarray tuchar 24) (bytes (cm_nonce CM)) (offset_val 8 rp) *
   @data_at W sh (tarray tuchar 32) (bytes (cm_enc CM)) (offset_val 32 rp))%logic.

Lemma hrx5_k3p2_cm_open sh rp CM :
  cmsg_rep sh rp CM = (!! (cm_ok CM /\ @field_compatible W t_cmsg [] rp) && hrx5_k3p2_cm sh rp CM)%logic.
Proof.
  unfold cmsg_rep, hrx5_k3p2_cm, cmsg_val.
  erewrite (@data_at_change_composite Cookie.CS W _ sh t_cmsg _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  apply pred_ext.
  - Intros. pose proof H as (L1 & L2).
    assert_PROP (@field_compatible W t_cmsg [] rp) as FC by entailer!.
    unfold_data_at (@data_at W _ t_cmsg _ rp).
    rewrite (@field_at_data_at W sh t_cmsg (DOT HRM._nonce)), (@field_at_data_at W sh t_cmsg (DOT HRM._encrypted_cookie)).
    rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 1%nat.
    entailer!.
  - Intros. pose proof H as (L1 & L2).
    unfold_data_at (@data_at W _ t_cmsg _ rp).
    rewrite (@field_at_data_at W sh t_cmsg (DOT HRM._nonce)), (@field_at_data_at W sh t_cmsg (DOT HRM._encrypted_cookie)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 3%nat.
    entailer!.
Qed.

Lemma hrx5_k3p2_cm_fold sh rp CM : cm_ok CM -> @field_compatible W t_cmsg [] rp ->
  hrx5_k3p2_cm sh rp CM |-- cmsg_rep sh rp CM.
Proof. intros Hok FC. rewrite hrx5_k3p2_cm_open. entailer!. Qed.

End W.
