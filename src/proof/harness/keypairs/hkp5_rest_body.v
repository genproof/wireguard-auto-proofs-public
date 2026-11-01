(* law keypairs: the body of rest_same.  The statement is
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_rest.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

#[local] Instance hkp5_rb_i1 : change_composite_env Noise.CS W_keypairs. make_cs_preserve Noise.CS W_keypairs. Defined.
#[local] Instance hkp5_rb_i2 : change_composite_env W_keypairs CKS. make_cs_preserve W_keypairs CKS. Defined.

Definition hkp5_rb_tp := Tstruct KC._wg_peer noattr.
Definition hkp5_rb_ts := Tstruct KC._pr_snap noattr.

Lemma hkp5_rb_pres : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_rb_i1) t_peer = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hkp5_rb_pres_ck : cs_preserve_type W_keypairs CKS (@coeq _ _ hkp5_rb_i2) (Tstruct KC._ck_snap noattr) = true.
Proof. vm_compute. reflexivity. Qed.

(* the fields of the peer that rest_same reads, at W_keypairs *)
Lemma hkp5_rb_f_device sh (v: val) p :
  @field_at Noise.CS sh t_peer [StructField I._device] v p = @field_at W_keypairs sh hkp5_rb_tp [StructField I._device] v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite _ _ hkp5_rb_i1 sh t_peer [StructField I._device] v v (JMeq_refl _) hkp5_rb_pres)).
Qed.

Lemma hkp5_rb_f_is_dead sh (v: val) p :
  @field_at Noise.CS sh t_peer [StructField I._is_dead] v p = @field_at W_keypairs sh hkp5_rb_tp [StructField I._is_dead] v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite _ _ hkp5_rb_i1 sh t_peer [StructField I._is_dead] v v (JMeq_refl _) hkp5_rb_pres)).
Qed.

Lemma hkp5_rb_f_last_sent_handshake sh (v: val) p :
  @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] v p = @field_at W_keypairs sh hkp5_rb_tp [StructField I._last_sent_handshake] v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite _ _ hkp5_rb_i1 sh t_peer [StructField I._last_sent_handshake] v v (JMeq_refl _) hkp5_rb_pres)).
Qed.

Lemma hkp5_rb_f_internal_id sh (v: val) p :
  @field_at Noise.CS sh t_peer [StructField I._internal_id] v p = @field_at W_keypairs sh hkp5_rb_tp [StructField I._internal_id] v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite _ _ hkp5_rb_i1 sh t_peer [StructField I._internal_id] v v (JMeq_refl _) hkp5_rb_pres)).
Qed.

Lemma hkp5_rb_f_pubkey_next sh (v: val) p :
  @field_at Noise.CS sh t_peer [StructField I._pubkey_next] v p = @field_at W_keypairs sh hkp5_rb_tp [StructField I._pubkey_next] v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite _ _ hkp5_rb_i1 sh t_peer [StructField I._pubkey_next] v v (JMeq_refl _) hkp5_rb_pres)).
Qed.

Definition hkp5_rb_prest (sh: share) (p: val) (P: peer) : mpred :=
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) * hs_rep sh (hs_addr p) (p_hs P) *
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma hkp5_rb_peer_eq sh p P :
  peer_rep sh p P =
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at W_keypairs sh hkp5_rb_tp [StructField I._device] (p_device P) p *
   @field_at W_keypairs sh hkp5_rb_tp [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   @field_at W_keypairs sh hkp5_rb_tp [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at W_keypairs sh hkp5_rb_tp [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at W_keypairs sh hkp5_rb_tp [StructField I._pubkey_next] (p_pknext P) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) * hkp5_rb_prest sh p P).
Proof.
  unfold peer_rep, hkp5_rb_prest.
  rewrite <- hkp5_rb_f_device, <- hkp5_rb_f_is_dead, <- hkp5_rb_f_last_sent_handshake, <- hkp5_rb_f_internal_id,
    <- hkp5_rb_f_pubkey_next.
  apply pred_ext; entailer!; cancel.
Qed.

Definition hkp5_rb_srest (sh: share) (s: val) : mpred :=
  field_at sh hkp5_rb_ts (DOT KC._current_keypair) nullval s *
  field_at sh hkp5_rb_ts (DOT KC._previous_keypair) nullval s *
  field_at sh hkp5_rb_ts (DOT KC._next_keypair) nullval s * spacer sh 9 16 s.

Lemma hkp5_rb_snap_eq sh P s :
  data_at sh hkp5_rb_ts (hk5_prsnap_val P) s =
  field_at sh hkp5_rb_ts (DOT KC._device) (p_device P) s *
  field_at sh hkp5_rb_ts (DOT KC._is_dead) (Val.of_bool (p_dead P)) s *
  field_at sh hkp5_rb_ts (DOT KC._last_sent_handshake) (Vlong (p_lsh P)) s *
  field_at sh hkp5_rb_ts (DOT KC._internal_id) (Vlong (p_id P)) s *
  field_at sh hkp5_rb_ts (DOT KC._pubkey_next) (p_pknext P) s *
  field_at sh hkp5_rb_ts (DOT KC._cookie) (hk5_ck_val (p_cookie P)) s *
  hkp5_rb_srest sh s.
Proof.
  unfold hkp5_rb_ts, hkp5_rb_srest. unfold_data_at (data_at _ _ _ s).
  unfold hk5_prsnap_val. cbn [fst snd].
  apply pred_ext; cancel.
Qed.

Lemma hkp5_rb_vp_dev sh wg D R :
  readable_share sh -> device_rep sh wg D * R |-- valid_pointer wg.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold device_rep. Intros.
  do 4 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hkp5_rb_ck_eq sh C s :
  field_at sh hkp5_rb_ts (DOT KC._cookie) (hk5_ck_val C) s =
  @data_at CKS sh t_cksnap (cksnap_val C) (field_address hkp5_rb_ts (DOT KC._cookie) s).
Proof.
  rewrite field_at_data_at.
  exact (f_equal (fun f => f (field_address hkp5_rb_ts (DOT KC._cookie) s))
    (@data_at_change_composite W_keypairs CKS hkp5_rb_i2 sh (Tstruct KC._ck_snap noattr) (hk5_ck_val C) (cksnap_val C)
       (JMeq_refl _) hkp5_rb_pres_ck)).
Qed.

Lemma hkp5_rb_eqb_refl C : cookie_eqb C C = true.
Proof.
  destruct C as [b v c sn l d m]. unfold cookie_eqb, bytes_eqb. simpl. rewrite Int64.eq_true.
  rewrite !if_true by reflexivity. destruct v, sn; reflexivity.
Qed.

Lemma hkp5_rest_body :
  @semax_body hkp5_V hk5_G_rest_same W_keypairs KC.f_rest_same hk5_rest_same_spec.
Proof.
  start_function.
  fold hkp5_rb_ts. rewrite hkp5_rb_snap_eq, hkp5_rb_peer_eq. Intros. subst wg. rewrite H0.
  assert_PROP (isptr (p_device P)) as Pwg.
  { unfold device_rep. Intros. apply prop_right. match goal with Hc: field_compatible _ _ _ |- _ => destruct Hc; auto end. }
  forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp KC._t'1 (Vint Int.one) :: Q) (SEPx S))) end.
  { apply denote_tc_test_eq_split; apply sepcon_valid_pointer2; rewrite <- (sepcon_emp (device_rep _ _ _));
      apply hkp5_rb_vp_dev; auto. }
  { clear H.
    forward; [entailer!; destruct (p_dead P); simpl; auto |].
    forward.
    forward. entailer!. destruct (p_dead P); reflexivity. }
  { exfalso. auto. }
  forward_if (temp KC._t'2 (Vint Int.one)).
  { forward. forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  assert_PROP (field_compatible hkp5_rb_ts (DOT KC._cookie) s /\ field_compatible hkp5_rb_tp (DOT KC._latest_cookie) p)
    as FCsp.
  { entailer!. match goal with Hc: field_compatible hkp5_rb_tp (DOT I._device) p |- _ =>
      destruct Hc as (A1 & A2 & A3 & A4 & A5 & _) end.
    repeat split; auto. vm_compute. do 5 right. left. reflexivity. }
  destruct FCsp as [FCs FCp].
  rewrite hkp5_rb_ck_eq.
  forward_if (temp KC._t'3 (Vint Int.one)).
  { forward_call (shs, field_address hkp5_rb_ts (DOT KC._cookie) s, p_cookie P, shp, cookie_addr p, p_cookie P).
    rewrite hkp5_rb_eqb_refl. forward. entailer!. }
  { exfalso. apply Int.one_not_zero. assumption. }
  forward_if (temp KC._t'5 (Vint Int.one)).
  { forward. forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  forward_if (temp KC._t'6 (Vint Int.one)).
  { forward. forward. forward. entailer!. }
  { exfalso. apply Int.one_not_zero. assumption. }
  forward.
  fold hkp5_rb_ts. rewrite hkp5_rb_snap_eq, hkp5_rb_peer_eq, <- hkp5_rb_ck_eq, H0. entailer!.
Qed.
