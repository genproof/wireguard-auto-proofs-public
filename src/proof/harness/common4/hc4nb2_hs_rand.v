(* body of hs_randomize (v4 spec, flag raw), closes hc4_body_hs_randomize *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.

Module FR := WgNoise.harness.x_consume_response_any.code.

#[local] Instance hc4nb2_hs_rand_cce : change_composite_env Noise.CS CSknb.
Proof. make_cs_preserve Noise.CS CSknb. Defined.
#[local] Instance hc4nb2_hs_rand_cce' : change_composite_env CSknb Noise.CS.
Proof. make_cs_preserve CSknb Noise.CS. Defined.

#[local] Existing Instance CSknb.

Lemma hc4nb2_hs_rand_map (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs -> map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros F. unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [| exact F].
  intros b Hb. simpl. unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia).
  reflexivity.
Qed.

Local Open Scope logic.

Lemma hc4nb2_hs_rand_eq (sh: share) (h: val) :
  @data_at_ CSknb sh t_hs h =
  field_at_ sh t_hs (DOT I._entry) h * field_at_ sh t_hs (DOT I._state) h * spacer sh 36 40 h *
  field_at_ sh t_hs (DOT I._last_initiation_consumption) h * field_at_ sh t_hs (DOT I._static_identity) h *
  field_at_ sh t_hs (DOT I._ephemeral_private) h * field_at_ sh t_hs (DOT I._remote_static) h *
  field_at_ sh t_hs (DOT I._remote_ephemeral) h * field_at_ sh t_hs (DOT I._precomputed_static_static) h *
  field_at_ sh t_hs (DOT I._preshared_key) h * field_at_ sh t_hs (DOT I._hash) h *
  field_at_ sh t_hs (DOT I._chaining_key) h * field_at_ sh t_hs (DOT I._latest_timestamp) h *
  field_at_ sh t_hs (DOT I._remote_index) h * field_at_ sh t_hs (DOT I._lock) h * spacer sh 300 304 h.
Proof.
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ _).
  unfold field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

Ltac hc4nb2_hs_rand_back sh h f :=
  erewrite (@field_at_change_composite Noise.CS CSknb _ sh t_hs (DOT f)); [| apply JMeq_refl | reflexivity];
  rewrite (field_at_data_at sh t_hs (DOT f)); simpl nested_field_type.

Ltac hc4nb2_hs_rand_call sh h f n b :=
  erewrite (@field_at_change_composite Noise.CS CSknb _ sh t_hs (DOT f)); [| apply JMeq_refl | reflexivity];
  assert_PROP (field_compatible t_hs (DOT f) h) by entailer!;
  rewrite (field_at_data_at sh t_hs (DOT f)); simpl nested_field_type;
  forward_call (field_address t_hs (DOT f) h, n, sh);
  Intros b;
  match goal with Hl: Zlength b = _, Hr: Forall _ b |- _ =>
    let Lb := fresh "Lb" in let Rb := fresh "Rb" in rename Hl into Lb; rename Hr into Rb end.

Ltac hc4nb2_hs_rand_rcall sh h f n b :=
  assert_PROP (field_compatible t_hs (DOT f) h) by entailer!;
  rewrite (field_at__data_at_ sh t_hs (DOT f) h); simpl nested_field_type;
  forward_call (field_address t_hs (DOT f) h, n, sh);
  Intros b;
  match goal with Hl: Zlength b = _, Hr: Forall _ b |- _ =>
    let Lb := fresh "Lb" in let Rb := fresh "Rb" in rename Hl into Lb; rename Hr into Rb end.

Ltac hc4nb2_hs_rand_rback sh h f t v :=
  sep_apply (data_at_data_at_ sh t v (field_address t_hs (DOT f) h));
  let E := fresh "E" in
  assert (E: field_at_ sh t_hs (DOT f) h = data_at_ sh t (field_address t_hs (DOT f) h))
    by (rewrite field_at__data_at_; reflexivity);
  rewrite <- E; clear E.

Lemma hc4nb2_hs_rand_body :
  @semax_body [] hc4nb_G_hs_randomize CSknb WgNoise.harness.x_consume_response_any.code.f_hs_randomize hs_randomize4_spec.
Proof.
  start_function.
  destruct raw.
  - erewrite (@data_at__change_composite Noise.CS CSknb _ shp t_hs) by reflexivity.
    rewrite hc4nb2_hs_rand_eq.
    forward_call tt.
    Intros st.
    unfold field_at_ at 2.
    forward.
    hc4nb2_hs_rand_rcall shp (hs_addr p) I._ephemeral_private 32 b1.
    hc4nb2_hs_rand_rcall shp (hs_addr p) I._remote_ephemeral 32 b2.
    hc4nb2_hs_rand_rcall shp (hs_addr p) I._hash 32 b3.
    hc4nb2_hs_rand_rcall shp (hs_addr p) I._chaining_key 32 b4.
    hc4nb2_hs_rand_rcall shp (hs_addr p) I._latest_timestamp 12 b5.
    forward_call tt.
    Intros ri.
    unfold field_at_ at 7.
    forward.
    forward_call tt.
    Intros lic.
    unfold field_at_ at 2.
    forward.
    Exists st lic (map Byte.repr b1) (map Byte.repr b2) (map Byte.repr b3) (map Byte.repr b4) (map Byte.repr b5)
      (Int.repr ri).
    rewrite !Zlength_map.
    erewrite (@data_at__change_composite Noise.CS CSknb _ shp t_hs) by reflexivity.
    rewrite hc4nb2_hs_rand_eq.
    sep_apply (field_at_field_at_ shp t_hs (DOT I._state) (Vint st) (hs_addr p)).
    sep_apply (field_at_field_at_ shp t_hs (DOT I._last_initiation_consumption) (Vlong lic) (hs_addr p)).
    sep_apply (field_at_field_at_ shp t_hs (DOT I._remote_index) (Vint (Int.repr ri)) (hs_addr p)).
    hc4nb2_hs_rand_rback shp (hs_addr p) I._ephemeral_private (tarray tuchar 32) (map (fun b : Z => Vint (Int.repr b)) b1).
    hc4nb2_hs_rand_rback shp (hs_addr p) I._remote_ephemeral (tarray tuchar 32) (map (fun b : Z => Vint (Int.repr b)) b2).
    hc4nb2_hs_rand_rback shp (hs_addr p) I._hash (tarray tuchar 32) (map (fun b : Z => Vint (Int.repr b)) b3).
    hc4nb2_hs_rand_rback shp (hs_addr p) I._chaining_key (tarray tuchar 32) (map (fun b : Z => Vint (Int.repr b)) b4).
    hc4nb2_hs_rand_rback shp (hs_addr p) I._latest_timestamp (tarray tuchar 12) (map (fun b : Z => Vint (Int.repr b)) b5).
    entailer!.
  - unfold peer_rep, hs_rep. Intros.
    match goal with H: hs_ok _ |- _ => destruct H as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) end.
    freeze FR1 := - (field_at shp t_hs (DOT I._state) _ _) (field_at shp t_hs (DOT I._last_initiation_consumption) _ _)
      (field_at shp t_hs (DOT I._ephemeral_private) _ _) (field_at shp t_hs (DOT I._remote_ephemeral) _ _)
      (field_at shp t_hs (DOT I._hash) _ _) (field_at shp t_hs (DOT I._chaining_key) _ _)
      (field_at shp t_hs (DOT I._latest_timestamp) _ _) (field_at shp t_hs (DOT I._remote_index) _ _).
    forward_call tt.
    Intros st.
    erewrite (@field_at_change_composite Noise.CS CSknb _ shp t_hs (DOT I._state)); [| apply JMeq_refl | reflexivity].
    forward.
    hc4nb2_hs_rand_call shp (hs_addr p) I._ephemeral_private 32 b1.
    hc4nb2_hs_rand_call shp (hs_addr p) I._remote_ephemeral 32 b2.
    hc4nb2_hs_rand_call shp (hs_addr p) I._hash 32 b3.
    hc4nb2_hs_rand_call shp (hs_addr p) I._chaining_key 32 b4.
    hc4nb2_hs_rand_call shp (hs_addr p) I._latest_timestamp 12 b5.
    forward_call tt.
    Intros ri.
    erewrite (@field_at_change_composite Noise.CS CSknb _ shp t_hs (DOT I._remote_index)); [| apply JMeq_refl | reflexivity].
    forward.
    forward_call tt.
    Intros lic.
    erewrite (@field_at_change_composite Noise.CS CSknb _ shp t_hs (DOT I._last_initiation_consumption));
      [| apply JMeq_refl | reflexivity].
    forward.
    rewrite !hc4nb2_hs_rand_map by assumption.
    Exists st lic (map Byte.repr b1) (map Byte.repr b2) (map Byte.repr b3) (map Byte.repr b4) (map Byte.repr b5)
      (Int.repr ri).
    unfold peer_rep, hs_rep. thaw FR1.
    cbn [p_hs p_set_hs hs_randomized hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck
         hs_ts hs_rindex p_device p_dead p_cur p_prev p_next p_lsh p_cookie p_refs p_id p_pknext].
    hc4nb2_hs_rand_back shp (hs_addr p) I._ephemeral_private.
    hc4nb2_hs_rand_back shp (hs_addr p) I._remote_ephemeral.
    hc4nb2_hs_rand_back shp (hs_addr p) I._hash.
    hc4nb2_hs_rand_back shp (hs_addr p) I._chaining_key.
    hc4nb2_hs_rand_back shp (hs_addr p) I._latest_timestamp.
    erewrite (@field_at_change_composite Noise.CS CSknb _ shp t_hs (DOT I._state)); [| apply JMeq_refl | reflexivity].
    erewrite (@field_at_change_composite Noise.CS CSknb _ shp t_hs (DOT I._remote_index)); [| apply JMeq_refl | reflexivity].
    erewrite (@field_at_change_composite Noise.CS CSknb _ shp t_hs (DOT I._last_initiation_consumption));
      [| apply JMeq_refl | reflexivity].
    rewrite !Zlength_map.
    entailer!.
    unfold hs_ok, hs_randomized; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
    rewrite !Zlength_map. repeat split; assumption.
Qed.
