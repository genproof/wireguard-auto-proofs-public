(* (group snap of common4) child part: replay_counter_fresh, peer_randomize_rest,
   draw_peer_refs, le32_load. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.

#[local] Existing Instance CSk.
Module R3 := WgNoise.proof.protocol.prot_repr3.

(* byte arrays are the same in every compspecs (copy of hc3_body_ck.v's hc3b_ck_data_at_cs) *)
Lemma hc4bm_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.
Lemma hc4bm_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. intros. unfold data_at_, field_at_. apply hc4bm_data_at_cs. Qed.

(* copies of aead_donna3_msg.v's adb3_lor_add / adb3_le32_of_unsigned *)
Lemma hc4bm_lor_add (a b k: Z) :
  0 <= k -> 0 <= a < 2 ^ k -> 0 <= b -> Z.lor a (b * 2 ^ k) = a + b * 2 ^ k.
Proof.
  intros Hk Ha Hb.
  assert (Hl: Z.land a (b * 2 ^ k) = 0).
  { apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - replace a with (a mod 2 ^ k) by (apply Z.mod_small; lia).
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact Hl. rewrite Z.add_nocarry_lxor by exact Hl. reflexivity.
Qed.

Lemma hc4bm_le32_or (b0 b1 b2 b3: byte) :
  Int.or (Int.or (Int.or (Int.repr (Byte.unsigned b0))
                         (Int.shl (Int.repr (Byte.unsigned b1)) (Int.repr 8)))
                 (Int.shl (Int.repr (Byte.unsigned b2)) (Int.repr 16)))
         (Int.shl (Int.repr (Byte.unsigned b3)) (Int.repr 24)) =
  Int.repr (Byte.unsigned b0 + Byte.unsigned b1 * 2 ^ 8 + Byte.unsigned b2 * 2 ^ 16 + Byte.unsigned b3 * 2 ^ 24).
Proof.
  pose proof (Byte.unsigned_range b0) as R0. pose proof (Byte.unsigned_range b1) as R1.
  pose proof (Byte.unsigned_range b2) as R2. pose proof (Byte.unsigned_range b3) as R3.
  change Byte.modulus with 256 in *.
  unfold Int.or, Int.shl.
  rewrite !(Int.unsigned_repr 8), !(Int.unsigned_repr 16), !(Int.unsigned_repr 24) by rep_lia.
  rewrite !(Int.unsigned_repr (Byte.unsigned _)) by rep_lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (Int.unsigned_repr (_ * 2 ^ 8)) by rep_lia.
  rewrite hc4bm_lor_add by rep_lia.
  rewrite (Int.unsigned_repr (_ + _)) by rep_lia.
  rewrite (Int.unsigned_repr (_ * 2 ^ 16)) by rep_lia.
  rewrite hc4bm_lor_add by rep_lia.
  rewrite (Int.unsigned_repr (_ + _)) by rep_lia.
  rewrite (Int.unsigned_repr (_ * 2 ^ 24)) by rep_lia.
  rewrite hc4bm_lor_add by rep_lia.
  reflexivity.
Qed.

Lemma hc4bm_le32 :
  @semax_body [] hc4_G_none CSk WgNoise.harness.x_handshake_receive.code.f_le32_load le32_load4_spec.
Proof.
  start_function.
  unfold hbytes, WgNoise.proof.protocol.prot_repr3.bytes in *. Intros.
  rewrite (hc4bm_data_at_cs (cs1:=HCS) (cs2:=CSk)).
  do 4 (forward; [rewrite !Znth_map by list_solve; entailer!; rep_lia|]).
  rewrite !Znth_map by list_solve.
  forward.
  entailer!.
  - unfold le32_val, Vubyte. simpl. f_equal. apply hc4bm_le32_or.
  - rewrite (hc4bm_data_at_cs (cs1:=HCS) (cs2:=CSk)). auto.
Qed.

Lemma hc4bm_refs :
  @semax_body [] hc4_G_draw_peer_refs CSk WgNoise.harness.x_cookie_mac.code.f_draw_peer_refs draw_peer_refs4_spec.
Proof.
  start_function.
  forward_call tt. Intros b.
  apply (semax_switch_PQR (b mod 4)); [reflexivity | entailer! | entailer! | ].
  { destruct H1 as [_ E]; discriminate. }
  { f_equal. unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 4); rep_lia).
  assert (b mod 4 = 0 \/ b mod 4 = 1 \/ b mod 4 = 2 \/ b mod 4 = 3) as [E|[E|[E|E]]]
    by (pose proof (Z.mod_pos_bound b 4); lia);
    rewrite E; match goal with |- semax _ _ ?c _ => let c' := eval simpl in c in change c with c' end.
  - forward_call tt. Intros n. forward.
    Exists (Int.add (Int.repr 1) (Int.modu (Int.repr n) (Int.repr 2147483646))). entailer!.
    pose proof (Z.mod_pos_bound n 2147483646). rewrite Int.unsigned_repr by rep_lia. lia.
  - forward. Exists (Int.repr 2147483646). entailer!.
  - forward_call tt. Intros c.
    assert (0 <= Z.land c 1 <= 1)
      by (pose proof (Z.land_ones c 1 ltac:(lia)) as LO; change (Z.ones 1) with 1 in LO; change (2 ^ 1) with 2 in LO; rewrite LO; pose proof (Z.mod_pos_bound c 2); lia).
    forward.
    Exists (Int.repr (1 + Z.land c 1)). entailer!. try (rewrite Int.unsigned_repr by rep_lia). lia.
  - forward_call tt. Intros c.
    assert (0 <= Z.land c 1 <= 1)
      by (pose proof (Z.land_ones c 1 ltac:(lia)) as LO; change (Z.ones 1) with 1 in LO; change (2 ^ 1) with 2 in LO; rewrite LO; pose proof (Z.mod_pos_bound c 2); lia).
    forward.
    Exists (Int.repr (1 + Z.land c 1)). entailer!. try (rewrite Int.unsigned_repr by rep_lia). lia.
Qed.

#[local] Instance hc4bm_cce1 : change_composite_env Noise.CS CSk.
Proof. make_cs_preserve Noise.CS CSk. Defined.
#[local] Instance hc4bm_cce2 : change_composite_env CSk Noise.CS.
Proof. make_cs_preserve CSk Noise.CS. Defined.

Lemma hc4bm_rcf :
  @semax_body [] hc4_G_none CSk WgNoise.harness.x_keypairs.code.f_replay_counter_fresh replay_counter_fresh4_spec.
Proof.
  start_function.
  erewrite (@data_at_change_composite Noise.CS CSk _ sh t_rcounter); [| apply JMeq_refl | reflexivity].
  forward.
  forward_if (PROP (rc = Int64.zero) LOCAL (temp WgNoise.harness.x_keypairs.code._c c)
              SEP (data_at sh t_rcounter (Vlong rc, (lk, map Vlong bt)) c)).
  { forward.
    rewrite (data_at_change_composite (cs_from:=CSk) (cs_to:=Noise.CS) sh t_rcounter _ (Vlong rc, (lk, map Vlong bt)));
      [| apply JMeq_refl | reflexivity].
    entailer!. unfold rc_fresh. destruct (Int64.eq rc Int64.zero) eqn:Q; [|reflexivity].
    apply Int64.same_if_eq in Q. subst. contradiction. }
  { forward. entailer!. }
  Intros. subst rc.
  forward_for_simple_bound 128 (EX i: Z, PROP (forallb (fun x => Int64.eq x Int64.zero) (sublist 0 i bt) = true)
    LOCAL (temp WgNoise.harness.x_keypairs.code._c c)
    SEP (data_at sh t_rcounter (Vlong Int64.zero, (lk, map Vlong bt)) c))%assert.
  { entailer!. }
  { cbv beta. Intros. forward.
    forward_if (PROP (Znth i bt = Int64.zero)
                LOCAL (temp WgNoise.harness.x_keypairs.code._i (Vlong (Int64.repr i)); temp WgNoise.harness.x_keypairs.code._c c)
                SEP (data_at sh t_rcounter (Vlong Int64.zero, (lk, map Vlong bt)) c)).
    { forward.
      rewrite (data_at_change_composite (cs_from:=CSk) (cs_to:=Noise.CS) sh t_rcounter _
                 (Vlong Int64.zero, (lk, map Vlong bt))); [| apply JMeq_refl | reflexivity].
      entailer!. unfold rc_fresh. destruct (forallb _ bt) eqn:Q; [|reflexivity].
      exfalso. rewrite forallb_forall in Q. specialize (Q (Znth i bt) ltac:(apply Znth_In; lia)).
      apply Int64.same_if_eq in Q. contradiction. }
    { forward. entailer!. }
    entailer!. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite (sublist_one i (i + 1)) by lia.
    rewrite forallb_app, H1. simpl. rewrite H2. reflexivity. }
  forward.
  rewrite (data_at_change_composite (cs_from:=CSk) (cs_to:=Noise.CS) sh t_rcounter _
             (Vlong Int64.zero, (lk, map Vlong bt))); [| apply JMeq_refl | reflexivity].
  entailer!. rewrite sublist_same in H0 by lia. unfold rc_fresh. rewrite H0. reflexivity.
Qed.

Lemma hc4bm_ofbool (x: int) :
  Val.of_bool (negb (Int.eq x Int.zero)) = Vint (if Int.eq x Int.zero then Int.zero else Int.one).
Proof. destruct (Int.eq x Int.zero); reflexivity. Qed.

Lemma hc4bm_prr :
  @semax_body [] hc4_G_peer_randomize_rest CSk WgNoise.harness.x_consume_initiation_any.code.f_peer_randomize_rest peer_randomize_rest4_spec.
Proof.
  start_function.
  unfold R3.peer_rep, R3.cookie_rep. Intros lk.
  match goal with H: R3.cookie_ok _ |- _ => destruct H as (L1 & L2 & L3 & L4) end.
  erewrite (@data_at_change_composite Noise.CS CSk _ shp R3.t_cookie); [| apply JMeq_refl | reflexivity].
  erewrite (@field_at_change_composite Noise.CS CSk _ shp R3.t_peer (DOT R3.I._is_dead)); [| apply JMeq_refl | reflexivity].
  erewrite (@field_at_change_composite Noise.CS CSk _ shp R3.t_peer (DOT R3.I._last_sent_handshake)); [| apply JMeq_refl | reflexivity].
  assert (FCk: @field_compatible CSk R3.t_peer [] p)
    by (apply (@field_compatible_change_composite Noise.CS CSk _ R3.t_peer); [reflexivity | assumption]).
  assert (CA: R3.cookie_addr p = field_address R3.t_peer (DOT R3.I._latest_cookie) p)
    by (unfold R3.cookie_addr; rewrite field_address_offset by auto with field_compatible; reflexivity).
  rewrite CA. change R3.t_cookie with (nested_field_type R3.t_peer (DOT R3.I._latest_cookie)).
  rewrite <- (field_at_data_at shp R3.t_peer (DOT R3.I._latest_cookie)).
  unfold_field_at (field_at _ _ (DOT R3.I._latest_cookie) _ p).
  unfold R3.cookie_val. cbn [fst snd].
  forward_call tt. Intros b1. forward.
  forward_call tt. Intros lsh. forward.
  forward_call tt. Intros b2. forward.
  forward_call tt. Intros birth. forward.
  rewrite (field_at_data_at shp R3.t_peer (DOT R3.I._latest_cookie DOT R3.I._cookie)).
  forward_call (field_address R3.t_peer (DOT R3.I._latest_cookie DOT R3.I._cookie) p, 16, shp).
  Intros ck.
  forward_call tt. Intros b3. forward.
  rewrite (field_at_data_at shp R3.t_peer (DOT R3.I._latest_cookie DOT R3.I._last_mac1_sent)).
  forward_call (field_address R3.t_peer (DOT R3.I._latest_cookie DOT R3.I._last_mac1_sent) p, 16, shp).
  Intros m1.
  Exists (negb (Int.eq (Int.and (Int.repr b1) (Int.repr 1)) Int.zero)) lsh
    (negb (Int.eq (Int.and (Int.repr b2) (Int.repr 1)) Int.zero)) birth (map Byte.repr ck)
    (negb (Int.eq (Int.and (Int.repr b3) (Int.repr 1)) Int.zero)) (map Byte.repr m1).
  unfold R3.peer_rep, R3.cookie_rep, p_rest_randomized.
  cbn [prot_model3.p_device prot_model3.p_dead prot_model3.p_cur prot_model3.p_prev
       prot_model3.p_next prot_model3.p_hs prot_model3.p_lsh prot_model3.p_cookie prot_model3.p_refs
       prot_model3.p_id prot_model3.p_pknext prot_model3.ck_birth prot_model3.ck_valid prot_model3.ck_cookie
       prot_model3.ck_sent prot_model3.ck_last_mac1 prot_model3.ck_dkey prot_model3.ck_mkey].
  entailer!.
  { unfold R3.cookie_ok; cbn [prot_model3.ck_cookie prot_model3.ck_last_mac1 prot_model3.ck_dkey prot_model3.ck_mkey].
    rewrite !Zlength_map. auto. }
  Exists lk.
  erewrite (@field_at_change_composite Noise.CS CSk _ shp R3.t_peer (DOT R3.I._is_dead)); [| apply JMeq_refl | reflexivity].
  erewrite (@data_at_change_composite Noise.CS CSk _ shp R3.t_cookie); [| apply JMeq_refl | reflexivity].
  rewrite CA. change R3.t_cookie with (nested_field_type R3.t_peer (DOT R3.I._latest_cookie)).
  rewrite <- (field_at_data_at shp R3.t_peer (DOT R3.I._latest_cookie)).
  unfold_field_at (field_at _ _ (DOT R3.I._latest_cookie) _ p).
  unfold R3.cookie_val. cbn [fst snd prot_model3.ck_birth prot_model3.ck_valid prot_model3.ck_cookie
       prot_model3.ck_sent prot_model3.ck_last_mac1 prot_model3.ck_dkey prot_model3.ck_mkey].
  rewrite (field_at_data_at shp R3.t_peer (DOT R3.I._latest_cookie DOT R3.I._cookie)).
  rewrite (field_at_data_at shp R3.t_peer (DOT R3.I._latest_cookie DOT R3.I._last_mac1_sent)).
  unfold R3.bytes. rewrite !map_map.
  replace (map (fun x => Vubyte (Byte.repr x)) ck) with (map (fun b => Vint (Int.repr b)) ck).
  2: { apply map_ext_Forall. eapply Forall_impl; [| exact H4]. intros b Hb. unfold Vubyte.
       rewrite Byte.unsigned_repr by rep_lia. reflexivity. }
  replace (map (fun x => Vubyte (Byte.repr x)) m1) with (map (fun b => Vint (Int.repr b)) m1).
  2: { apply map_ext_Forall. eapply Forall_impl; [| exact H7]. intros b Hb. unfold Vubyte.
       rewrite Byte.unsigned_repr by rep_lia. reflexivity. }
  rewrite !hc4bm_ofbool.
  cancel.
Qed.

Theorem hc4b_snap_misc_ok :
  (@semax_body [] hc4_G_none CSk WgNoise.harness.x_keypairs.code.f_replay_counter_fresh replay_counter_fresh4_spec) /\
  (@semax_body [] hc4_G_peer_randomize_rest CSk WgNoise.harness.x_consume_initiation_any.code.f_peer_randomize_rest peer_randomize_rest4_spec) /\
  (@semax_body [] hc4_G_draw_peer_refs CSk WgNoise.harness.x_cookie_mac.code.f_draw_peer_refs draw_peer_refs4_spec) /\
  (@semax_body [] hc4_G_none CSk WgNoise.harness.x_handshake_receive.code.f_le32_load le32_load4_spec).
Proof.
  exact (conj hc4bm_rcf (conj hc4bm_prr (conj hc4bm_refs hc4bm_le32))).
Qed.
