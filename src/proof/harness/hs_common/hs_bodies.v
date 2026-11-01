(* The bodies of the helpers of hs_laws.h and hs_unchanged.h (hs_specs.v), proved once on the copies of the
   harness hs_reject_initiation in the compspecs CSh, each with the context of its callees only
   (hs_lift.v: hs_helpers_ok, contexts Ghs_<f>): every hs_ program has a helper's callees whenever it has the
   helper, so hs_lift.hs_helper_entry moves each body into the piece of each law that uses it. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require WgNoise.contracts.hs_reject_initiation.

(* A byte array has the same layout in every compspecs (no composite inside). *)
Lemma hs_small_fc_tuchar {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (A (@cenv_cs cs2) (Ptrofs.unsigned i)).
  tauto.
Qed.

(* bytes_at (stated at Noise.CS) as the byte array of the body's compspecs *)
Lemma hs_small_bytes_at sh bs p :
  bytes_at sh bs p = @data_at CSh sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof.
  unfold bytes_at, data_at, field_at. f_equal. f_equal. apply prop_ext. apply hs_small_fc_tuchar.
Qed.

(* the loop invariant of bytes_eq: equal prefixes extend by one equal byte *)
Lemma hs_small_prefix_step (A B: list byte) i : 0 <= i < Zlength A -> Zlength A = Zlength B ->
  sublist 0 i A = sublist 0 i B -> Byte.unsigned (Znth i A) = Byte.unsigned (Znth i B) ->
  sublist 0 (i + 1) A = sublist 0 (i + 1) B.
Proof.
  intros. rewrite !(sublist_split 0 i (i + 1)) by lia. rewrite !sublist_len_1 by lia.
  rewrite H1, <- (Byte.repr_unsigned (Znth i A)), H2, Byte.repr_unsigned. reflexivity.
Qed.

Lemma hs_small_eqb_false (A B: list byte) i : 0 <= i < Zlength A ->
  Byte.unsigned (Znth i A) <> Byte.unsigned (Znth i B) -> bytes_eqb A B = false.
Proof. intros. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A B); [subst; congruence | reflexivity]. Qed.

Lemma hs_small_eqb_true (A B: list byte) : Zlength A = Zlength B ->
  sublist 0 (Zlength A) A = sublist 0 (Zlength A) B -> bytes_eqb A B = true.
Proof.
  intros. rewrite !sublist_same in H0 by lia. subst.
  unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec B B); congruence.
Qed.

Lemma hs_small_Znth_bytes (A: list byte) i : 0 <= i < Zlength A -> Znth i (bytes A) = Vubyte (Znth i A).
Proof. intros. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

(* The shim's 64-bit clock globals (stated at Noise.CS): the same predicates in the body's compspecs. *)
Lemma hs_small_align_long (t: type) ce z : (t = tulong \/ t = tlong) ->
  align_compatible_rec ce t z <-> (8 | z).
Proof.
  intros Ht. split; intros A.
  - destruct Ht; subst; inversion A; subst; simpl in *; try discriminate;
      match goal with E: By_value _ = By_value _ |- _ => inversion E; subst; simpl in *; assumption end.
  - destruct Ht; subst; (eapply align_compatible_rec_by_value; [reflexivity | exact A]).
Qed.

Lemma hs_small_tulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at CSh sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  rewrite !hs_small_align_long by auto. tauto.
Qed.

Lemma hs_small_tlong sh (v: val) p : @data_at Noise.CS sh tlong v p = @data_at CSh sh tlong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  rewrite !hs_small_align_long by auto. tauto.
Qed.

(* any_u64, bytes_eq, any_clocks: the nondeterministic draws and the byte comparison *)
Lemma hs_body_small_ctx :
  @semax_body hs_Vh Ghs_any_u64 CSh H.f_any_u64 any_u64_spec /\
  @semax_body hs_Vh Ghs_bytes_eq CSh H.f_bytes_eq bytes_eq_spec /\
  @semax_body hs_Vh Ghs_any_clocks CSh H.f_any_clocks any_clocks_spec.
Proof.
  split; [|split].
  - (* any_u64: forward_call cannot fuse a call with the widening cast or the return that follows it, so
       each call gets its own postcondition *)
    start_function.
    apply semax_seq' with (P' := EX hi: Z,
      PROP (0 <= hi <= Int.max_unsigned) LOCAL (temp H._high (Vlong (Int64.repr hi))) SEP ()).
    { apply semax_seq' with (P' := EX hi: Z,
        PROP (0 <= hi <= Int.max_unsigned) LOCAL (temp H._t'1 (Vint (Int.repr hi))) SEP ()).
      - forward_call tt. Intros v. Exists v. entailer!.
      - Intros hi. forward. Exists hi. entailer!. }
    Intros hi.
    apply semax_seq' with (P' := EX lo: Z,
      PROP (0 <= lo <= Int.max_unsigned)
      LOCAL (temp H._high (Vlong (Int64.repr hi)); temp H._t'2 (Vint (Int.repr lo))) SEP ()).
    { forward_call tt. Intros v. Exists v. entailer!. }
    Intros lo. forward.
    Exists (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo)).
    entailer!.
  - (* bytes_eq: the loop keeps the compared prefixes equal *)
    start_function.
    rewrite !hs_small_bytes_at.
    forward_for_simple_bound (Zlength la) (EX i:Z, PROP (sublist 0 i la = sublist 0 i lb)
      LOCAL (temp H._a a; temp H._b b; temp H._n (Vlong (Int64.repr (Zlength la))))
      SEP (@data_at CSh sha (tarray tuchar (Zlength la)) (bytes la) a;
           @data_at CSh shb (tarray tuchar (Zlength lb)) (bytes lb) b))%assert.
    + entailer!.
    + cbv beta. Intros. forward.
      { rewrite hs_small_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite hs_small_Znth_bytes by lia.
      forward.
      { rewrite hs_small_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite hs_small_Znth_bytes by lia.
      forward_if.
      * forward.
        rewrite (hs_small_eqb_false la lb i) by auto. entailer!. rewrite !hs_small_bytes_at. cancel.
      * forward.
        entailer!. apply hs_small_prefix_step; auto.
    + forward.
      rewrite hs_small_eqb_true by auto. entailer!. rewrite !hs_small_bytes_at. cancel.
  - (* any_clocks: the three stores into the shim's clocks; the other shim globals are framed out *)
    start_function.
    unfold shim_state4, shim_core. Intros.
    rewrite !hs_small_tulong, !hs_small_tlong.
    freeze [3;4;5;6;7;8;9;10;11;12] FR.
    forward_call tt. Intros v1. forward.
    forward_call tt. Intros v2. forward.
    forward_call tt. Intros n. forward.
    Exists (Int64.shru v1 (Int64.repr (Int.unsigned (Int.repr 2)))) v2
      (Int64.repr (Int.unsigned (Int.modu (Int.repr n) (Int.repr 1000000000)))).
    entailer!.
    + pose proof (Z.mod_pos_bound n 1000000000 ltac:(lia)).
      rewrite Int.unsigned_repr by rep_lia. split; [|lia].
      rewrite Int64.shru_div_two_p. change (Int64.unsigned (Int64.repr 2)) with 2.
      pose proof (Int64.unsigned_range v1). change (two_p 2) with 4.
      rewrite Int64.unsigned_repr; [|split; [apply Z.div_pos|apply Z.div_le_upper_bound]; rep_lia].
      apply Z.div_lt_upper_bound; [lia|]. change (4 * 2^62) with Int64.modulus. lia.
    + thaw FR. unfold shim_state4, shim_core, shim_clocks; simpl.
      rewrite !hs_small_tulong, !hs_small_tlong. entailer!.
Qed.

(* new_device: the structs of noise.c are stated at Noise.CS, the body runs at CSh (same structs) *)
#[local] Instance hs_nd_N_H : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.
#[local] Instance hs_nd_H_N : change_composite_env CSh Noise.CS.
Proof. make_cs_preserve CSh Noise.CS. Defined.

Section NewDevice.
#[local] Existing Instance Noise.CS.

(* struct wg_device at Noise.CS as new_device uses it: its fields, the identity's fields at id_addr wg (the
   pieces wg_noise_set_static_identity_private_key takes) and the identity's tail padding *)
Lemma hs_nd_dev_split sh wg (dv: val) (pub priv: list val) (lk hv: val) (cv: @reptype Noise.CS t_cc) (pt it: val) :
  @field_compatible Noise.CS t_dev [] wg ->
  @data_at Noise.CS sh t_dev ((dv, ((pub, (priv, (lk, hv))), (cv, (pt, it)))) : @reptype Noise.CS t_dev) wg =
  (@field_at Noise.CS sh t_dev (DOT I._dev) dv wg *
  @field_at Noise.CS sh t_sid (DOT I._static_public) pub (id_addr wg) *
  @field_at Noise.CS sh t_sid (DOT I._static_private) priv (id_addr wg) *
  @field_at Noise.CS sh t_sid (DOT I._lock) lk (id_addr wg) *
  @field_at Noise.CS sh t_sid (DOT I._has_identity) hv (id_addr wg) * spacer sh 69 72 (id_addr wg) *
  @field_at Noise.CS sh t_dev (DOT I._cookie_checker) cv wg *
  @field_at Noise.CS sh t_dev (DOT I._peer_hashtable) pt wg *
  @field_at Noise.CS sh t_dev (DOT I._index_hashtable) it wg)%logic.
Proof.
  intros FC.
  unfold_data_at (@data_at Noise.CS _ _ _ wg).
  rewrite (@field_at_data_at Noise.CS _ _ (DOT I._static_identity)).
  rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  change (nested_field_offset t_dev (DOT I._static_identity)) with OFS_DEV_IDENTITY. fold (id_addr wg).
  change (nested_field_type t_dev (DOT I._static_identity)) with t_sid.
  unfold_data_at (data_at sh t_sid _ (id_addr wg)).
  rewrite !sepcon_assoc. reflexivity.
Qed.

End NewDevice.

Lemma hs_body_new_device_ctx x25519 :
  @semax_body hs_Vh (Ghs_new_device x25519) CSh H.f_new_device (new_device_spec x25519).
Proof.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_dev [] wg) as FC by entailer!.
  rewrite (@data_at__change_composite Noise.CS CSh _ sh t_dev) by reflexivity.
  rewrite (@data_at__change_composite Noise.CS CSh _ sh t_itab) by reflexivity.
  rewrite (@data_at__change_composite Noise.CS CSh _ sh t_ptab) by reflexivity.
  do 4 forward.
  forward_for_simple_bound 32 (EX i: Z,
    PROP () LOCAL (gvars gv; temp H._wg wg; temp H._indices ti; temp H._keys tk; temp H._private_key pk)
    SEP (@data_at CSh sh t_dev
          ((Vundef, ((Zrepeat (Vint (Int.repr 0)) i ++ Zrepeat Vundef (32 - i), (Zrepeat Vundef 32, (Vundef, Vundef))),
            (@default_val CSh t_cc, (tk, ti)))) : @reptype CSh t_dev) wg;
         @data_at CSh sh t_itab nullval ti; @data_at CSh sh t_ptab nullval tk; bytes_at shk raw pk; wg_consts5 gv)).
  { entailer!. }
  { forward. entailer!. apply derives_refl'.
    change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
    replace (upd_Znth i (Zrepeat (Vint (Int.repr 0)) i ++ Zrepeat Vundef (32 - i)) (Vint (Int.repr 0)))
      with (Zrepeat (Vint (Int.repr 0)) (i + 1) ++ Zrepeat Vundef (32 - (i + 1))) by list_solve.
    reflexivity. }
  erewrite (@data_at_change_composite CSh Noise.CS _ sh t_dev _ _ (JMeq_refl _)) by reflexivity.
  rewrite hs_nd_dev_split by auto.
  replace (Zrepeat (Vint (Int.repr 0)) 32 ++ Zrepeat Vundef (32 - 32)) with (bytes zeros32) by reflexivity.
  forward_call (gv, sh, id_addr wg, zeros32, shk, pk, raw).
  { cancel. }
  rewrite (@data_at_change_composite CSh Noise.CS _ sh t_itab nullval nullval (JMeq_refl _)) by reflexivity.
  rewrite (@data_at_change_composite CSh Noise.CS _ sh t_ptab nullval nullval (JMeq_refl _)) by reflexivity.
  unfold device_rep5, ptable, hs_dev, hs_id. cbn [d_id d_ptab d_itab].
  entailer!.
Qed.

Section NewPeer.

(* the predicates of the specification are stated at Noise.CS, the body runs at CSh (same kernel structs) *)
#[local] Instance hs_new_peer_N_H : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.
#[local] Instance hs_new_peer_H_N : change_composite_env CSh Noise.CS.
Proof. make_cs_preserve CSh Noise.CS. Defined.

Section Pieces.
#[local] Existing Instance Noise.CS.

(* struct wg_peer at Noise.CS cut into its fields and its padding *)
Lemma hs_new_peer_split sh p :
  @data_at_ Noise.CS sh t_peer p =
  (@field_at_ Noise.CS sh t_peer (DOT H._device) p * @field_at_ Noise.CS sh t_peer (DOT H._is_dead) p *
  spacer sh 9 16 p * @field_at_ Noise.CS sh t_peer (DOT H._keypairs) p *
  @field_at_ Noise.CS sh t_peer (DOT H._handshake) p *
  @field_at_ Noise.CS sh t_peer (DOT H._last_sent_handshake) p *
  @field_at_ Noise.CS sh t_peer (DOT H._latest_cookie) p *
  @field_at_ Noise.CS sh t_peer (DOT H._refcount) p * spacer sh 476 480 p *
  @field_at_ Noise.CS sh t_peer (DOT H._internal_id) p * @field_at_ Noise.CS sh t_peer (DOT H._pubkey_next) p)%logic.
Proof.
  change (@data_at_ Noise.CS sh t_peer p) with (@data_at Noise.CS sh t_peer (@default_val Noise.CS t_peer) p).
  unfold_data_at (@data_at Noise.CS sh t_peer _ p).
  unfold field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the handshake member of struct wg_peer is the struct noise_handshake at hs_addr *)
Lemma hs_new_peer_hs sh p :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at_ Noise.CS sh t_peer (DOT H._handshake) p = @data_at_ Noise.CS sh t_hs (hs_addr p).
Proof.
  intros FC. unfold field_at_. rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

(* the keypairs member of struct wg_peer is the struct noise_keypairs at kps_addr *)
Lemma hs_new_peer_kps sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_peer (DOT H._keypairs) v p = @data_at Noise.CS sh t_kps v (kps_addr p).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

End Pieces.

(* new_peer: the stores to the peer's own fields, wg_noise_handshake_init on its handshake with the device's
   identity (the preshared key is not NULL: bytes_at of 32 bytes is at a pointer), then the peer is pushed at
   the head of the device's public-key table *)
Lemma hs_body_new_peer_ctx x25519 :
  @semax_body hs_Vh (Ghs_new_peer x25519) CSh H.f_new_peer (new_peer_spec x25519).
Proof.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_peer [] peer) as FCp by entailer!.
  assert_PROP (isptr pskp) as Pk by (unfold bytes_at; entailer!).
  rewrite hs_new_peer_split, (hs_new_peer_hs sh peer FCp).
  rewrite !(@field_at__change_composite Noise.CS CSh _ sh t_peer) by reflexivity.
  unfold device_rep5. Intros.
  do 6 forward.
  replace (bytes_at shq psk pskp) with (if eq_dec pskp nullval then emp else bytes_at shq psk pskp)
    by (rewrite if_false by (intro E; subst; contradiction); reflexivity).
  forward_call (gv, sh, peer, shd, id_addr wg, d_id D, shk, pubp, pub, shq, pskp, psk).
  rewrite !if_false by (intro E; subst; contradiction).
  erewrite (@field_at_change_composite Noise.CS CSh _ shd t_dev (DOT I._peer_hashtable) _ _ (JMeq_refl _))
    by reflexivity.
  unfold ptable. erewrite (@data_at_change_composite Noise.CS CSh _ sht t_ptab _ _ (JMeq_refl _)) by reflexivity.
  change I._peer_hashtable with H._peer_hashtable.
  do 5 forward.
  erewrite (@field_at_change_composite CSh Noise.CS _ sh t_peer (DOT H._device) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSh Noise.CS _ sh t_peer (DOT H._is_dead) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSh Noise.CS _ sh t_peer (DOT H._keypairs) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSh Noise.CS _ sh t_peer (DOT H._refcount) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSh Noise.CS _ sh t_peer (DOT H._pubkey_next) _ _ (JMeq_refl _))
    by reflexivity.
  rewrite !(@field_at__change_composite CSh Noise.CS _ sh t_peer) by reflexivity.
  erewrite (@field_at_change_composite CSh Noise.CS _ shd t_dev (DOT H._peer_hashtable) _ _ (JMeq_refl _))
    by reflexivity.
  erewrite (@data_at_change_composite CSh Noise.CS _ sht t_ptab _ _ (JMeq_refl _)) by reflexivity.
  rewrite (hs_new_peer_kps sh peer _ FCp).
  unfold peer_rep5, device_rep5, kps_rep, ptable, hs_peer0.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_refs p_pknext].
  (* the keypairs' lock is never written: its default value *)
  match goal with |- context [data_at _ _ (_, (_, (_, ?l))) (kps_addr peer)] => Exists l end.
  change I._device with H._device; change I._is_dead with H._is_dead;
    change I._last_sent_handshake with H._last_sent_handshake; change I._latest_cookie with H._latest_cookie;
    change I._refcount with H._refcount; change I._internal_id with H._internal_id;
    change I._pubkey_next with H._pubkey_next; change I._peer_hashtable with H._peer_hashtable.
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  change (Val.of_bool false) with (Vint Int.zero).
  change (Vint Int.one) with (Vint (Int.repr 1)).
  entailer!.
Qed.

End NewPeer.

Require Import WgNoise.proof.harness.hs_common.hs_pair_lemmas.

Section NewPair.
#[local] Existing Instance CSh.

(* the side conditions of new_pair's calls: the arguments &p->x are the members' addresses, lengths *)
Local Ltac hs_np_side :=
  first [ rewrite Zlength_map; auto
        | split; [assumption | rewrite Zlength_map; auto]
        | entailer!; unfold pair_a, pair_b, pair_ai, pair_bi, pair_ak, pair_bk, pair_ap, pair_bp, id_addr,
                            OFS_DEV_IDENTITY;
          rewrite !field_address_offset by auto with field_compatible; simpl; rewrite ?offset_offset_val;
          auto ].

(* new_pair: struct pair split into its members, the keys drawn, the two devices, then each device's peer
   for the other, keyed with the other device's static public key read in place *)
Lemma hs_body_new_pair_ctx x25519 :
  @semax_body hs_Vh (Ghs_new_pair x25519) CSh H.f_new_pair (new_pair_spec x25519).
Proof.
  start_function.
  assert_PROP (field_compatible t_pair [] p) as FC by entailer!.
  rewrite hs_pair_split by auto.
  forward_call (v_a_private, 32, Tsh). Intros a0.
  forward_call (v_b_private, 32, Tsh). Intros b0.
  forward_call (v_psk, 32, Tsh). Intros k0.
  forward_call (gv, h, ck, kc).
  rewrite (hs_nondet_bytes Tsh 32 a0), (hs_nondet_bytes Tsh 32 b0), (hs_nondet_bytes Tsh 32 k0) by auto.
  forward_call (gv, sh, pair_a p, pair_ai p, pair_ak p, Tsh, v_a_private, map Byte.repr a0); [hs_np_side | hs_np_side |].
  forward_call (gv, sh, pair_b p, pair_bi p, pair_bk p, Tsh, v_b_private, map Byte.repr b0); [hs_np_side | hs_np_side |].
  (* A's peer for B, with B's public key *)
  assert_PROP (Zlength (id_pub (hs_id x25519 (map Byte.repr b0))) = 32) as LB.
  { unfold device_rep5, identity_rep. Intros. entailer!.
    match goal with Hi: id_ok _ |- _ => exact (proj1 Hi) end. }
  rewrite (hs_dev_pub_split sh (pair_b p)). Intros. simpl d_id.
  forward_call (gv, sh, pair_ap p, sh, pair_a p, pair_devA x25519 p (map Byte.repr a0), sh, nullval,
                sh, id_addr (pair_b p), id_pub (hs_id x25519 (map Byte.repr b0)), Tsh, v_psk, map Byte.repr k0);
    [hs_np_side | hs_np_side |].
  (* B's peer for A, with A's public key *)
  sep_apply (derives_refl' _ _ (eq_sym (hs_dev_pub_split sh (pair_b p) (pair_devB x25519 p (map Byte.repr b0))))).
  assert_PROP (Zlength (id_pub (hs_id x25519 (map Byte.repr a0))) = 32) as LA.
  { unfold device_rep5, identity_rep. Intros. entailer!.
    match goal with Hi: id_ok _ |- _ => exact (proj1 Hi) end. }
  unfold pair_devA. rewrite (hs_dev_pub_split sh (pair_a p)). Intros. simpl d_id.
  forward_call (gv, sh, pair_bp p, sh, pair_b p, pair_devB x25519 p (map Byte.repr b0), sh, nullval,
                sh, id_addr (pair_a p), id_pub (hs_id x25519 (map Byte.repr a0)), Tsh, v_psk, map Byte.repr k0);
    [hs_np_side | hs_np_side |].
  sep_apply (derives_refl' _ _ (eq_sym (hs_dev_pub_split sh (pair_a p) (pair_devA x25519 p (map Byte.repr a0))))).
  (* the pair: the two devices, the tables (A's and B's peer in them), the peers; the local arrays freed *)
  Exists (map Byte.repr a0) (map Byte.repr b0) (map Byte.repr k0).
  unfold hs_pair. rewrite !hs_table_itable by auto.
  sep_apply (hs_bytes_free (cs:=CSh) Tsh (map Byte.repr a0) v_a_private).
  sep_apply (hs_bytes_free (cs:=CSh) Tsh (map Byte.repr b0) v_b_private).
  sep_apply (hs_bytes_free (cs:=CSh) Tsh (map Byte.repr k0) v_psk).
  rewrite !Zlength_map, H, H1, H3.
  unfold pair_devA, pair_devB, pair_peerA, pair_peerB, hs_dev. simpl d_ptab. simpl d_id.
  entailer!.
Qed.

End NewPair.

(* ---- copy_peer: the copied peer at CSh, field by field ---- *)

#[local] Instance hscp_cce_NH : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.
#[local] Instance hscp_cce_HN : change_composite_env CSh Noise.CS.
Proof. make_cs_preserve CSh Noise.CS. Defined.

(* the fields of a struct of noise.c (a peer, a handshake) at Noise.CS are the same predicates at CSh *)
Ltac hscp_to_CSh :=
  repeat match goal with
  | |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?q] =>
      rewrite (field_at_cs_eq (cs1 := Noise.CS) (cs2 := CSh) sh t gfs v v q (JMeq_refl _)) by reflexivity
  | |- context [@field_at_ Noise.CS ?sh ?t ?gfs ?q] =>
      rewrite (@field_at__change_composite Noise.CS CSh _ sh t gfs) by reflexivity
  end.

Section CopyPeer.
#[local] Existing Instance CSh.
Local Open Scope logic.

(* struct wg_peer at q cut into the fields copy_peer writes (with values given) and the others (any), with the
   padding of the struct and of its keypairs and handshake *)
Definition hscp_shape (sh: share) (q: val) (cur prv nxt: val) (ent: reptype t_entry_s) (st lic sid: val)
    (a1 a2 a3 a4 a5 a6 a7 ts: list val) (ri rc: val) : mpred :=
  field_at_ sh t_peer (DOT H._device) q *
  field_at_ sh t_peer (DOT H._is_dead) q *
  field_at sh t_peer (DOT H._keypairs DOT H._current_keypair) cur q *
  field_at sh t_peer (DOT H._keypairs DOT H._previous_keypair) prv q *
  field_at sh t_peer (DOT H._keypairs DOT H._next_keypair) nxt q *
  field_at_ sh t_peer (DOT H._keypairs DOT H._keypair_update_lock) q *
  field_at sh t_peer (DOT H._handshake DOT H._entry) ent q *
  field_at sh t_peer (DOT H._handshake DOT H._state) st q *
  field_at sh t_peer (DOT H._handshake DOT H._last_initiation_consumption) lic q *
  field_at sh t_peer (DOT H._handshake DOT H._static_identity) sid q *
  field_at sh t_peer (DOT H._handshake DOT H._ephemeral_private) a1 q *
  field_at sh t_peer (DOT H._handshake DOT H._remote_static) a2 q *
  field_at sh t_peer (DOT H._handshake DOT H._remote_ephemeral) a3 q *
  field_at sh t_peer (DOT H._handshake DOT H._precomputed_static_static) a4 q *
  field_at sh t_peer (DOT H._handshake DOT H._preshared_key) a5 q *
  field_at sh t_peer (DOT H._handshake DOT H._hash) a6 q *
  field_at sh t_peer (DOT H._handshake DOT H._chaining_key) a7 q *
  field_at sh t_peer (DOT H._handshake DOT H._latest_timestamp) ts q *
  field_at sh t_peer (DOT H._handshake DOT H._remote_index) ri q *
  field_at_ sh t_peer (DOT H._handshake DOT H._lock) q *
  field_at_ sh t_peer (DOT H._last_sent_handshake) q *
  field_at_ sh t_peer (DOT H._latest_cookie) q *
  field_at sh t_peer (DOT H._refcount) rc q *
  field_at_ sh t_peer (DOT H._internal_id) q *
  field_at_ sh t_peer (DOT H._pubkey_next) q *
  spacer sh 9 16 q * spacer sh (OFS_PEER_KEYPAIRS + 28) (OFS_PEER_KEYPAIRS + 32) q *
  spacer sh (OFS_PEER_HANDSHAKE + 36) (OFS_PEER_HANDSHAKE + 40) q *
  spacer sh (OFS_PEER_HANDSHAKE + 300) (OFS_PEER_HANDSHAKE + 304) q * spacer sh 476 480 q.

(* the uninitialised destination: the shape with every copied field undefined *)
Lemma hscp_dst_split sh q :
  @data_at_ Noise.CS sh t_peer q =
  hscp_shape sh q Vundef Vundef Vundef (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))) Vundef Vundef Vundef
    (Zrepeat Vundef 32) (Zrepeat Vundef 32) (Zrepeat Vundef 32) (Zrepeat Vundef 32) (Zrepeat Vundef 32)
    (Zrepeat Vundef 32) (Zrepeat Vundef 32) (Zrepeat Vundef 12) Vundef Vundef.
Proof.
  rewrite (data_at__cs_eq (cs1 := Noise.CS) (cs2 := CSh)) by reflexivity.
  change (@data_at_ CSh sh t_peer q) with (@data_at CSh sh t_peer (@default_val CSh t_peer) q).
  unfold_data_at (@data_at CSh sh t_peer _ q).
  unfold_field_at 3%nat. unfold_field_at 7%nat.
  unfold hscp_shape, field_at_, OFS_PEER_KEYPAIRS, OFS_PEER_HANDSHAKE. simpl Z.add.
  apply pred_ext; cancel.
Qed.

(* snap_rep: the shape with the copied values *)
Lemma hscp_snap_eq sh q P E next hashed :
  snap_rep sh q P E next hashed =
  !! (@field_compatible Noise.CS t_peer [] q /\ hs_ok (p_hs P)) &&
  hscp_shape sh q (p_cur P) (p_prev P) (p_next P) (entry_val E next hashed) (Vint (hs_state (p_hs P)))
    (Vlong (hs_lic (p_hs P))) (hs_sid (p_hs P)) (bytes (hs_eph (p_hs P))) (bytes (hs_rstatic (p_hs P)))
    (bytes (hs_reph (p_hs P))) (bytes (hs_ss (p_hs P))) (bytes (hs_psk (p_hs P))) (bytes (hs_hash (p_hs P)))
    (bytes (hs_ck (p_hs P))) (bytes (hs_ts (p_hs P))) (Vint (hs_rindex (p_hs P))) (Vint (p_refs P)).
Proof.
  unfold snap_rep, hscp_shape. cbv zeta. hscp_to_CSh. reflexivity.
Qed.

(* the source peer's keypairs and handshake entry, as fields of the struct at CSh *)
Lemma hscp_kps sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_kps v (kps_addr p) = @field_at CSh sh t_peer (DOT H._keypairs) v p.
Proof.
  intros FC. rewrite (data_at_cs_eq (cs1 := Noise.CS) (cs2 := CSh) sh t_kps v v _ (JMeq_refl _)) by reflexivity.
  assert (FC': field_compatible t_peer [] p) by (apply (@field_compatible_change_composite Noise.CS CSh _ t_peer); auto).
  rewrite field_at_data_at, field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hscp_entry sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at CSh sh t_hs (DOT H._entry) v (hs_addr p).
Proof.
  intros FC. rewrite (data_at_cs_eq (cs1 := Noise.CS) (cs2 := CSh) sh t_entry_s v v _ (JMeq_refl _)) by reflexivity.
  assert (FC': field_compatible t_peer [] p) by (apply (@field_compatible_change_composite Noise.CS CSh _ t_peer); auto).
  assert (FC1: field_compatible t_peer (DOT H._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)) by (apply field_compatible_nested_field in FC1; exact FC1).
  rewrite field_at_data_at, field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero by (destruct FC2; auto). reflexivity.
Qed.

(* the loop's byte copies: after i steps, the first i bytes of A are copied *)
Lemma hscp_upd_prefix (A: list byte) i n : 0 <= i < n -> Zlength A = n ->
  upd_Znth i (bytes (sublist 0 i A) ++ Zrepeat Vundef (n - i)) (Vubyte (Znth i A)) =
  bytes (sublist 0 (i + 1) A) ++ Zrepeat Vundef (n - (i + 1)).
Proof. intros. unfold bytes. list_solve. Qed.

Lemma hscp_Znth_bytes (A: list byte) i : 0 <= i < Zlength A -> Znth i (bytes A) = Vubyte (Znth i A).
Proof. intros. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

Lemma hscp_tc_ubyte b : is_int I8 Unsigned (Vubyte b).
Proof. simpl. pose proof (Byte.unsigned_range_2 b). rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma hscp_cast_byte (A: list byte) i : 0 <= i < Zlength A ->
  force_val (sem_cast_i2i I8 Unsigned (Znth i (bytes A))) = Vubyte (Znth i A).
Proof.
  intros. rewrite hscp_Znth_bytes by lia. simpl. unfold Vubyte. f_equal. apply zero_ext_inrange.
  pose proof (Byte.unsigned_range_2 (Znth i A)). rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Lemma hscp_prefix_full (A: list byte) n : Zlength A = n ->
  bytes (sublist 0 n A) ++ Zrepeat Vundef (n - n) = bytes A.
Proof. intros. rewrite sublist_same, Z.sub_diag, Zrepeat_0, app_nil_r by lia. reflexivity. Qed.

End CopyPeer.

(* copy_peer: the source's fields are read at CSh (hscp_kps, hscp_entry, hscp_to_CSh), the destination is cut
   by hscp_dst_split; the loop copies the seven 32-byte arrays and the first 12 bytes of the timestamp *)
Lemma hs_body_copy_peer_ctx :
  @semax_body hs_Vh Ghs_copy_peer CSh H.f_copy_peer copy_peer_spec.
Proof.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) as FCH.
  { unfold peer_rep5, hs_rep. entailer!. }
  destruct FCH as [FC HOK].
  assert_PROP (@field_compatible Noise.CS t_peer [] q) as FCq by entailer!.
  rewrite hscp_dst_split. unfold peer_rep5, hs_rep, kps_rep, entry_at.
  Intros. Intros lkh lkk.
  rewrite (hscp_kps shp p _ FC), (hscp_entry she p _ FC).
  hscp_to_CSh.
  unfold hscp_shape, entry_val. repeat flatten_sepcon_in_SEP. unfold hs_addr in *.
  do 6 forward.
  { entailer!. destruct hashed; simpl; auto. }
  do 13 forward.
  match goal with |- context [temp H._h ?v] => replace v with (offset_val OFS_PEER_HANDSHAKE p) by reflexivity end.
  freeze [0;1;2;3;4;5;6;7;8;9;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;44;45;46;47;48;49;50;51;52;53;54;55] FR.
  destruct HOK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  forward_for_simple_bound 32 (EX i: Z, PROP ()
    LOCAL (temp H._h (offset_val OFS_PEER_HANDSHAKE p); temp H._to q; temp H._from p)
    SEP (FRZL FR;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._ephemeral_private)
        (bytes (sublist 0 i (hs_eph (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._remote_static)
        (bytes (sublist 0 i (hs_rstatic (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._remote_ephemeral)
        (bytes (sublist 0 i (hs_reph (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._precomputed_static_static)
        (bytes (sublist 0 i (hs_ss (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._preshared_key)
        (bytes (sublist 0 i (hs_psk (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._hash)
        (bytes (sublist 0 i (hs_hash (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._chaining_key)
        (bytes (sublist 0 i (hs_ck (p_hs P))) ++ Zrepeat Vundef (32 - i)) q;
      @field_at CSh shq t_peer (DOT H._handshake DOT H._latest_timestamp)
        (bytes (sublist 0 (Z.min i 12) (hs_ts (p_hs P))) ++ Zrepeat Vundef (12 - Z.min i 12)) q;
      @field_at CSh shp t_hs (DOT I._ephemeral_private) (bytes (hs_eph (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._remote_static) (bytes (hs_rstatic (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._remote_ephemeral) (bytes (hs_reph (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._precomputed_static_static) (bytes (hs_ss (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._preshared_key) (bytes (hs_psk (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._hash) (bytes (hs_hash (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._chaining_key) (bytes (hs_ck (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p);
      @field_at CSh shp t_hs (DOT I._latest_timestamp) (bytes (hs_ts (p_hs P))) (offset_val OFS_PEER_HANDSHAKE p)))%assert.
  { entailer!. }
  - do 7 (forward; [entailer!; exact (hscp_tc_ubyte _) | forward]).
    forward_if.
    + rewrite Int64.unsigned_repr in H6 by rep_lia. rewrite Int64.unsigned_repr in H6 by rep_lia.
      rewrite (Z.min_l i 12) by lia.
      forward; [entailer!; exact (hscp_tc_ubyte _) | forward].
      rewrite !hscp_cast_byte by lia. rewrite !hscp_upd_prefix by lia.
      rewrite (Z.min_l (i + 1) 12) by lia.
      entailer!.
    + rewrite Int64.unsigned_repr in H6 by rep_lia. rewrite Int64.unsigned_repr in H6 by rep_lia.
      forward.
      rewrite !hscp_cast_byte by lia. rewrite !hscp_upd_prefix by lia.
      rewrite (Z.min_r i 12), (Z.min_r (i + 1) 12) by lia.
      entailer!.
  - change (Z.min 32 12) with 12. rewrite !hscp_prefix_full by auto.
    thaw FR.
    do 8 forward.
    replace (force_val (sem_cast_i2bool (Val.of_bool hashed))) with (Val.of_bool hashed)
      by (destruct hashed; reflexivity).
    assert (HOK: hs_ok (p_hs P)) by (repeat split; auto).
    rewrite hscp_snap_eq. unfold hscp_shape, peer_rep5, hs_rep, kps_rep, entry_at, entry_val.
    Exists lkh lkk.
    change (offset_val OFS_PEER_HANDSHAKE p) with (hs_addr p).
    rewrite (hscp_kps shp p _ FC), (hscp_entry she p _ FC).
    hscp_to_CSh.
    entailer!.
Qed.

(* ---- same_peer: the peer and its copy as the comparisons read them ---- *)
Section SamePeer.
#[local] Existing Instance CSh.
#[local] Instance hsp_cce_n : change_composite_env Noise.CS CSh. make_cs_preserve Noise.CS CSh. Defined.
#[local] Instance hsp_cce_h : change_composite_env CSh Noise.CS. make_cs_preserve CSh Noise.CS. Defined.
Local Open Scope logic.

(* a byte array is the same predicate in any compspecs *)
Lemma hsp_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
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

(* the fields of a handshake at h that same_peer compares, the arrays as bytes_at at their addresses *)
Definition hsp_hs (sh: share) (h: val) (Hs: handshake) : mpred :=
  field_at sh t_hs (DOT H._state) (Vint (hs_state Hs)) h *
  field_at sh t_hs (DOT H._last_initiation_consumption) (Vlong (hs_lic Hs)) h *
  field_at sh t_hs (DOT H._static_identity) (hs_sid Hs) h *
  bytes_at sh (hs_eph Hs) (field_address t_hs (DOT H._ephemeral_private) h) *
  bytes_at sh (hs_rstatic Hs) (field_address t_hs (DOT H._remote_static) h) *
  bytes_at sh (hs_reph Hs) (field_address t_hs (DOT H._remote_ephemeral) h) *
  bytes_at sh (hs_ss Hs) (field_address t_hs (DOT H._precomputed_static_static) h) *
  bytes_at sh (hs_psk Hs) (field_address t_hs (DOT H._preshared_key) h) *
  bytes_at sh (hs_hash Hs) (field_address t_hs (DOT H._hash) h) *
  bytes_at sh (hs_ck Hs) (field_address t_hs (DOT H._chaining_key) h) *
  bytes_at sh (hs_ts Hs) (field_address t_hs (DOT H._latest_timestamp) h) *
  field_at sh t_hs (DOT H._remote_index) (Vint (hs_rindex Hs)) h.

(* the rest of peer_rep5 (fields same_peer does not read) *)
Definition hsp_prest (sh: share) (p: val) (P: peer) : mpred :=
  @field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
  @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  (EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk (hs_addr p)) *
  spacer sh 36 40 (hs_addr p) * spacer sh 300 304 (hs_addr p) *
  @field_at_ Noise.CS sh t_peer [StructField I._last_sent_handshake] p *
  @field_at_ Noise.CS sh t_peer [StructField I._latest_cookie] p *
  @field_at_ Noise.CS sh t_peer [StructField I._internal_id] p *
  @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Local Ltac hsp_cc f v :=
  rewrite (@field_at_change_composite Noise.CS CSh _ _ t_hs (DOT f) v v (JMeq_refl v)) by reflexivity.

(* hs_rep's compared fields, at noise.c's compspecs *)
Lemma hsp_hs_fields sh h Hs :
  hs_ok Hs ->
  @field_at Noise.CS sh t_hs [StructField I._state] (Vint (hs_state Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._static_identity] (hs_sid Hs) h *
  @field_at Noise.CS sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_static] (bytes (hs_rstatic Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._preshared_key] (bytes (hs_psk Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._hash] (bytes (hs_hash Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._chaining_key] (bytes (hs_ck Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts Hs)) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_index] (Vint (hs_rindex Hs)) h =
  hsp_hs sh h Hs.
Proof.
  intros HOK. pose proof HOK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  unfold hsp_hs.
  hsp_cc I._state (Vint (hs_state Hs)).
  hsp_cc I._last_initiation_consumption (Vlong (hs_lic Hs)).
  hsp_cc I._static_identity (hs_sid Hs). hsp_cc I._remote_index (Vint (hs_rindex Hs)).
  hsp_cc I._ephemeral_private (bytes (hs_eph Hs)).
  hsp_cc I._remote_static (bytes (hs_rstatic Hs)).
  hsp_cc I._remote_ephemeral (bytes (hs_reph Hs)).
  hsp_cc I._precomputed_static_static (bytes (hs_ss Hs)).
  hsp_cc I._preshared_key (bytes (hs_psk Hs)). hsp_cc I._hash (bytes (hs_hash Hs)).
  hsp_cc I._chaining_key (bytes (hs_ck Hs)). hsp_cc I._latest_timestamp (bytes (hs_ts Hs)).
  rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
    (field_at_data_at sh t_hs (DOT I._remote_static)),
    (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
    (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
    (field_at_data_at sh t_hs (DOT I._preshared_key)),
    (field_at_data_at sh t_hs (DOT I._hash)),
    (field_at_data_at sh t_hs (DOT I._chaining_key)),
    (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type. unfold bytes_at.
  rewrite L1, L2, L3, L4, L5, L6, L7, L8.
  rewrite !(@hsp_data_at_cs CSh Noise.CS).
  apply pred_ext; cancel.
Qed.

(* hs_rep: the compared fields, the lock and the padding *)
Lemma hsp_hs_eq sh h Hs :
  hs_ok Hs ->
  hs_rep sh h Hs =
  hsp_hs sh h Hs * (EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.
Proof.
  intros HOK. unfold hs_rep. rewrite prop_true_andp by auto. rewrite <- (hsp_hs_fields sh h Hs HOK).
  apply pred_ext; cancel.
Qed.

(* the address of a field of the handshake of the peer at q, relative to the handshake at hs_addr q *)
Lemma hsp_fa f q :
  @field_compatible Noise.CS t_peer [] q ->
  @field_address Noise.CS t_peer (DOT I._handshake DOT f) q = @field_address Noise.CS t_hs (DOT f) (hs_addr q).
Proof.
  intros FC.
  change [StructField f; StructField I._handshake] with ([StructField f] ++ [StructField I._handshake]).
  rewrite (@field_address_app Noise.CS t_peer (DOT I._handshake) (DOT f)).
  rewrite (@field_address_offset Noise.CS t_peer (DOT I._handshake)) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hsp_fc p : @field_compatible Noise.CS t_peer [] p <-> field_compatible t_peer [] p.
Proof. apply (@field_compatible_change_composite Noise.CS CSh _ t_peer). reflexivity. Qed.

(* the keypairs of the peer at p, as a field of struct wg_peer *)
Lemma hsp_kps_eq sh p (c d e lk: val) :
  field_compatible t_peer [] p ->
  @data_at Noise.CS sh t_kps (c, (d, (e, lk))) (kps_addr p) =
  field_at sh t_peer (DOT H._keypairs) (c, (d, (e, lk))) p.
Proof.
  intros FC.
  rewrite (@data_at_change_composite Noise.CS CSh _ sh t_kps _ _ (JMeq_refl _)) by reflexivity.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  reflexivity.
Qed.

(* peer_rep5 as same_peer reads it *)
Lemma hsp_peer_eq sh p P :
  peer_rep5 sh p P =
  !! (field_compatible t_peer [] p /\ hs_ok (p_hs P)) &&
  (hsp_hs sh (hs_addr p) (p_hs P) *
   (EX lk: val, field_at sh t_peer (DOT H._keypairs) (p_cur P, (p_prev P, (p_next P, lk))) p) *
   field_at sh t_peer (DOT H._refcount) (Vint (p_refs P)) p * hsp_prest sh p P).
Proof.
  unfold peer_rep5, kps_rep, hsp_prest.
  rewrite (@field_at_change_composite Noise.CS CSh _ _ t_peer (DOT I._refcount) _ _ (JMeq_refl _)) by reflexivity.
  apply pred_ext.
  - Intros lk. rename H into FC0. pose proof (proj1 (hsp_fc p) FC0) as FC.
    assert_PROP (hs_ok (p_hs P)) as HOK by (unfold hs_rep; entailer!).
    rewrite hsp_hs_eq by auto. rewrite hsp_kps_eq by auto. Intros lk'.
    Exists lk lk'. entailer!.
  - Intros lk lk'. rename H into FC.
    assert (HOK: hs_ok (p_hs P)) by (unfold hs_ok; tauto).
    rewrite hsp_hs_eq by auto.
    Exists lk. rewrite hsp_kps_eq by auto. entailer!.
    + apply hsp_fc; auto.
    + Exists lk'. cancel.
Qed.

(* the handshake entry of the peer at p, as the field entry of its handshake *)
Lemma hsp_entry_eq sh p E next hashed :
  field_compatible t_peer [] p ->
  entry_at sh (hs_addr p) E next hashed = @field_at CSh sh t_hs (DOT H._entry) (entry_val E next hashed) (hs_addr p).
Proof.
  intros FC. unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS CSh _ sh t_entry_s _ _ (JMeq_refl _)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT H._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT H._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

(* the fields of snap_rep that same_peer does not read *)
Definition hsp_srest (sh: share) (q: val) : mpred :=
  @field_at_ Noise.CS sh t_peer (DOT I._device) q *
  @field_at_ Noise.CS sh t_peer (DOT I._is_dead) q *
  @field_at_ Noise.CS sh t_peer (DOT I._keypairs DOT I._keypair_update_lock) q *
  @field_at_ Noise.CS sh t_peer (DOT I._handshake DOT I._lock) q *
  @field_at_ Noise.CS sh t_peer (DOT I._last_sent_handshake) q *
  @field_at_ Noise.CS sh t_peer (DOT I._latest_cookie) q *
  @field_at_ Noise.CS sh t_peer (DOT I._internal_id) q *
  @field_at_ Noise.CS sh t_peer (DOT I._pubkey_next) q *
  spacer sh 9 16 q * spacer sh (OFS_PEER_KEYPAIRS + 28) (OFS_PEER_KEYPAIRS + 32) q *
  spacer sh (OFS_PEER_HANDSHAKE + 36) (OFS_PEER_HANDSHAKE + 40) q *
  spacer sh (OFS_PEER_HANDSHAKE + 300) (OFS_PEER_HANDSHAKE + 304) q * spacer sh 476 480 q.

Local Ltac hsp_rr f :=
  rewrite (@field_at_data_at Noise.CS _ t_peer (DOT I._handshake DOT f)), hsp_fa by auto.

(* snap_rep as same_peer reads it: the copied handshake at hs_addr q *)
Lemma hsp_snap_eq sh q P E next hashed :
  snap_rep sh q P E next hashed =
  !! (field_compatible t_peer [] q /\ hs_ok (p_hs P)) &&
  (@field_at CSh sh t_hs (DOT H._entry) (entry_val E next hashed) (hs_addr q) *
   hsp_hs sh (hs_addr q) (p_hs P) *
   field_at sh t_peer (DOT H._keypairs DOT H._current_keypair) (p_cur P) q *
   field_at sh t_peer (DOT H._keypairs DOT H._previous_keypair) (p_prev P) q *
   field_at sh t_peer (DOT H._keypairs DOT H._next_keypair) (p_next P) q *
   field_at sh t_peer (DOT H._refcount) (Vint (p_refs P)) q *
   hsp_srest sh q).
Proof.
  assert (BODY: @field_compatible Noise.CS t_peer [] q -> hs_ok (p_hs P) ->
    @field_at CSh sh t_hs (DOT H._entry) (entry_val E next hashed) (hs_addr q) *
    hsp_hs sh (hs_addr q) (p_hs P) *
    field_at sh t_peer (DOT H._keypairs DOT H._current_keypair) (p_cur P) q *
    field_at sh t_peer (DOT H._keypairs DOT H._previous_keypair) (p_prev P) q *
    field_at sh t_peer (DOT H._keypairs DOT H._next_keypair) (p_next P) q *
    field_at sh t_peer (DOT H._refcount) (Vint (p_refs P)) q * hsp_srest sh q =
    @field_at_ Noise.CS sh t_peer (DOT I._device) q *
    @field_at_ Noise.CS sh t_peer (DOT I._is_dead) q *
    @field_at Noise.CS sh t_peer (DOT I._keypairs DOT I._current_keypair) (p_cur P) q *
    @field_at Noise.CS sh t_peer (DOT I._keypairs DOT I._previous_keypair) (p_prev P) q *
    @field_at Noise.CS sh t_peer (DOT I._keypairs DOT I._next_keypair) (p_next P) q *
    @field_at_ Noise.CS sh t_peer (DOT I._keypairs DOT I._keypair_update_lock) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._entry) (entry_val E next hashed) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._state) (Vint (hs_state (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._last_initiation_consumption) (Vlong (hs_lic (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._static_identity) (hs_sid (p_hs P)) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._ephemeral_private) (bytes (hs_eph (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._remote_static) (bytes (hs_rstatic (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._remote_ephemeral) (bytes (hs_reph (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._precomputed_static_static) (bytes (hs_ss (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._preshared_key) (bytes (hs_psk (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._hash) (bytes (hs_hash (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._chaining_key) (bytes (hs_ck (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._latest_timestamp) (bytes (hs_ts (p_hs P))) q *
    @field_at Noise.CS sh t_peer (DOT I._handshake DOT I._remote_index) (Vint (hs_rindex (p_hs P))) q *
    @field_at_ Noise.CS sh t_peer (DOT I._handshake DOT I._lock) q *
    @field_at_ Noise.CS sh t_peer (DOT I._last_sent_handshake) q *
    @field_at_ Noise.CS sh t_peer (DOT I._latest_cookie) q *
    @field_at Noise.CS sh t_peer (DOT I._refcount) (Vint (p_refs P)) q *
    @field_at_ Noise.CS sh t_peer (DOT I._internal_id) q *
    @field_at_ Noise.CS sh t_peer (DOT I._pubkey_next) q *
    spacer sh 9 16 q * spacer sh (OFS_PEER_KEYPAIRS + 28) (OFS_PEER_KEYPAIRS + 32) q *
    spacer sh (OFS_PEER_HANDSHAKE + 36) (OFS_PEER_HANDSHAKE + 40) q *
    spacer sh (OFS_PEER_HANDSHAKE + 300) (OFS_PEER_HANDSHAKE + 304) q * spacer sh 476 480 q).
  { intros FC HOK. unfold hsp_srest.
    rewrite <- (hsp_hs_fields sh (hs_addr q) (p_hs P) HOK).
    rewrite <- (@field_at_change_composite Noise.CS CSh _ sh t_hs (DOT H._entry) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CSh _ sh t_peer (DOT H._keypairs DOT H._current_keypair) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CSh _ sh t_peer (DOT H._keypairs DOT H._previous_keypair) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CSh _ sh t_peer (DOT H._keypairs DOT H._next_keypair) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CSh _ sh t_peer (DOT H._refcount) _ _ (JMeq_refl _)) by reflexivity.
    hsp_rr I._entry. hsp_rr I._state. hsp_rr I._last_initiation_consumption. hsp_rr I._static_identity.
    hsp_rr I._ephemeral_private. hsp_rr I._remote_static. hsp_rr I._remote_ephemeral.
    hsp_rr I._precomputed_static_static. hsp_rr I._preshared_key. hsp_rr I._hash. hsp_rr I._chaining_key.
    hsp_rr I._latest_timestamp. hsp_rr I._remote_index.
    rewrite !(@field_at_data_at Noise.CS sh t_hs).
    simpl nested_field_type.
    apply pred_ext; cancel. }
  unfold snap_rep. apply pred_ext.
  - Intros. rename H into FC0. assert (HOK: hs_ok (p_hs P)) by (unfold hs_ok; tauto).
    rewrite <- BODY by auto. entailer!. apply hsp_fc; auto.
  - Intros. rename H into FC. assert (HOK: hs_ok (p_hs P)) by (unfold hs_ok; tauto).
    assert (FC0: @field_compatible Noise.CS t_peer [] q) by (apply hsp_fc; auto).
    rewrite BODY by auto. entailer!.
Qed.

(* valid pointers for the comparisons: the peer, the static identity *)
Lemma hsp_vp_peer sh p P R :
  readable_share sh -> hsp_prest sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold hsp_prest.
  do 10 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hsp_fch p : field_compatible t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC.
  assert (FC1: field_compatible t_peer (DOT H._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

Lemma hsp_eqb_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hsp_vp_sid sh a ID R :
  readable_share sh -> identity_rep sh a ID * R |-- valid_pointer a.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold identity_rep. Intros lk.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

End SamePeer.

(* Tactics of the proof of same_peer.  Every comparison of the && chain is between equal values, so each
   forward_if has the postcondition "the temporary is 1"; its else branch is unreachable (hsp_contra). *)

(* the comparison of the peer pointer: valid by hsp_prest *)
Local Ltac hsp_vp_p :=
  match goal with |- context [hsp_prest ?s ?x ?Q] =>
    apply denote_tc_test_eq_split;
    (apply (derives_trans _ (hsp_prest s x Q * TT)%logic); [cancel | apply hsp_vp_peer; auto]) end.

(* the else branch of a test of a temporary known to be 1 *)
Local Ltac hsp_contra := exfalso; match goal with H: Int.one = Int.zero |- _ => discriminate H end.
(* the temporary of an equality test of equal values is 1 *)
Local Ltac hsp_fin :=
  entailer!; try (rewrite ?Int.eq_true, ?Int64.eq_true; reflexivity);
  try match goal with |- context [Val.of_bool ?b] => destruct b; reflexivity end;
  try match goal with |- context [eq_dec ?x ?x] => destruct (eq_dec x x); [reflexivity | congruence] end.
(* the comparison of the static identity pointers: valid by identity_rep *)
Local Ltac hsp_vp_sid_tac :=
  match goal with |- context [identity_rep ?s ?x ?I] =>
    apply denote_tc_test_eq_split;
    (apply (derives_trans _ (identity_rep s x I * TT)%logic); [cancel | apply hsp_vp_sid; auto]) end.
(* the arguments of a bytes_eq call: the arrays' addresses and lengths *)
Local Ltac hsp_args :=
  entailer!; simpl;
  repeat match goal with Hz: Zlength _ = _ |- _ => rewrite Hz end;
  rewrite ?field_address_offset by auto with field_compatible; try reflexivity.

(* same_peer's body in the context of its only callee, bytes_eq *)
Lemma hs_body_same_peer_ctx :
  @semax_body hs_Vh Ghs_same_peer CSh H.f_same_peer same_peer_spec.
Proof.
  start_function.
  rename H into EP.
  rewrite hsp_peer_eq, hsp_snap_eq. Intros lk.
  rewrite hsp_entry_eq by auto.
  unfold hsp_hs, entry_val. rewrite EP, H0, H1, H2. repeat flatten_sepcon_in_SEP.
  assert (Pp: isptr p) by (destruct H; auto).
  forward. forward.
  forward. forward.
  forward_if (temp H._t'1 (Vint Int.one)).
  { hsp_vp_p. }
  { forward. forward. forward. entailer!. }
  { congruence. }
  assert (TB: tc_val tbool (Val.of_bool hashed)) by (destruct hashed; hnf; auto).
  pose proof H3 as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  pose proof (hsp_fch p H) as FHp. pose proof (hsp_fch q H4) as FHq.
  forward_if (temp H._t'2 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'3 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'4 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  assert_PROP (isptr (hs_sid (p_hs P))) as Psid.
  { unfold identity_rep. Intros lk'. entailer!. }
  forward_if (temp H._t'5 (Vint Int.one)).
  { forward. forward. forward.
    { entailer!. hsp_vp_sid_tac. }
    hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'6 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'7 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'8 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'9 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._ephemeral_private) (hs_addr p), hs_eph (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._ephemeral_private) (hs_addr q), hs_eph (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'11 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._remote_static) (hs_addr p), hs_rstatic (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._remote_static) (hs_addr q), hs_rstatic (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'13 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._remote_ephemeral) (hs_addr p), hs_reph (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._remote_ephemeral) (hs_addr q), hs_reph (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'15 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._hash) (hs_addr p), hs_hash (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._hash) (hs_addr q), hs_hash (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'17 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._precomputed_static_static) (hs_addr p), hs_ss (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._precomputed_static_static) (hs_addr q), hs_ss (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'19 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._preshared_key) (hs_addr p), hs_psk (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._preshared_key) (hs_addr q), hs_psk (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'21 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._chaining_key) (hs_addr p), hs_ck (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._chaining_key) (hs_addr q), hs_ck (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'23 (Vint Int.one)).
  { forward_call (shp, @field_address CSh t_hs (DOT H._latest_timestamp) (hs_addr p), hs_ts (p_hs P),
                  shq, @field_address CSh t_hs (DOT H._latest_timestamp) (hs_addr q), hs_ts (p_hs P)).
    { hsp_args. }
    forward. rewrite hsp_eqb_refl. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'25 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'26 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'27 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward_if (temp H._t'28 (Vint Int.one)).
  { forward. forward. forward. hsp_fin. }
  { hsp_contra. }
  forward.
  Exists Int.one.
  rewrite hsp_peer_eq, hsp_snap_eq, hsp_entry_eq by auto. unfold hsp_hs, entry_val. rewrite H0, H1, H2.
  Exists lk. entailer!.
Qed.

Theorem hs_common_bodies : forall x25519, x25519_props x25519 -> hs_helpers_ok x25519.
Proof.
  intros x25519 _. unfold hs_helpers_ok.
  destruct hs_body_small_ctx as (B1 & B2 & B3).
  exact (conj B1 (conj B2 (conj B3 (conj (hs_body_new_device_ctx x25519) (conj (hs_body_new_peer_ctx x25519)
          (conj (hs_body_new_pair_ctx x25519) (conj hs_body_copy_peer_ctx hs_body_same_peer_ctx))))))).
Qed.
