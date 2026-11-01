(* Body proofs of the protocol piece, group cookie_make.
   Target: prot4_ck_bodies_make.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot4 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.blake2s.model WgNoise.proof.blake2s.spec WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section CookieMake.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Cookie.CS.
Local Open Scope logic.
#[local] Instance prot4_ck_make_CCE_b2s_cookie : change_composite_env Blake2s.CS Cookie.CS.
Proof. make_cs_preserve Blake2s.CS Cookie.CS. Defined.
#[local] Instance prot4_ck_make_CCE_cookie_b2s : change_composite_env Cookie.CS Blake2s.CS.
Proof. make_cs_preserve Cookie.CS Blake2s.CS. Defined.

Lemma prot4_ck_make_blake2s_len key outlen msg :
  0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros. unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. lia.
Qed.

Definition prot4_ck_make_ccval (CC: checker) (lk: val) : reptype t_cc :=
  (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC), (Vlong (cc_birth CC), (lk, cc_dev CC))))).

Lemma prot4_ck_make_b2s sh bs p n :
  Zlength bs = n -> n <> 0 -> @data_at Cookie.CS sh (tarray tuchar n) (bytes bs) p = b2s_bytes sh bs p.
Proof.
  intros; subst n. rewrite b2s_bytes_nonempty by auto.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma prot4_ck_make_skb_eq sh s p :
  field_compatible t_skb [] p ->
  @data_at Cookie.CS sh t_skb (skb_val s) p =
  field_at sh t_skb (DOT C._data) (sk_data s) p * field_at sh t_skb (DOT C._len) (Vint (sk_len s)) p *
  field_at sh t_skb (DOT C._protocol) (Vint (Int.repr (sk_proto s))) p *
  data_at sh (tarray tuchar 4) (bytes (sk_ip4 s)) (field_address t_skb (DOT C._ip4 DOT C._saddr DOT C._s_addr) p) *
  data_at sh (tarray tuchar 16) (bytes (sk_ip6 s)) (field_address t_skb (DOT C._ip6 DOT C._saddr DOT C._s6_addr) p) *
  data_at sh (tarray tuchar 2) (bytes (sk_port s)) (field_address t_skb (DOT C._udp DOT C._source) p) *
  spacer sh 36 40 p.
Proof.
  intros FC. unfold skb_val.
  unfold_data_at (data_at sh t_skb _ p).
  unfold_field_at 4%nat. unfold_field_at 4%nat.
  unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at sh t_skb (DOT C._ip4 DOT C._saddr DOT C._s_addr)).
  rewrite (field_at_data_at sh t_skb (DOT C._ip6 DOT C._saddr DOT C._s6_addr)).
  rewrite (field_at_data_at sh t_skb (DOT C._udp DOT C._source)).
  apply pred_ext; cancel.
Qed.

Lemma prot4_ck_make_cc_fold sh c CC lk :
  cc_ok CC ->
  b2s_bytes sh (cc_secret CC) (field_address t_cc (DOT C._secret) c) *
  field_at sh t_cc (DOT C._cookie_encryption_key) (bytes (cc_ekey CC)) c *
  field_at sh t_cc (DOT C._message_mac1_key) (bytes (cc_mkey CC)) c *
  field_at sh t_cc (DOT C._secret_birthdate) (Vlong (cc_birth CC)) c *
  field_at sh t_cc (DOT C._secret_lock) lk c * spacer sh 108 112 c *
  field_at sh t_cc (DOT C._device) (cc_dev CC) c
  |-- checker_rep sh c CC.
Proof.
  intros Hcc. unfold checker_rep. Exists lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at sh t_cc _ c).
  rewrite (field_at_data_at sh t_cc (DOT C._secret)).
  change (nested_field_type t_cc (DOT C._secret)) with (tarray tuchar 32).
  rewrite <- (prot4_ck_make_b2s sh (cc_secret CC) _ 32) by (destruct Hcc; lia).
  entailer!.
Qed.

Lemma prot4_ck_make_skb_fold sh s p :
  skb_ok s -> field_compatible t_skb [] p ->
  field_at sh t_skb (DOT C._data) (sk_data s) p * field_at sh t_skb (DOT C._len) (Vint (sk_len s)) p *
  field_at sh t_skb (DOT C._protocol) (Vint (Int.repr (sk_proto s))) p *
  b2s_bytes sh (sk_ip4 s) (field_address t_skb (DOT C._ip4 DOT C._saddr DOT C._s_addr) p) *
  b2s_bytes sh (sk_ip6 s) (field_address t_skb (DOT C._ip6 DOT C._saddr DOT C._s6_addr) p) *
  b2s_bytes sh (sk_port s) (field_address t_skb (DOT C._udp DOT C._source) p) *
  spacer sh 36 40 p
  |-- skb_rep sh p s.
Proof.
  intros Hs FC. unfold skb_rep. rewrite (prot4_ck_make_skb_eq sh s p FC).
  destruct Hs as (Hp & H4 & H6 & H2).
  rewrite <- (prot4_ck_make_b2s sh (sk_ip4 s) _ 4) by (auto; lia).
  rewrite <- (prot4_ck_make_b2s sh (sk_ip6 s) _ 16) by (auto; lia).
  rewrite <- (prot4_ck_make_b2s sh (sk_port s) _ 2) by (auto; lia).
  entailer!. unfold skb_ok; auto.
Qed.

Lemma prot4_ck_make_out_fold sh o dig :
  Zlength dig = 16 ->
  @data_at Blake2s.CS sh (tarray tuchar 16) (map Vubyte dig) o |-- bytes_at sh dig o.
Proof.
  intros Hd. unfold bytes_at. rewrite Hd.
  erewrite (@data_at_change_composite Blake2s.CS Cookie.CS _ sh (tarray tuchar 16)); [| apply JMeq_refl | reflexivity].
  erewrite (@data_at_change_composite Cookie.CS Noise.CS _ sh (tarray tuchar 16)); [| apply JMeq_refl | reflexivity].
  apply derives_refl.
Qed.

Definition prot4_ck_make_eq {A: Type} (a b: A) : Prop := a = b.

Definition prot4_ck_make_addr (s: skb) : list byte :=
  if Z.eq_dec (sk_proto s) PROTO_IP then sk_ip4 s
  else if Z.eq_dec (sk_proto s) PROTO_IPV6 then sk_ip6 s else [].

Definition prot4_ck_make_G := Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS.

Lemma prot4_ck_make_body_make_cookie :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_make_G Cookie.CS
      WgNoise.cookie.code.f_make_cookie make_cookie_spec.
Proof.
start_function.
unfold checker_rep, skb_rep. Intros lk.
erewrite (@data_at_change_composite Noise.CS Cookie.CS _ shc t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
forward.
forward_call (gv, S, w, cc_birth CC, Int64.repr 120).
forward_if (EX r: list byte,
  PROP (Zlength r = 32)
  LOCAL (lvar C._blake (Tstruct C._blake2s_ctx noattr) v_blake; gvars gv; temp C._cookie__1 o;
         temp C._skb sp; temp C._checker c)
  SEP (shim_state4 gv (if checker_rotates CC (s_boot S) then shim_draw S r else S) w;
       data_at_ Tsh (Tstruct C._blake2s_ctx noattr) v_blake;
       data_at_ sho (tarray tuchar 16) o; data_at shs t_skb (skb_val s) sp;
       data_at shc t_cc (prot4_ck_make_ccval (checker_rotate CC (s_boot S) r) lk) c;
       wg_consts gv)).
{ (* rotation *)
  forward_call (gv, S, w).
  forward.
  assert_PROP (field_compatible t_cc (DOT C._secret) c) as FCs by entailer!.
  unfold_data_at (data_at shc t_cc _ c).
  rewrite (field_at_data_at shc t_cc (DOT C._secret)).
  sep_apply (data_at_data_at_ shc (nested_field_type t_cc (DOT C._secret)) (bytes (cc_secret CC))
               (field_address t_cc (DOT C._secret) c)).
  forward_call (gv, S, w, shc, field_address t_cc (DOT C._secret) c, 32).
  { entailer!. simpl. rewrite field_address_offset by auto. reflexivity. }
  Intros bs.
  Exists bs.
  assert (Hexp: birthdate_expired (cc_birth CC) (Int64.repr 120) (s_boot S) = true)
    by (destruct (birthdate_expired _ _ _); [reflexivity | compute in H1; discriminate]).
  unfold checker_rotates, checker_rotate. rewrite Hexp.
  unfold prot4_ck_make_ccval; cbn [cc_secret cc_ekey cc_mkey cc_birth cc_dev].
  unfold_data_at (data_at shc t_cc _ c).
  rewrite (field_at_data_at shc t_cc (DOT C._secret)).
  unfold bytes_at. rewrite H2.
  change (nested_field_type t_cc (DOT C._secret)) with (tarray tuchar 32).
  entailer!.
}
{ (* no rotation *)
  forward.
  Exists (Zrepeat Byte.zero 32).
  assert (Hexp: birthdate_expired (cc_birth CC) (Int64.repr 120) (s_boot S) = false)
    by (destruct (birthdate_expired _ _ _); [compute in H1; discriminate | reflexivity]).
  unfold checker_rotates, checker_rotate. rewrite Hexp.
  unfold prot4_ck_make_ccval.
  entailer!.
}
Intros r.
assert (Hcc1: cc_ok (checker_rotate CC (s_boot S) r))
  by (unfold checker_rotate; destruct (birthdate_expired _ _ _); [unfold cc_ok in *; simpl; tauto | auto]).
remember (checker_rotate CC (s_boot S) r) as CC1 eqn:ECC1.
change (prot4_ck_make_eq CC1 (checker_rotate CC (s_boot S) r)) in ECC1.
unfold prot4_ck_make_ccval.
assert_PROP (field_compatible t_cc (DOT C._secret) c) as FCs by entailer!.
unfold_data_at (data_at shc t_cc _ c).
rewrite (field_at_data_at shc t_cc (DOT C._secret)).
change (nested_field_type t_cc (DOT C._secret)) with (tarray tuchar 32).
rewrite (prot4_ck_make_b2s shc (cc_secret CC1) _ 32) by (destruct Hcc1; lia).
erewrite (@data_at__change_composite Cookie.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_blake, 16, shc, field_address t_cc (DOT C._secret) c, cc_secret CC1).
{ destruct Hcc1 as [Hs _]. rewrite Hs. entailer!. simpl. rewrite field_address_offset by auto. reflexivity. }
{ destruct Hcc1; lia. }
assert_PROP (field_compatible t_skb [] sp) as FCskb by entailer!.
rewrite (prot4_ck_make_skb_eq shs s sp FCskb).
destruct H as (Hproto & Hl4 & Hl6 & Hl2).
rewrite (prot4_ck_make_b2s shs (sk_ip4 s) _ 4) by (auto; lia).
rewrite (prot4_ck_make_b2s shs (sk_ip6 s) _ 16) by (auto; lia).
rewrite (prot4_ck_make_b2s shs (sk_port s) _ 2) by (auto; lia).
Intros. forward_call 2048.
replace (swab16 2048) with PROTO_IP by reflexivity.
forward.
{ entailer!. lia. }
forward_if (PROP ()
  LOCAL (lvar C._blake (Tstruct C._blake2s_ctx noattr) v_blake; gvars gv; temp C._cookie__1 o;
         temp C._skb sp; temp C._checker c)
  SEP (blake2s_state Tsh (cc_secret CC1) 16 (prot4_ck_make_addr s) v_blake;
       b2s_bytes shc (cc_secret CC1) (field_address t_cc (DOT C._secret) c);
       shim_state4 gv (if checker_rotates CC (s_boot S) then shim_draw S r else S) w;
       data_at_ sho (tarray tuchar 16) o;
       field_at shs t_skb (DOT C._data) (sk_data s) sp;
       field_at shs t_skb (DOT C._len) (Vint (sk_len s)) sp;
       field_at shs t_skb (DOT C._protocol) (Vint (Int.repr (sk_proto s))) sp;
       b2s_bytes shs (sk_ip4 s) (field_address t_skb (DOT C._ip4 DOT C._saddr DOT C._s_addr) sp);
       b2s_bytes shs (sk_ip6 s) (field_address t_skb (DOT C._ip6 DOT C._saddr DOT C._s6_addr) sp);
       b2s_bytes shs (sk_port s) (field_address t_skb (DOT C._udp DOT C._source) sp);
       spacer shs 36 40 sp;
       field_at shc t_cc (DOT C._cookie_encryption_key) (bytes (cc_ekey CC1)) c;
       field_at shc t_cc (DOT C._message_mac1_key) (bytes (cc_mkey CC1)) c;
       field_at shc t_cc (DOT C._secret_birthdate) (Vlong (cc_birth CC1)) c;
       field_at shc t_cc (DOT C._secret_lock) lk c;
       spacer shc 108 112 c;
       field_at shc t_cc (DOT C._device) (cc_dev CC1) c;
       wg_consts gv)).
{ (* IPv4 *)
  unfold wg_consts; Intros.
  forward_call (Tsh, v_blake, cc_secret CC1, 16, @nil byte, shs,
                field_address t_skb (DOT C._ip4 DOT C._saddr DOT C._s_addr) sp, sk_ip4 s, gv).
  { entailer!. rewrite Hl4. simpl. rewrite field_address_offset by auto with field_compatible. simpl.
    rewrite offset_offset_val. reflexivity. }
  assert (Hp: sk_proto s = PROTO_IP)
    by (apply repr_inj_unsigned; [rep_lia | unfold PROTO_IP; rep_lia | exact H]).
  replace (prot4_ck_make_addr s) with ([] ++ sk_ip4 s)
    by (unfold prot4_ck_make_addr; rewrite if_true by auto; reflexivity).
  unfold wg_consts. entailer!.
}
{ (* not IPv4 *)
  assert (Hn4: sk_proto s <> PROTO_IP) by (intro E; apply H; rewrite E; reflexivity).
  forward_call 34525.
  replace (swab16 34525) with PROTO_IPV6 by reflexivity.
  forward.
  forward_if.
  { (* IPv6 *)
    unfold wg_consts; Intros.
    forward_call (Tsh, v_blake, cc_secret CC1, 16, @nil byte, shs,
                  field_address t_skb (DOT C._ip6 DOT C._saddr DOT C._s6_addr) sp, sk_ip6 s, gv).
    { entailer!. rewrite Hl6. simpl. rewrite field_address_offset by auto with field_compatible. simpl.
      rewrite offset_offset_val. reflexivity. }
    assert (Hp: sk_proto s = PROTO_IPV6)
      by (apply repr_inj_unsigned; [rep_lia | unfold PROTO_IPV6; rep_lia | assumption]).
    replace (prot4_ck_make_addr s) with ([] ++ sk_ip6 s)
      by (unfold prot4_ck_make_addr; rewrite if_false by auto; rewrite if_true by auto; reflexivity).
    unfold wg_consts. entailer!.
  }
  { (* other *)
    assert (Hn6: sk_proto s <> PROTO_IPV6)
      by (intro E; match goal with Hx: Int.repr (sk_proto s) <> Int.repr PROTO_IPV6 |- _ => apply Hx end;
          rewrite E; reflexivity).
    forward.
    replace (prot4_ck_make_addr s) with (@nil byte)
      by (unfold prot4_ck_make_addr; rewrite !if_false by auto; reflexivity).
    entailer!.
  }
}
unfold wg_consts; Intros.
forward_call (Tsh, v_blake, cc_secret CC1, 16, prot4_ck_make_addr s, shs,
              field_address t_skb (DOT C._udp DOT C._source) sp, sk_port s, gv).
{ entailer!. rewrite Hl2. simpl. rewrite field_address_offset by auto with field_compatible. simpl.
  try rewrite offset_offset_val. reflexivity. }
change (prot4_ck_make_addr s ++ sk_port s) with (skb_source s).
erewrite (@data_at__change_composite Cookie.CS Blake2s.CS _ sho (tarray tuchar 16)); [| reflexivity].
forward_call (Tsh, v_blake, cc_secret CC1, 16, skb_source s, sho, o, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
erewrite (@data_at__change_composite Blake2s.CS Cookie.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
remember (blake2s (cc_secret CC1) 16 (skb_source s)) as dig eqn:Edig.
assert (Hdig: Zlength dig = 16) by (subst dig; apply prot4_ck_make_blake2s_len; lia).
change (prot4_ck_make_eq dig (blake2s (cc_secret CC1) 16 (skb_source s))) in Edig.
Exists r.
unfold prot4_ck_make_eq in ECC1, Edig. rewrite <- ECC1.
unfold cookie_of, MAC. rewrite <- Edig.
sep_apply (prot4_ck_make_out_fold sho o dig Hdig).
sep_apply (prot4_ck_make_cc_fold shc c CC1 lk Hcc1).
sep_apply (prot4_ck_make_skb_fold shs s sp); [unfold skb_ok; auto |].
unfold wg_consts.
entailer!.
Qed.

Lemma prot4_ck_make_split sh (l: list byte) k m d :
  0 <= k <= Zlength l -> Zlength l - k = m -> field_compatible (tarray tuchar (Zlength l)) [] d ->
  @data_at Cookie.CS sh (tarray tuchar (Zlength l)) (bytes l) d =
  b2s_bytes sh (sublist 0 k l) d *
  @data_at Cookie.CS sh (tarray tuchar m) (bytes (sublist k (Zlength l) l)) (offset_val k d).
Proof.
  intros Hk Hm FC. subst m.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength l) k) by (try (unfold bytes; rewrite Zlength_map); lia).
  replace (field_address0 (Tarray tuchar (Zlength l) noattr) (SUB k) d) with (offset_val k d).
  2:{ rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]). simpl. f_equal. lia. }
  unfold bytes. rewrite !sublist_map.
  destruct (Z.eq_dec k 0) as [->|Hk0].
  - rewrite sublist_nil. rewrite b2s_bytes_nil.
    rewrite (data_at_zero_array_eq sh tuchar) by (auto; apply field_compatible_isptr in FC; auto).
    reflexivity.
  - rewrite <- (prot4_ck_make_b2s sh (sublist 0 k l) d k) by (try rewrite Zlength_sublist; lia).
    reflexivity.
Qed.

Lemma prot4_ck_make_ba sh (l: list byte) p :
  bytes_at sh l p = @data_at Cookie.CS sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. unfold bytes_at. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot4_ck_make_msg2 sh msg d :
  16 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] d ->
  bytes_at sh msg d =
  b2s_bytes sh (sublist 0 (Zlength msg - 16) msg) d *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
    (offset_val (Zlength msg - 16) d).
Proof.
  intros Hn FC. rewrite prot4_ck_make_ba.
  apply (prot4_ck_make_split sh msg (Zlength msg - 16) 16 d); auto; lia.
Qed.

Lemma prot4_ck_make_msg3 sh msg d :
  32 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] d ->
  bytes_at sh msg d =
  b2s_bytes sh (sublist 0 (Zlength msg - 32) msg) d *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 32) (Zlength msg - 16) msg))
    (offset_val (Zlength msg - 32) d) *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
    (offset_val (Zlength msg - 16) d).
Proof.
  intros Hn FC. rewrite prot4_ck_make_ba.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength msg) (Zlength msg - 32) (Zlength msg - 16))
    by (try rewrite Zlength_map; lia).
  replace (field_address0 (Tarray tuchar (Zlength msg) noattr) (SUB (Zlength msg - 32)) d)
    with (offset_val (Zlength msg - 32) d).
  2:{ rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]). simpl. f_equal. lia. }
  replace (field_address0 (Tarray tuchar (Zlength msg) noattr) (SUB (Zlength msg - 16)) d)
    with (offset_val (Zlength msg - 16) d).
  2:{ rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]). simpl. f_equal. lia. }
  replace (Zlength msg - 16 - (Zlength msg - 32)) with 16 by lia.
  replace (Zlength msg - (Zlength msg - 16)) with 16 by lia.
  rewrite !sublist_map.
  f_equal. f_equal.
  destruct (Z.eq_dec (Zlength msg - 32) 0) as [E|E].
  - rewrite E, sublist_nil, b2s_bytes_nil.
    apply (data_at_zero_array_eq sh tuchar); try reflexivity; try (eapply field_compatible_isptr; eauto); auto.
  - rewrite <- (prot4_ck_make_b2s sh (sublist 0 (Zlength msg - 32) msg) d (Zlength msg - 32))
      by (try rewrite Zlength_sublist; lia).
    reflexivity.
Qed.

Lemma prot4_ck_make_cc_mkey sh c CC :
  checker_rep sh c CC |--
  bytes_at sh (cc_mkey CC) (field_address t_cc (DOT C._message_mac1_key) c) *
  (bytes_at sh (cc_mkey CC) (field_address t_cc (DOT C._message_mac1_key) c) -* checker_rep sh c CC).
Proof.
  unfold checker_rep at 1. Intros lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at sh t_cc _ c).
  rewrite (field_at_data_at sh t_cc (DOT C._message_mac1_key)).
  change (nested_field_type t_cc (DOT C._message_mac1_key)) with (tarray tuchar 32).
  assert (E: @data_at Cookie.CS sh (tarray tuchar 32) (bytes (cc_mkey CC))
               (field_address t_cc (DOT C._message_mac1_key) c) =
             bytes_at sh (cc_mkey CC) (field_address t_cc (DOT C._message_mac1_key) c)).
  { unfold bytes_at. destruct H as (_ & _ & Hm). rewrite Hm.
    apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. }
  rewrite E.
  cancel.
  apply -> wand_sepcon_adjoint.
  unfold checker_rep. Exists lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at sh t_cc _ c).
  rewrite (field_at_data_at sh t_cc (DOT C._message_mac1_key)).
  change (nested_field_type t_cc (DOT C._message_mac1_key)) with (tarray tuchar 32).
  rewrite E.
  entailer!.
Qed.

Lemma prot4_ck_make_memneq a b : memneq_bool a b = negb (bytes_eqb a b).
Proof. unfold memneq_bool, bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b); reflexivity. Qed.

Lemma prot4_ck_make_vm_mac1 CC s msg chk now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = false ->
  validate_model CC s msg chk now rl r = (INVALID_MAC, CC) /\ validate_rotates CC msg chk now = false.
Proof. intros E. unfold validate_model, validate_rotates. rewrite E. auto. Qed.

Lemma prot4_ck_make_vm_nochk CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  validate_model CC s msg false now rl r = (VALID_MAC_BUT_NO_COOKIE, CC) /\
  validate_rotates CC msg false now = false.
Proof. intros E. unfold validate_model, validate_rotates. rewrite E. auto. Qed.

Lemma prot4_ck_make_vm_mac2 CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC now r)) s) msg)
            (sublist (Zlength msg - 16) (Zlength msg) msg) = false ->
  validate_model CC s msg true now rl r = (VALID_MAC_BUT_NO_COOKIE, checker_rotate CC now r) /\
  validate_rotates CC msg true now = checker_rotates CC now.
Proof. intros E1 E2. unfold validate_model, validate_rotates. rewrite E1, E2. auto. Qed.

Lemma prot4_ck_make_vm_rl CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC now r)) s) msg)
            (sublist (Zlength msg - 16) (Zlength msg) msg) = true ->
  validate_model CC s msg true now rl r =
    (if rl then VALID_MAC_WITH_COOKIE else VALID_MAC_WITH_COOKIE_BUT_RATELIMITED, checker_rotate CC now r) /\
  validate_rotates CC msg true now = checker_rotates CC now.
Proof. intros E1 E2. unfold validate_model, validate_rotates. rewrite E1, E2. destruct rl; auto. Qed.

Lemma prot4_ck_make_skb_intro sh p s :
  skb_ok s -> @data_at Cookie.CS sh t_skb (skb_val s) p |-- skb_rep sh p s.
Proof. intros. unfold skb_rep. entailer!. Qed.

Lemma prot4_ck_make_msg3_fold sh msg d :
  32 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] d ->
  b2s_bytes sh (sublist 0 (Zlength msg - 32) msg) d *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 32) (Zlength msg - 16) msg))
    (offset_val (Zlength msg - 32) d) *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
    (offset_val (Zlength msg - 16) d)
  |-- bytes_at sh msg d.
Proof. intros. rewrite (prot4_ck_make_msg3 sh msg d) by auto. apply derives_refl. Qed.

Lemma prot4_ck_make_rlallow (S: shim) (b: bool) (r: list byte) : s_rlallow (if b then shim_draw S r else S) = s_rlallow S.
Proof. destruct b; reflexivity. Qed.

Lemma prot4_ck_make_ba_ sh (l: list byte) p :
  bytes_at sh l p |-- @data_at_ Cookie.CS sh (tarray tuchar (Zlength l)) p.
Proof. rewrite prot4_ck_make_ba. apply data_at_data_at_. Qed.

Lemma prot4_ck_make_cc_lf sh c CC :
  checker_rep sh c CC |-- !! (cc_ok CC /\ field_compatible t_cc [] c).
Proof.
  unfold checker_rep. Intros lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

Ltac prot4_ck_make_contra :=
  first [ apply Int.one_not_zero; assumption
        | match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end
        | match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end
        | match goal with Hx: Int.zero <> Int.zero |- _ => apply Hx; reflexivity end ].

Lemma prot4_ck_make_body_validate :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_make_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_validate_packet wg_cookie_validate_packet_spec.
Proof.
start_function.
unfold skb_rep. Intros.
assert_PROP (field_compatible (tarray tuchar (Zlength msg)) [] (sk_data s)) as FCm
  by (rewrite prot4_ck_make_ba; entailer!).
assert_PROP (cc_ok CC /\ field_compatible t_cc [] c) as HccF
  by (sep_apply (prot4_ck_make_cc_lf shc c CC); entailer!).
destruct HccF as [Hcc FCc].
unfold skb_val. forward. forward. forward.
{ entailer!. apply field_compatible_isptr in FCm. destruct (sk_data s); try contradiction; simpl; auto. }
match goal with |- context [temp C._macs ?v] => assert (Hm: v = offset_val (Zlength msg - 32) (sk_data s)) end.
{ pose proof (field_compatible_isptr _ _ _ FCm) as Hp. destruct (sk_data s); try contradiction. simpl.
  f_equal.
  rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  replace (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 32))) with (Ptrofs.repr 32) by reflexivity.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite <- H0.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr. f_equal; f_equal; lia. }
rewrite Hm. clear Hm.
match goal with |- semax _ ?P _ _ =>
forward_loop P
  continue: (EX r: list byte,
    PROP (Zlength r = 32)
    LOCAL (temp C._ret (Vint (Int.repr (fst (validate_model CC s msg chk (s_boot S) (s_rlallow S) r))));
           lvar C._cookie__1 (tarray tuchar 16) v_cookie__1;
           lvar C._computed_mac (tarray tuchar 16) v_computed_mac)
    SEP (data_at_ Tsh (tarray tuchar 16) v_cookie__1; data_at_ Tsh (tarray tuchar 16) v_computed_mac;
         checker_rep shc c (snd (validate_model CC s msg chk (s_boot S) (s_rlallow S) r));
         skb_rep shs sp s; bytes_at shm msg (sk_data s);
         shim_state4 gv (if validate_rotates CC msg chk (s_boot S) then shim_draw S r else S) w;
         wg_consts gv))
  break: (EX r: list byte,
    PROP (Zlength r = 32)
    LOCAL (temp C._ret (Vint (Int.repr (fst (validate_model CC s msg chk (s_boot S) (s_rlallow S) r))));
           lvar C._cookie__1 (tarray tuchar 16) v_cookie__1;
           lvar C._computed_mac (tarray tuchar 16) v_computed_mac)
    SEP (data_at_ Tsh (tarray tuchar 16) v_cookie__1; data_at_ Tsh (tarray tuchar 16) v_computed_mac;
         checker_rep shc c (snd (validate_model CC s msg chk (s_boot S) (s_rlallow S) r));
         skb_rep shs sp s; bytes_at shm msg (sk_data s);
         shim_state4 gv (if validate_rotates CC msg chk (s_boot S) then shim_draw S r else S) w;
         wg_consts gv))
end.
{ apply ENTAIL_refl. }
2:{ Intros r. forward. Exists r. entailer!. }
2:{ Intros r. forward. Exists r. entailer!. }
(* the body *)
forward. forward. forward.
sep_apply (prot4_ck_make_cc_mkey shc c CC).
rewrite (prot4_ck_make_msg3 shm msg (sk_data s)) by auto.
rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ Tsh (tarray tuchar 16) v_computed_mac) by reflexivity.
Intros.
forward_call (gv, Tsh, v_computed_mac, shm, sk_data s, sublist 0 (Zlength msg - 32) msg, shc,
              field_address t_cc (DOT C._message_mac1_key) c, cc_mkey CC).
{ entailer!. rewrite Zlength_sublist by lia. simpl. rewrite field_address_offset by auto with field_compatible.
  rewrite H0. replace (Int.unsigned (sk_len s) - 32 - 0 + 32) with (Int.unsigned (sk_len s)) by lia. reflexivity. }
{ destruct Hcc as (_ & _ & Hk). split; [exact Hk |]. rewrite Zlength_sublist by lia.
  pose proof (Int.unsigned_range (sk_len s)). rep_lia. }
sep_apply (modus_ponens_wand (bytes_at shc (cc_mkey CC) (field_address t_cc (DOT C._message_mac1_key) c))
                             (checker_rep shc c CC)).
remember (MAC (cc_mkey CC) (sublist 0 (Zlength msg - 32) msg)) as m1 eqn:Em1.
assert (Hm1: Zlength m1 = 16) by (subst m1; unfold MAC; apply prot4_ck_make_blake2s_len; lia).
change (prot4_ck_make_eq m1 (MAC (cc_mkey CC) (sublist 0 (Zlength msg - 32) msg))) in Em1.
rewrite (prot4_ck_make_ba Tsh m1 v_computed_mac). rewrite Hm1.
forward_call (Tsh, shm, v_computed_mac, offset_val (Zlength msg - 32) (sk_data s), 16, m1,
              sublist (Zlength msg - 32) (Zlength msg - 16) msg).
{ rewrite Zlength_sublist; lia. }
assert (Emac1: mac1_of (cc_mkey CC) msg = m1) by (unfold prot4_ck_make_eq in Em1; subst m1; reflexivity).
destruct (memneq_bool m1 (sublist (Zlength msg - 32) (Zlength msg - 16) msg)) eqn:Hmn.
{ (* mac1 mismatch *)
  forward_if.
  2:{ exfalso. apply Int.one_not_zero. assumption. }
  forward.
  rewrite prot4_ck_make_memneq in Hmn.
  assert (Hb: bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = false)
    by (rewrite Emac1; destruct (bytes_eqb _ _); simpl in Hmn; congruence).
  destruct (prot4_ck_make_vm_mac1 CC s msg chk (s_boot S) (s_rlallow S) (Zrepeat Byte.zero 32) Hb) as [E1 E2].
  Exists (Zrepeat Byte.zero 32).
  rewrite E1, E2.
  rewrite (prot4_ck_make_msg3 shm msg (sk_data s)) by auto.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte m1) v_computed_mac).
  unfold skb_rep, skb_val. simpl fst; simpl snd.
  entailer!.
}
forward_if.
{ exfalso. apply H2. reflexivity. }
forward.
rewrite prot4_ck_make_memneq in Hmn.
assert (Hb1: bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true)
  by (rewrite Emac1; destruct (bytes_eqb _ _); simpl in Hmn; congruence).
destruct chk.
2:{ (* no cookie check *)
  forward_if.
  2:{ exfalso; prot4_ck_make_contra. }
  forward.
  destruct (prot4_ck_make_vm_nochk CC s msg (s_boot S) (s_rlallow S) (Zrepeat Byte.zero 32) Hb1) as [E1 E2].
  Exists (Zrepeat Byte.zero 32).
  rewrite E1, E2.
  rewrite (prot4_ck_make_msg3 shm msg (sk_data s)) by auto.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte m1) v_computed_mac).
  unfold skb_rep, skb_val. simpl fst; simpl snd.
  entailer!.
}
forward_if.
{ exfalso; prot4_ck_make_contra. }
clear Hmn.
sep_apply (prot4_ck_make_skb_intro shs sp s H1).
rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ Tsh (tarray tuchar 16) v_cookie__1) by reflexivity.
forward_call (gv, S, w, Tsh, v_cookie__1, shs, sp, s, shc, c, CC).
Intros r.
remember (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s) as ck eqn:Eck.
assert (Hck: Zlength ck = 16) by (subst ck; unfold cookie_of, MAC; apply prot4_ck_make_blake2s_len; lia).
change (prot4_ck_make_eq ck (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s)) in Eck.
remember (checker_rotate CC (s_boot S) r) as CC1 eqn:ECC1.
change (prot4_ck_make_eq CC1 (checker_rotate CC (s_boot S) r)) in ECC1.
remember (if checker_rotates CC (s_boot S) then shim_draw S r else S) as S1 eqn:ES1.
change (prot4_ck_make_eq S1 (if checker_rotates CC (s_boot S) then shim_draw S r else S)) in ES1.
unfold skb_rep, skb_val. Intros.
forward. forward.
sep_apply (prot4_ck_make_msg3_fold shm msg (sk_data s) H FCm).
rewrite (prot4_ck_make_msg2 shm msg (sk_data s)) by (auto; lia).
sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte m1) v_computed_mac).
rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ Tsh (tarray tuchar 16) v_computed_mac) by reflexivity.
Intros.
forward_call (gv, Tsh, v_computed_mac, shm, sk_data s, sublist 0 (Zlength msg - 16) msg, Tsh, v_cookie__1, ck).
{ entailer!. rewrite Zlength_sublist by lia.
  replace (Zlength msg - 16 - 0 + 16) with (Zlength msg) by lia. rewrite H0. reflexivity. }
{ rewrite Zlength_sublist by lia. pose proof (Int.unsigned_range (sk_len s)). rep_lia. }
remember (MAC ck (sublist 0 (Zlength msg - 16) msg)) as m2 eqn:Em2.
assert (Hm2: Zlength m2 = 16) by (subst m2; unfold MAC; apply prot4_ck_make_blake2s_len; lia).
change (prot4_ck_make_eq m2 (MAC ck (sublist 0 (Zlength msg - 16) msg))) in Em2.
assert (Emac2: mac2_of (cookie_of (cc_secret CC1) s) msg = m2)
  by (unfold prot4_ck_make_eq in Em2, Eck; subst m2 ck; reflexivity).
rewrite (prot4_ck_make_ba Tsh m2 v_computed_mac). rewrite Hm2.
forward_call (Tsh, shm, v_computed_mac, offset_val (Zlength msg - 16) (sk_data s), 16, m2,
              sublist (Zlength msg - 16) (Zlength msg) msg).
{ entailer!. simpl. rewrite offset_offset_val. replace (Zlength msg - 32 + 16) with (Zlength msg - 16) by lia. reflexivity. }
{ rewrite Zlength_sublist; lia. }
unfold prot4_ck_make_eq in ECC1, ES1.
destruct (memneq_bool m2 (sublist (Zlength msg - 16) (Zlength msg) msg)) eqn:Hmn2;
  rewrite prot4_ck_make_memneq in Hmn2.
{ (* mac2 mismatch *)
  forward_if.
  2:{ exfalso; prot4_ck_make_contra. }
  forward.
  assert (Hb2: bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s) msg)
                 (sublist (Zlength msg - 16) (Zlength msg) msg) = false)
    by (rewrite <- ECC1, Emac2;
        destruct (bytes_eqb m2 (sublist (Zlength msg - 16) (Zlength msg) msg)) eqn:Ex;
        [simpl in Hmn2; discriminate | reflexivity]).
  destruct (prot4_ck_make_vm_mac2 CC s msg (s_boot S) (s_rlallow S) r Hb1 Hb2) as [E1 E2].
  rewrite <- ECC1 in E1.
  Exists r.
  rewrite E1, E2, <- ES1. simpl fst; simpl snd.
  rewrite (prot4_ck_make_msg2 shm msg (sk_data s)) by (auto; lia).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte m2) v_computed_mac).
  sep_apply (prot4_ck_make_ba_ Tsh ck v_cookie__1). rewrite Hck.
  unfold skb_rep, skb_val.
  entailer!.
}
forward_if.
{ exfalso; prot4_ck_make_contra. }
forward.
assert (Hb2: bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s) msg)
               (sublist (Zlength msg - 16) (Zlength msg) msg) = true)
  by (rewrite <- ECC1, Emac2;
      destruct (bytes_eqb m2 (sublist (Zlength msg - 16) (Zlength msg) msg)) eqn:Ex;
      [reflexivity | simpl in Hmn2; discriminate]).
forward_call (gv, S1, w, sp, nullval).
assert (Hrl: s_rlallow S1 = s_rlallow S) by (rewrite ES1; apply prot4_ck_make_rlallow).
rewrite Hrl.
destruct (prot4_ck_make_vm_rl CC s msg (s_boot S) (s_rlallow S) r Hb1 Hb2) as [E1 E2].
rewrite <- ECC1 in E1.
destruct (s_rlallow S) eqn:Hrl'.
{ (* allowed *)
  forward_if.
  { exfalso; prot4_ck_make_contra. }
  forward.
  Exists r.
  rewrite E1, E2, <- ES1. simpl fst; simpl snd.
  rewrite (prot4_ck_make_msg2 shm msg (sk_data s)) by (auto; lia).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte m2) v_computed_mac).
  sep_apply (prot4_ck_make_ba_ Tsh ck v_cookie__1). rewrite Hck.
  unfold skb_rep, skb_val.
  entailer!.
}
{ (* rate limited *)
  forward_if.
  2:{ exfalso; prot4_ck_make_contra. }
  forward.
  Exists r.
  rewrite E1, E2, <- ES1. simpl fst; simpl snd.
  rewrite (prot4_ck_make_msg2 shm msg (sk_data s)) by (auto; lia).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte m2) v_computed_mac).
  sep_apply (prot4_ck_make_ba_ Tsh ck v_cookie__1). rewrite Hck.
  unfold skb_rep, skb_val.
  entailer!.
}
Qed.

End CookieMake.

Theorem prot4_ck_bodies_make :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_make_cookie make_cookie_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_validate_packet wg_cookie_validate_packet_spec).
Proof.
  intros. split.
  - apply prot4_ck_make_body_make_cookie.
  - apply prot4_ck_make_body_validate.
Qed.
