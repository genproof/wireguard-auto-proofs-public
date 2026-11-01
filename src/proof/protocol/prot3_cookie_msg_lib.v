(* Helpers of group cookie_msg: byte-buffer / skb / checker lemmas in Cookie.CS, copied from
   group cookie_make proof with the prefix prot3_cookie_msg_. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.blake2s.model WgNoise.proof.blake2s.spec WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section CookieMsgLib.
#[local] Existing Instance Cookie.CS.
Local Open Scope logic.
#[export] Instance prot3_cookie_msg_CCE_b2s_cookie : change_composite_env Blake2s.CS Cookie.CS.
Proof. make_cs_preserve Blake2s.CS Cookie.CS. Defined.
#[export] Instance prot3_cookie_msg_CCE_cookie_b2s : change_composite_env Cookie.CS Blake2s.CS.
Proof. make_cs_preserve Cookie.CS Blake2s.CS. Defined.
Lemma prot3_cookie_msg_blake2s_len key outlen msg :
  0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros. unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. lia.
Qed.

Definition prot3_cookie_msg_ccval (CC: checker) (lk: val) : reptype t_cc :=
  (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC), (Vlong (cc_birth CC), (lk, cc_dev CC))))).

Lemma prot3_cookie_msg_b2s sh bs p n :
  Zlength bs = n -> n <> 0 -> @data_at Cookie.CS sh (tarray tuchar n) (bytes bs) p = b2s_bytes sh bs p.
Proof.
  intros; subst n. rewrite b2s_bytes_nonempty by auto.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma prot3_cookie_msg_skb_eq sh s p :
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

Lemma prot3_cookie_msg_cc_fold sh c CC lk :
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
  rewrite <- (prot3_cookie_msg_b2s sh (cc_secret CC) _ 32) by (destruct Hcc; lia).
  entailer!.
Qed.

Lemma prot3_cookie_msg_skb_fold sh s p :
  skb_ok s -> field_compatible t_skb [] p ->
  field_at sh t_skb (DOT C._data) (sk_data s) p * field_at sh t_skb (DOT C._len) (Vint (sk_len s)) p *
  field_at sh t_skb (DOT C._protocol) (Vint (Int.repr (sk_proto s))) p *
  b2s_bytes sh (sk_ip4 s) (field_address t_skb (DOT C._ip4 DOT C._saddr DOT C._s_addr) p) *
  b2s_bytes sh (sk_ip6 s) (field_address t_skb (DOT C._ip6 DOT C._saddr DOT C._s6_addr) p) *
  b2s_bytes sh (sk_port s) (field_address t_skb (DOT C._udp DOT C._source) p) *
  spacer sh 36 40 p
  |-- skb_rep sh p s.
Proof.
  intros Hs FC. unfold skb_rep. rewrite (prot3_cookie_msg_skb_eq sh s p FC).
  destruct Hs as (Hp & H4 & H6 & H2).
  rewrite <- (prot3_cookie_msg_b2s sh (sk_ip4 s) _ 4) by (auto; lia).
  rewrite <- (prot3_cookie_msg_b2s sh (sk_ip6 s) _ 16) by (auto; lia).
  rewrite <- (prot3_cookie_msg_b2s sh (sk_port s) _ 2) by (auto; lia).
  entailer!. unfold skb_ok; auto.
Qed.

Lemma prot3_cookie_msg_out_fold sh o dig :
  Zlength dig = 16 ->
  @data_at Blake2s.CS sh (tarray tuchar 16) (map Vubyte dig) o |-- bytes_at sh dig o.
Proof.
  intros Hd. unfold bytes_at. rewrite Hd.
  erewrite (@data_at_change_composite Blake2s.CS Cookie.CS _ sh (tarray tuchar 16)); [| apply JMeq_refl | reflexivity].
  erewrite (@data_at_change_composite Cookie.CS Noise.CS _ sh (tarray tuchar 16)); [| apply JMeq_refl | reflexivity].
  apply derives_refl.
Qed.

Definition prot3_cookie_msg_eq {A: Type} (a b: A) : Prop := a = b.

Definition prot3_cookie_msg_addr (s: skb) : list byte :=
  if Z.eq_dec (sk_proto s) PROTO_IP then sk_ip4 s
  else if Z.eq_dec (sk_proto s) PROTO_IPV6 then sk_ip6 s else [].
Lemma prot3_cookie_msg_split sh (l: list byte) k m d :
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
  - rewrite <- (prot3_cookie_msg_b2s sh (sublist 0 k l) d k) by (try rewrite Zlength_sublist; lia).
    reflexivity.
Qed.

Lemma prot3_cookie_msg_ba sh (l: list byte) p :
  bytes_at sh l p = @data_at Cookie.CS sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. unfold bytes_at. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_cookie_msg_msg2 sh msg d :
  16 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] d ->
  bytes_at sh msg d =
  b2s_bytes sh (sublist 0 (Zlength msg - 16) msg) d *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
    (offset_val (Zlength msg - 16) d).
Proof.
  intros Hn FC. rewrite prot3_cookie_msg_ba.
  apply (prot3_cookie_msg_split sh msg (Zlength msg - 16) 16 d); auto; lia.
Qed.

Lemma prot3_cookie_msg_msg3 sh msg d :
  32 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] d ->
  bytes_at sh msg d =
  b2s_bytes sh (sublist 0 (Zlength msg - 32) msg) d *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 32) (Zlength msg - 16) msg))
    (offset_val (Zlength msg - 32) d) *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
    (offset_val (Zlength msg - 16) d).
Proof.
  intros Hn FC. rewrite prot3_cookie_msg_ba.
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
  - rewrite <- (prot3_cookie_msg_b2s sh (sublist 0 (Zlength msg - 32) msg) d (Zlength msg - 32))
      by (try rewrite Zlength_sublist; lia).
    reflexivity.
Qed.

Lemma prot3_cookie_msg_cc_mkey sh c CC :
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

Lemma prot3_cookie_msg_memneq a b : memneq_bool a b = negb (bytes_eqb a b).
Proof. unfold memneq_bool, bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b); reflexivity. Qed.

Lemma prot3_cookie_msg_vm_mac1 CC s msg chk now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = false ->
  validate_model CC s msg chk now rl r = (INVALID_MAC, CC) /\ validate_rotates CC msg chk now = false.
Proof. intros E. unfold validate_model, validate_rotates. rewrite E. auto. Qed.

Lemma prot3_cookie_msg_vm_nochk CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  validate_model CC s msg false now rl r = (VALID_MAC_BUT_NO_COOKIE, CC) /\
  validate_rotates CC msg false now = false.
Proof. intros E. unfold validate_model, validate_rotates. rewrite E. auto. Qed.

Lemma prot3_cookie_msg_vm_mac2 CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC now r)) s) msg)
            (sublist (Zlength msg - 16) (Zlength msg) msg) = false ->
  validate_model CC s msg true now rl r = (VALID_MAC_BUT_NO_COOKIE, checker_rotate CC now r) /\
  validate_rotates CC msg true now = checker_rotates CC now.
Proof. intros E1 E2. unfold validate_model, validate_rotates. rewrite E1, E2. auto. Qed.

Lemma prot3_cookie_msg_vm_rl CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC now r)) s) msg)
            (sublist (Zlength msg - 16) (Zlength msg) msg) = true ->
  validate_model CC s msg true now rl r =
    (if rl then VALID_MAC_WITH_COOKIE else VALID_MAC_WITH_COOKIE_BUT_RATELIMITED, checker_rotate CC now r) /\
  validate_rotates CC msg true now = checker_rotates CC now.
Proof. intros E1 E2. unfold validate_model, validate_rotates. rewrite E1, E2. destruct rl; auto. Qed.

Lemma prot3_cookie_msg_skb_intro sh p s :
  skb_ok s -> @data_at Cookie.CS sh t_skb (skb_val s) p |-- skb_rep sh p s.
Proof. intros. unfold skb_rep. entailer!. Qed.

Lemma prot3_cookie_msg_msg3_fold sh msg d :
  32 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] d ->
  b2s_bytes sh (sublist 0 (Zlength msg - 32) msg) d *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 32) (Zlength msg - 16) msg))
    (offset_val (Zlength msg - 32) d) *
  @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
    (offset_val (Zlength msg - 16) d)
  |-- bytes_at sh msg d.
Proof. intros. rewrite (prot3_cookie_msg_msg3 sh msg d) by auto. apply derives_refl. Qed.

Lemma prot3_cookie_msg_rlallow (S: shim) (b: bool) (r: list byte) : s_rlallow (if b then shim_draw S r else S) = s_rlallow S.
Proof. destruct b; reflexivity. Qed.

Lemma prot3_cookie_msg_ba_ sh (l: list byte) p :
  bytes_at sh l p |-- @data_at_ Cookie.CS sh (tarray tuchar (Zlength l)) p.
Proof. rewrite prot3_cookie_msg_ba. apply data_at_data_at_. Qed.

Lemma prot3_cookie_msg_cc_lf sh c CC :
  checker_rep sh c CC |-- !! (cc_ok CC /\ field_compatible t_cc [] c).
Proof.
  unfold checker_rep. Intros lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

End CookieMsgLib.

Ltac prot3_cookie_msg_contra :=
  first [ apply Int.one_not_zero; assumption
        | match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end
        | match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end
        | match goal with Hx: Int.zero <> Int.zero |- _ => apply Hx; reflexivity end ].

