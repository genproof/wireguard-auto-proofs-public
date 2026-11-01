(* hc_pieces3, group sym: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.proof.libc.libc_piece.

#[local] Instance hc3b_sym_k2b : change_composite_env CSk Blake2s.CS.
Proof. make_cs_preserve CSk Blake2s.CS. Defined.
#[local] Instance hc3b_sym_b2k : change_composite_env Blake2s.CS CSk.
Proof. make_cs_preserve Blake2s.CS CSk. Defined.

Lemma hc3b_sym_hin sh bs p : hin sh bs p = spec.b2s_bytes sh bs p.
Proof.
  unfold hin, spec.b2s_bytes, hbytes, bytes. if_tac; auto. apply data_at_tarray_tuchar_cs.
Qed.

Lemma hc3b_sym_hbytes sh bs p : Zlength bs <> 0 -> hbytes sh bs p = spec.b2s_bytes sh bs p.
Proof.
  intros. rewrite <- hc3b_sym_hin. unfold hin. rewrite if_false by auto. reflexivity.
Qed.

Lemma hc3b_sym_blen32 k m : Zlength (blake2s k 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Lemma hc3b_sym_blen16 k m : Zlength (blake2s k 16 m) = 16.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity.
Qed.

(* m_hmac: the padded key and the xor loops *)
Lemma hc3b_sym_xkey K : Zlength K = 32 -> hmac_xkey K = K ++ zeros 32.
Proof. intros HK. unfold hmac_xkey. rewrite HK. replace (64 <? 32) with false by reflexivity. rewrite HK. reflexivity. Qed.

Lemma hc3b_sym_hmac K IN : Zlength K = 32 ->
  hmac K IN = HASH (map (Byte.xor (Byte.repr 92)) (K ++ zeros 32) ++
                    HASH (map (Byte.xor (Byte.repr 54)) (K ++ zeros 32) ++ IN)).
Proof. intros HK. unfold hmac. rewrite hc3b_sym_xkey by auto. reflexivity. Qed.

Lemma hc3b_sym_xor_store (b: byte) (c: Z) : 0 <= c <= 255 ->
  Vint (Int.zero_ext 8 (Int.xor (Int.repr (Byte.unsigned b)) (Int.repr c))) = Vubyte (Byte.xor (Byte.repr c) b).
Proof.
  intros Hc. rewrite Byte.xor_commut. pose proof (Byte.unsigned_range_2 b) as Hb.
  assert (R: 0 <= Z.lxor (Byte.unsigned b) c < 256)
    by (apply WgNoise.proof.libc.libc_piece.lxor_byte_range; rep_lia).
  unfold Vubyte, Byte.xor, Int.xor. f_equal.
  rewrite !Int.unsigned_repr by rep_lia.
  rewrite (Byte.unsigned_repr c) by rep_lia.
  rewrite Byte.unsigned_repr by rep_lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)).
  rewrite Int.zero_ext_mod by (cbv; intuition congruence).
  rewrite Int.unsigned_repr by rep_lia. f_equal. apply Z.mod_small. change (two_p 8) with 256. lia.
Qed.

Lemma hc3b_sym_xk_nth K j : Zlength K = 32 -> 0 <= j < 64 ->
  Znth j (K ++ zeros 32) = if zlt j 32 then Znth j K else Byte.zero.
Proof. intros HK Hj. unfold zeros. if_tac; list_solve. Qed.

Lemma hc3b_sym_hbytes32 sh bs p : Zlength bs = 32 ->
  hbytes sh bs p = @data_at CSk sh (tarray tuchar 32) (bytes bs) p.
Proof. intros Hl. unfold hbytes. rewrite Hl. apply data_at_tarray_tuchar_cs. Qed.

Lemma hc3b_sym_hin_ne sh bs n p : Zlength bs = n -> n <> 0 ->
  @data_at CSk sh (tarray tuchar n) (bytes bs) p = hin sh bs p.
Proof. intros Hl Hn. unfold hin, hbytes. rewrite if_false by lia. rewrite Hl. apply data_at_tarray_tuchar_cs. Qed.

Lemma hc3b_sym_hout sh n p : @data_at_ CSk sh (tarray tuchar n) p = hout sh n p.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

(* an equality that automation does not substitute (hides BLAKE2s terms) *)
Definition hc3b_sym_eqk (a b: list byte) : Prop := a = b.

Lemma hc3b_sym_step1 (c: byte) (xk: list byte) j :
  Zlength xk = 64 -> 0 <= j < 64 ->
  upd_Znth j (bytes (map (Byte.xor c) (sublist 0 j xk)) ++ Zrepeat Vundef (64 - j)) (Vubyte (Byte.xor c (Znth j xk))) =
  bytes (map (Byte.xor c) (sublist 0 (j + 1) xk)) ++ Zrepeat Vundef (64 - (j + 1)).
Proof. intros. unfold bytes. list_solve. Qed.

Lemma hc3b_sym_step2 (c: byte) (xk ik: list byte) j :
  Zlength xk = 64 -> Zlength ik = 64 -> 0 <= j < 64 ->
  upd_Znth j (bytes (map (Byte.xor c) (sublist 0 j xk) ++ sublist j 64 ik)) (Vubyte (Byte.xor c (Znth j xk))) =
  bytes (map (Byte.xor c) (sublist 0 (j + 1) xk) ++ sublist (j + 1) 64 ik).
Proof. intros. unfold bytes. list_solve. Qed.

#[local] Existing Instance CSk.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

Lemma hc3_body_m_hash2 :
  @semax_body [] (hc3_G_m_hash2) CSk FH.f_m_hash2 (m_hash2_spec).
Proof.
start_function.
erewrite (@data_at__change_composite CSk Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_ctx, 32).
rewrite !hc3b_sym_hin.
forward_call (Tsh, v_ctx, @nil byte, 32, @nil byte, sha, a, A, gv).
forward_call (Tsh, v_ctx, @nil byte, 32, [] ++ A, shb, b, B, gv).
unfold hout. rewrite (@data_at__tarray_tuchar_cs HCS Blake2s.CS).
forward_call (Tsh, v_ctx, @nil byte, 32, ([] ++ A) ++ B, sho, o, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_ctx).
erewrite (@data_at__change_composite Blake2s.CS CSk _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
rewrite app_nil_l, <- !hc3b_sym_hin.
change (blake2s [] 32 (A ++ B)) with (HASH (A ++ B)).
pose proof (hc3b_sym_blen32 [] (A ++ B)) as Hl. change (blake2s [] 32 (A ++ B)) with (HASH (A ++ B)) in Hl.
generalize (HASH (A ++ B)) Hl; intros hh Hhh.
unfold hbytes, bytes. rewrite Hhh, (@data_at_tarray_tuchar_cs Blake2s.CS HCS).
entailer!.
Qed.

Lemma hc3_body_m_hmac :
  @semax_body [] (hc3_G_m_hmac) CSk FH.f_m_hmac (m_hmac_spec).
Proof.
start_function.
assert (Hxk: Zlength (K ++ zeros 32) = 64) by (unfold zeros; list_solve).
rewrite (hc3b_sym_hbytes32 shk K k H).
forward_for_simple_bound 64 (EX j: Z, PROP () LOCAL (lvar FH._inner (tarray tuchar 32) v_inner;
   lvar FH._k (tarray tuchar 64) v_k; gvars gv; temp FH._out o;
   temp FH._key k; temp FH._in i; temp FH._inlen (Vlong (Int64.repr (Zlength IN))))
   SEP (data_at_ Tsh (tarray tuchar 32) v_inner;
   data_at Tsh (tarray tuchar 64) (bytes (map (Byte.xor (Byte.repr 54)) (sublist 0 j (K ++ zeros 32))) ++ Zrepeat Vundef (64 - j)) v_k;
   hout sho 32 o; data_at shk (tarray tuchar 32) (bytes K) k; hin shi IN i; blake2s_globals gv)).
- entailer!.
- rename i0 into j.
  forward_if (temp FH._t'1 (Vubyte (Znth j (K ++ zeros 32)))).
  + forward.
    { entailer!. apply WgNoise.proof.libc.libc_piece.is_int_Vubyte. }
    forward.
    replace (Znth j (bytes K)) with (Vubyte (Znth j K)) by (unfold bytes; rewrite Znth_map by lia; reflexivity).
    rewrite hc3b_sym_xk_nth by lia. rewrite if_true by lia. entailer!.
  + forward.
    rewrite hc3b_sym_xk_nth by lia. rewrite if_false by lia. entailer!.
  + forward.
    rewrite Int.zero_ext_idem by lia. rewrite hc3b_sym_xor_store by lia.
    rewrite hc3b_sym_step1 by lia. entailer!.
- set (ik := map (Byte.xor (Byte.repr 54)) (K ++ zeros 32)).
  assert (Hik: Zlength ik = 64) by (unfold ik; rewrite Zlength_map; auto).
  replace (bytes (map (Byte.xor (Byte.repr 54)) (sublist 0 64 (K ++ zeros 32))) ++ Zrepeat Vundef (64 - 64))
    with (bytes ik) by (unfold ik; rewrite sublist_same by auto; list_solve).
  rewrite (hc3b_sym_hin_ne Tsh ik 64 v_k Hik) by lia.
  rewrite (hc3b_sym_hout Tsh 32 v_inner).
  forward_call (gv, Tsh, v_inner, Tsh, v_k, ik, shi, i, IN).
  { apply prop_right; simpl; rewrite Hik; reflexivity. }
  assert (Hih: Zlength (HASH (ik ++ IN)) = 32) by apply hc3b_sym_blen32.
  remember (HASH (ik ++ IN)) as ih eqn:Eih. change (hc3b_sym_eqk ih (HASH (ik ++ IN))) in Eih.
  rewrite <- (hc3b_sym_hin_ne Tsh ik 64 v_k Hik) by lia.
  forward_for_simple_bound 64 (EX j: Z, PROP () LOCAL (
     lvar FH._inner (tarray tuchar 32) v_inner;
     lvar FH._k (tarray tuchar 64) v_k; gvars gv; temp FH._out o;
     temp FH._key k; temp FH._in i; temp FH._inlen (Vlong (Int64.repr (Zlength IN))))
     SEP (hbytes Tsh ih v_inner;
     data_at Tsh (tarray tuchar 64) (bytes (map (Byte.xor (Byte.repr 92)) (sublist 0 j (K ++ zeros 32)) ++ sublist j 64 ik)) v_k;
     hin shi IN i; blake2s_globals gv; hout sho 32 o; data_at shk (tarray tuchar 32) (bytes K) k)).
  + entailer!. rewrite sublist_same by auto. apply derives_refl.
  + rename i0 into j.
    forward_if (temp FH._t'2 (Vubyte (Znth j (K ++ zeros 32)))).
    * forward.
      { entailer!. apply WgNoise.proof.libc.libc_piece.is_int_Vubyte. }
      forward.
      replace (Znth j (bytes K)) with (Vubyte (Znth j K)) by (unfold bytes; rewrite Znth_map by lia; reflexivity).
      rewrite hc3b_sym_xk_nth by lia. rewrite if_true by lia. entailer!.
    * forward.
      rewrite hc3b_sym_xk_nth by lia. rewrite if_false by lia. entailer!.
    * forward.
      rewrite Int.zero_ext_idem by lia. rewrite hc3b_sym_xor_store by lia.
      rewrite hc3b_sym_step2 by lia. entailer!.
  + set (ok := map (Byte.xor (Byte.repr 92)) (K ++ zeros 32)).
    assert (Hok: Zlength ok = 64) by (unfold ok; rewrite Zlength_map; auto).
    replace (bytes (map (Byte.xor (Byte.repr 92)) (sublist 0 64 (K ++ zeros 32)) ++ sublist 64 64 ik))
      with (bytes ok) by (unfold ok; rewrite sublist_same by auto; rewrite sublist_nil, app_nil_r; reflexivity).
    rewrite (hc3b_sym_hin_ne Tsh ok 64 v_k Hok) by lia.
    assert (HI: hbytes Tsh ih v_inner = hin Tsh ih v_inner) by (unfold hin; rewrite if_false by lia; reflexivity).
    rewrite HI.
    forward_call (gv, sho, o, Tsh, v_k, ok, Tsh, v_inner, ih).
    { apply prop_right; simpl; rewrite Hok, Hih; reflexivity. }
    assert (Hm: HASH (ok ++ ih) = hmac K IN)
      by (unfold hc3b_sym_eqk in Eih; subst ih; rewrite hc3b_sym_hmac by auto; reflexivity).
    rewrite Hm. clear Hm Eih. generalize (hmac K IN); intros hm.
    rewrite <- (hc3b_sym_hin_ne Tsh ok 64 v_k Hok) by lia. rewrite <- HI.
    rewrite (hc3b_sym_hbytes32 shk K k H).
    unfold hbytes at 2. rewrite Hih, (@data_at_tarray_tuchar_cs HCS CSk).
    entailer!.
Qed.

Lemma hc3_body_m_label_key :
  @semax_body [] (hc3_G_m_hmac) CSk FH.f_m_label_key (m_label_key_spec).
Proof.
start_function.
assert (HL: hbytes sh LABEL l = hin sh LABEL l) by (unfold hin; rewrite if_false by lia; reflexivity).
assert (HP: hbytes sh PUB p = hin sh PUB p) by (unfold hin; rewrite if_false by lia; reflexivity).
rewrite HL, HP.
forward_call (gv, sho, o, sh, l, LABEL, sh, p, PUB).
{ apply prop_right; simpl; rewrite H, H0; reflexivity. }
rewrite <- HL, <- HP.
change (HASH (LABEL ++ PUB)) with (label_key LABEL PUB).
generalize (label_key LABEL PUB); intros lk.
entailer!.
Qed.

Lemma hc3_body_m_mac :
  @semax_body [] (hc3_G_m_mac) CSk FH.f_m_mac (m_mac_spec).
Proof.
start_function.
rewrite !hc3b_sym_hin.
unfold hout. rewrite (@data_at__tarray_tuchar_cs HCS Blake2s.CS).
forward_call (shk, k, K, shm, m, M, sho, o, 16, gv).
rewrite <- !hc3b_sym_hin.
pose proof (hc3b_sym_blen16 K M) as Hl. change (blake2s K 16 M) with (MAC K M) in Hl |- *.
generalize (MAC K M) Hl; intros mm Hmm.
unfold hbytes, bytes. rewrite Hmm, (@data_at_tarray_tuchar_cs Blake2s.CS HCS).
entailer!.
Qed.

(* the group *)
Theorem hc3_bodies_sym :
  (@semax_body [] (hc3_G_m_hash2) CSk FH.f_m_hash2 (m_hash2_spec)) /\
  (@semax_body [] (hc3_G_m_hmac) CSk FH.f_m_hmac (m_hmac_spec)) /\
  (@semax_body [] (hc3_G_m_hmac) CSk FH.f_m_label_key (m_label_key_spec)) /\
  (@semax_body [] (hc3_G_m_mac) CSk FH.f_m_mac (m_mac_spec)).
Proof.
exact (conj hc3_body_m_hash2 (conj hc3_body_m_hmac (conj hc3_body_m_label_key hc3_body_m_mac))).
Qed.

End Bodies.
