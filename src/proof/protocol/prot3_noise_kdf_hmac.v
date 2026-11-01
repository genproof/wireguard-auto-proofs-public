(* Group noise_kdf (prot_body3_noise_kdf.v): byte / buffer lemmas and the body of hmac (noise.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.proof.libc.libc_piece.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

#[local] Instance CCE_kdf_n2b : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance CCE_kdf_b2n : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

(* ---------------------------------------------------------------------------------------------- *)
(* byte lemmas                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma prot3_kdf_xor_store (b: byte) (c: Z) : 0 <= c <= 255 ->
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

Lemma prot3_kdf_xor_val (b: byte) (k: int) : 0 <= Int.unsigned k <= 255 ->
  force_val (sem_cast_i2i I8 Unsigned (force_val (sem_xor tuchar tint (Vubyte b) (Vint k)))) =
  Vubyte (Byte.xor (Byte.repr (Int.unsigned k)) b).
Proof. intros. rewrite <- prot3_kdf_xor_store by auto. rewrite Int.repr_unsigned. reflexivity. Qed.

(* one step of the xor loops *)
Lemma prot3_kdf_xor_step (c: byte) (xk: list byte) i n :
  Zlength xk = n -> 0 <= i < n ->
  upd_Znth i (bytes (map (Byte.xor c) (sublist 0 i xk) ++ sublist i n xk)) (Vubyte (Byte.xor c (Znth i xk))) =
  bytes (map (Byte.xor c) (sublist 0 (i + 1) xk) ++ sublist (i + 1) n xk).
Proof. intros. subst n. unfold bytes. list_solve. Qed.

Lemma prot3_kdf_xor_xor (b: byte) :
  Byte.xor (Byte.repr 106) (Byte.xor (Byte.repr 54) b) = Byte.xor (Byte.repr 92) b.
Proof. rewrite <- Byte.xor_assoc. reflexivity. Qed.

Lemma prot3_kdf_bytes_at_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite spec.b2s_bytes_nonempty by auto.
  apply data_at_tarray_tuchar_cs.
Qed.

Lemma prot3_kdf_blake2s_len key m : Zlength (blake2s key 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot3_kdf_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac, HASH. apply prot3_kdf_blake2s_len. Qed.

Lemma prot3_kdf_xkey_long key : 64 < Zlength key -> hmac_xkey key = blake2s [] 32 key ++ zeros 32.
Proof.
  intros Hk. unfold hmac_xkey, HASH. rewrite (proj2 (Z.ltb_lt _ _) Hk).
  rewrite prot3_kdf_blake2s_len. reflexivity.
Qed.

Lemma prot3_kdf_xkey_short key : Zlength key <= 64 -> hmac_xkey key = key ++ zeros (64 - Zlength key).
Proof. intros Hk. unfold hmac_xkey. rewrite (proj2 (Z.ltb_ge _ _) Hk). reflexivity. Qed.

Lemma prot3_kdf_xkey_len key : Zlength (hmac_xkey key) = 64.
Proof.
  destruct (Z.lt_ge_cases 64 (Zlength key)).
  - rewrite prot3_kdf_xkey_long by auto. unfold zeros. rewrite Zlength_app, prot3_kdf_blake2s_len. list_solve.
  - rewrite prot3_kdf_xkey_short by auto. unfold zeros. pose proof (Zlength_nonneg key). list_solve.
Qed.

Lemma prot3_kdf_data_at_b2s sh n bs p : Zlength bs = n -> n <> 0 ->
  @data_at Noise.CS sh (tarray tuchar n) (bytes bs) p = spec.b2s_bytes sh bs p.
Proof. intros. subst n. apply prot3_kdf_bytes_at_b2s. auto. Qed.

Section Split.
Local Open Scope logic.
#[local] Existing Instance Noise.CS.

Lemma prot3_kdf_frame (A B C: mpred) : A = B * C -> A |-- B * (B -* A).
Proof.
  intros ->. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. apply derives_refl.
Qed.

(* the data prefix of a buffer as a BLAKE2s input *)
Lemma prot3_kdf_prefix_split sh n (v: list val) data p :
  Zlength v = n -> Zlength data <= n -> sublist 0 (Zlength data) v = bytes data ->
  data_at sh (tarray tuchar n) v p |--
  spec.b2s_bytes sh data p * (spec.b2s_bytes sh data p -* data_at sh (tarray tuchar n) v p).
Proof.
  intros Hn Hd Hs. pose proof (Zlength_nonneg data).
  destruct (Z.eq_dec (Zlength data) 0) as [E|E].
  - unfold spec.b2s_bytes at 1 2. rewrite if_true by auto.
    rewrite emp_sepcon. apply wand_sepcon_adjoint. rewrite sepcon_emp. apply derives_refl.
  - apply (prot3_kdf_frame _ _ (data_at sh (tarray tuchar (n - Zlength data)) (sublist (Zlength data) n v)
      (field_address0 (tarray tuchar n) (SUB (Zlength data)) p))).
    rewrite (split2_data_at_Tarray_tuchar sh n (Zlength data)) by lia. f_equal.
    rewrite spec.b2s_bytes_nonempty by auto. rewrite Hs.
    apply data_at_tarray_tuchar_cs.
Qed.

(* the first 32 bytes of a buffer as an output *)
Lemma prot3_kdf_out_split sh n (v: list val) (h: list byte) p :
  Zlength v = n -> 32 <= n -> Zlength h = 32 ->
  data_at sh (tarray tuchar n) v p |--
  data_at_ sh (tarray tuchar 32) p *
  (data_at sh (tarray tuchar 32) (bytes h) p -* data_at sh (tarray tuchar n) (bytes h ++ sublist 32 n v) p).
Proof.
  intros Hn H32 Hh.
  rewrite (split2_data_at_Tarray_tuchar sh n 32 v) by lia.
  rewrite (split2_data_at_Tarray_tuchar sh n 32 (bytes h ++ sublist 32 n v)) by (unfold bytes; list_solve).
  replace (sublist 0 32 (bytes h ++ sublist 32 n v)) with (bytes h) by (unfold bytes; list_solve).
  replace (sublist 32 n (bytes h ++ sublist 32 n v)) with (sublist 32 n v) by (unfold bytes; list_solve).
  apply sepcon_derives; [apply data_at_data_at_ |].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. apply derives_refl.
Qed.

Lemma prot3_kdf_in alias osh ish out inp buf data :
  writable_share osh ->
  (alias = true -> out = inp /\ 32 <= Zlength buf /\ Zlength data <= Zlength buf /\
                   data = sublist 0 (Zlength data) buf) ->
  (if alias then bytes_at osh buf out else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp)
  |-- spec.b2s_bytes (if alias then osh else ish) data inp *
      (spec.b2s_bytes (if alias then osh else ish) data inp -*
       (if alias then bytes_at osh buf out
        else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp)).
Proof.
  intros Wo Ha. destruct alias.
  - destruct (Ha eq_refl) as [-> [H32 [Hd Hs]]]. unfold bytes_at.
    apply prot3_kdf_prefix_split; [unfold bytes; list_solve | auto |].
    rewrite Hs at 2. unfold bytes. rewrite sublist_map. f_equal.
  - eapply prot3_kdf_frame. apply sepcon_comm.
Qed.

Lemma prot3_kdf_out alias osh ish out inp buf data h :
  Zlength h = 32 ->
  (alias = true -> out = inp /\ 32 <= Zlength buf /\ Zlength data <= Zlength buf /\
                   data = sublist 0 (Zlength data) buf) ->
  (if alias then bytes_at osh buf out else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp)
  |-- data_at_ osh (tarray tuchar 32) out *
      (data_at osh (tarray tuchar 32) (bytes h) out -*
       (if alias then bytes_at osh (h ++ sublist 32 (Zlength buf) buf) out
        else bytes_at osh h out * spec.b2s_bytes ish data inp)).
Proof.
  intros Hh Ha. destruct alias.
  - destruct (Ha eq_refl) as [-> [H32 [Hd Hs]]]. unfold bytes_at.
    replace (Zlength (h ++ sublist 32 (Zlength buf) buf)) with (Zlength buf) by list_solve.
    replace (bytes (h ++ sublist 32 (Zlength buf) buf)) with (bytes h ++ sublist 32 (Zlength buf) (bytes buf))
      by (unfold bytes; rewrite map_app, sublist_map; reflexivity).
    apply prot3_kdf_out_split; [unfold bytes; list_solve | auto | auto].
  - unfold bytes_at. rewrite Hh. apply sepcon_derives; [apply derives_refl |].
    apply wand_sepcon_adjoint. rewrite sepcon_comm. apply derives_refl.
Qed.
(* kdf: the chaining key and the first output *)
Lemma prot3_kdf_ck (alias: bool) shc ck ckp sh1 d1 :
  (if alias then bytes_at shc ck ckp else bytes_at shc ck ckp * data_at_ sh1 (tarray tuchar 32) d1) |--
  bytes_at shc ck ckp *
  (bytes_at shc ck ckp -*
   (if alias then bytes_at shc ck ckp else bytes_at shc ck ckp * data_at_ sh1 (tarray tuchar 32) d1)).
Proof.
  destruct alias.
  - rewrite <- (sepcon_emp (bytes_at shc ck ckp)) at 1. apply sepcon_derives; [apply derives_refl |].
    apply wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
  - eapply prot3_kdf_frame. reflexivity.
Qed.

Lemma prot3_kdf_d1 (alias: bool) shc ck ckp sh1 d1 k :
  Zlength k = 32 -> Zlength ck = 32 -> (alias = true -> d1 = ckp) ->
  (if alias then bytes_at shc ck ckp else bytes_at shc ck ckp * data_at_ sh1 (tarray tuchar 32) d1) |--
  data_at_ (if alias then shc else sh1) (tarray tuchar 32) d1 *
  (data_at (if alias then shc else sh1) (tarray tuchar 32) (bytes k) d1 -*
   (if alias then bytes_at shc k ckp else bytes_at shc ck ckp * bytes_at sh1 k d1)).
Proof.
  intros Hk Hck Ha. unfold bytes_at. rewrite Hk. destruct alias.
  - rewrite (Ha eq_refl), Hck. rewrite <- (sepcon_emp (data_at shc (tarray tuchar 32) (bytes ck) ckp)).
    apply sepcon_derives; [apply data_at_data_at_ |].
    apply wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
  - rewrite sepcon_comm. apply sepcon_derives; [apply derives_refl |].
    apply wand_sepcon_adjoint. rewrite sepcon_comm. apply derives_refl.
Qed.
Lemma prot3_kdf_in_v alias osh ish out inp (buf: list val) data :
  writable_share osh ->
  (alias = true -> out = inp /\ 32 <= Zlength buf /\ Zlength data <= Zlength buf /\
                   sublist 0 (Zlength data) buf = bytes data) ->
  (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
   else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp)
  |-- spec.b2s_bytes (if alias then osh else ish) data inp *
      (spec.b2s_bytes (if alias then osh else ish) data inp -*
       (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
        else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp)).
Proof.
  intros Wo Ha. destruct alias.
  - destruct (Ha eq_refl) as [-> [H32 [Hd Hs]]].
    apply prot3_kdf_prefix_split; auto.
  - eapply prot3_kdf_frame. apply sepcon_comm.
Qed.

Lemma prot3_kdf_out_v alias osh ish out inp (buf: list val) data h :
  Zlength h = 32 ->
  (alias = true -> out = inp /\ 32 <= Zlength buf /\ Zlength data <= Zlength buf /\
                   sublist 0 (Zlength data) buf = bytes data) ->
  (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
   else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp)
  |-- data_at_ osh (tarray tuchar 32) out *
      (data_at osh (tarray tuchar 32) (bytes h) out -*
       (if alias then data_at osh (tarray tuchar (Zlength buf)) (bytes h ++ sublist 32 (Zlength buf) buf) out
        else bytes_at osh h out * spec.b2s_bytes ish data inp)).
Proof.
  intros Hh Ha. destruct alias.
  - destruct (Ha eq_refl) as [-> [H32 [Hd Hs]]].
    apply prot3_kdf_out_split; auto.
  - unfold bytes_at. rewrite Hh. apply sepcon_derives; [apply derives_refl |].
    apply wand_sepcon_adjoint. rewrite sepcon_comm. apply derives_refl.
Qed.
End Split.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* hmac_spec as used here: in alias mode the buffer is any list of values whose first
   |data| entries are the data (kdf's output[1..32] are uninitialized at the first expansion). *)
(* the specification proved here: prot_specs3.v hmac_spec *)
Notation hmac_spec_fix := hmac_spec (only parsing).

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gkdf := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Ltac prot3_kdf_norm_xkey k :=
  match goal with |- context [data_at Tsh (tarray tuchar 64) ?l ?x] =>
    let H := fresh in
    assert (H: l = Zrepeat (Vubyte Byte.zero) k ++ Zrepeat Vundef (64 - k)) by (vm_compute; reflexivity);
    rewrite H; clear H
  end.

Lemma body_hmac_fix : semax_body (QPvarspecs Noise.qp) Gkdf WgNoise.noise.code.f_hmac hmac_spec_fix.
Proof.
start_function.
do 8 forward. prot3_kdf_norm_xkey 8.
do 8 forward. prot3_kdf_norm_xkey 16.
do 8 forward. prot3_kdf_norm_xkey 24.
do 8 forward. prot3_kdf_norm_xkey 32.
do 8 forward. prot3_kdf_norm_xkey 40.
do 8 forward. prot3_kdf_norm_xkey 48.
do 8 forward. prot3_kdf_norm_xkey 56.
do 8 forward. prot3_kdf_norm_xkey 64.
change (Zrepeat (Vubyte Byte.zero) 64 ++ Zrepeat Vundef (64 - 64)) with (bytes (zeros 64)).
unfold wg_consts; Intros.
forward_if (PROP () LOCAL (lvar code._i_hash (tarray tuchar 32) v_i_hash;
   lvar code._x_key (tarray tuchar 64) v_x_key;
   lvar noise.code._blake (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   gvars gv; temp noise.code._out out; temp noise.code._in inp;
   temp noise.code._key kp;
   temp noise.code._inlen (Vlong (Int64.repr (Zlength data)));
   temp noise.code._keylen (Vlong (Int64.repr (Zlength key))))
   SEP (data_at_ Tsh (tarray tuchar 32) v_i_hash;
   data_at Tsh (tarray tuchar 64) (bytes (hmac_xkey key)) v_x_key;
   data_at_ Tsh (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
   else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp;
   bytes_at ksh key kp; blake2s_globals gv; @curve25519_globals Noise.CS gv; @zero_page Noise.CS gv; cookie_globals gv)).
- assert (Hk: 64 < Zlength key) by (rewrite !Int64.unsigned_repr in H2 by rep_lia; lia).
  erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
  forward_call (Tsh, v_blake, 32).
  rewrite (prot3_kdf_bytes_at_b2s ksh key kp) by lia.
  forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, ksh, kp, key, gv).
  rewrite app_nil_l.
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 32) by (unfold bytes; list_solve).
  Intros.
  rewrite (@data_at_tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 32).
  forward_call (Tsh, v_blake, @nil byte, 32, key, Tsh, v_x_key, gv).
  sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
  erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
  rewrite <- (prot3_kdf_bytes_at_b2s ksh key kp) by lia.
  rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS Tsh 32).
  rewrite prot3_kdf_xkey_long by auto.
  pose proof (prot3_kdf_blake2s_len [] key).
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 32 (bytes (blake2s [] 32 key ++ zeros 32)))
    by (unfold bytes, zeros; list_solve).
  replace (sublist 0 32 (bytes (blake2s [] 32 key ++ zeros 32))) with (map Vubyte (blake2s [] 32 key))
    by (unfold bytes, zeros; list_solve).
  replace (sublist 32 64 (bytes (blake2s [] 32 key ++ zeros 32))) with (sublist 32 64 (bytes (zeros 64)))
    by (unfold bytes, zeros; list_solve).
  entailer!.
- assert (Hk: Zlength key <= 64) by (rewrite !Int64.unsigned_repr in H2 by rep_lia; lia).
  pose proof (Zlength_nonneg key).
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 (Zlength key)) by (unfold bytes; list_solve).
  Intros.
  unfold bytes_at.
  forward_call (Tsh, ksh, v_x_key, kp, Zlength key, key).
  rewrite prot3_kdf_xkey_short by auto.
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 (Zlength key) (bytes (key ++ zeros (64 - Zlength key))))
    by (unfold bytes, zeros; list_solve).
  replace (sublist 0 (Zlength key) (bytes (key ++ zeros (64 - Zlength key)))) with (map Vubyte key)
    by (unfold bytes, zeros; list_solve).
  replace (sublist (Zlength key) 64 (bytes (key ++ zeros (64 - Zlength key)))) with
    (sublist (Zlength key) 64 (bytes (zeros 64))) by (unfold bytes, zeros; list_solve).
  unfold bytes_at, bytes. entailer!.
- pose proof (prot3_kdf_xkey_len key) as Hxl.
  set (xk := hmac_xkey key) in *.
  forward_for_simple_bound 64 (EX i: Z, PROP () LOCAL (lvar code._i_hash (tarray tuchar 32) v_i_hash;
   lvar code._x_key (tarray tuchar 64) v_x_key;
   lvar noise.code._blake (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   gvars gv; temp noise.code._out out; temp noise.code._in inp;
   temp noise.code._key kp;
   temp noise.code._inlen (Vlong (Int64.repr (Zlength data)));
   temp noise.code._keylen (Vlong (Int64.repr (Zlength key))))
   SEP (data_at_ Tsh (tarray tuchar 32) v_i_hash;
   data_at Tsh (tarray tuchar 64) (bytes (map (Byte.xor (Byte.repr 54)) (sublist 0 i xk) ++ sublist i 64 xk)) v_x_key;
   data_at_ Tsh (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
   else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp;
   bytes_at ksh key kp; blake2s_globals gv; @curve25519_globals Noise.CS gv; @zero_page Noise.CS gv; cookie_globals gv)).
  + entailer!. rewrite app_nil_l, sublist_same by auto. apply derives_refl.
  + assert (Hz: Znth i (bytes (map (Byte.xor (Byte.repr 54)) (sublist 0 i xk) ++ sublist i 64 xk)) =
                Vubyte (Znth i xk)) by (unfold bytes; list_solve).
    forward.
    { entailer!. rewrite Hz. apply WgNoise.proof.libc.libc_piece.is_int_Vubyte. }
    forward.
    assert (Hb: Znth i (map (Byte.xor (Byte.repr 54)) (sublist 0 i xk) ++ sublist i 64 xk) = Znth i xk)
      by list_solve.
    match goal with |- context [@Znth val ?d i (bytes ?l)] =>
      replace (@Znth val d i (bytes l)) with (Vubyte (Znth i xk)) by (unfold bytes; list_solve) end.
    rewrite prot3_kdf_xor_val by (rewrite Int.unsigned_repr by rep_lia; lia).
    rewrite Int.unsigned_repr by rep_lia.
    rewrite prot3_kdf_xor_step by lia.
    entailer!.
  + (* after the first xor loop *)
    set (ik := map (Byte.xor (Byte.repr 54)) xk).
    assert (Hik: Zlength ik = 64) by (unfold ik; rewrite Zlength_map; auto).
    replace (map (Byte.xor (Byte.repr 54)) (sublist 0 64 xk) ++ sublist 64 64 xk) with ik
      by (unfold ik; rewrite sublist_same by auto; rewrite sublist_nil, app_nil_r; auto).
    erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
    forward_call (Tsh, v_blake, 32).
    rewrite (prot3_kdf_data_at_b2s Tsh 64 ik v_x_key) by lia.
    forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, Tsh, v_x_key, ik, gv).
    { entailer!. rewrite Hik. reflexivity. }
    sep_apply (prot3_kdf_in_v alias osh ish out inp buf data SH H1).
    assert (Rd: readable_share (if alias then osh else ish)) by (destruct alias; auto).
    remember (if alias then osh else ish) as dsh eqn:Hdsh.
    remember (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
              else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp) as IO eqn:HIO.
    forward_call (Tsh, v_blake, @nil byte, 32, [] ++ ik, dsh, inp, data, gv).
    { cancel. }
    sep_apply (wand_frame_elim (spec.b2s_bytes dsh data inp) IO).
    forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ ik) ++ data, Tsh, v_i_hash, gv).
    rewrite app_nil_l.
    set (ih := blake2s [] 32 (ik ++ data)).
    assert (Hih: Zlength ih = 32) by apply prot3_kdf_blake2s_len.
    sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
    rewrite <- (prot3_kdf_data_at_b2s Tsh 64 ik v_x_key) by lia.
    forward_for_simple_bound 64 (EX i: Z, PROP () LOCAL (lvar code._i_hash (tarray tuchar 32) v_i_hash;
      lvar code._x_key (tarray tuchar 64) v_x_key;
      lvar noise.code._blake (Tstruct noise.code._blake2s_ctx noattr) v_blake;
      gvars gv; temp noise.code._out out; temp noise.code._in inp;
      temp noise.code._key kp;
      temp noise.code._inlen (Vlong (Int64.repr (Zlength data)));
      temp noise.code._keylen (Vlong (Int64.repr (Zlength key))))
      SEP (@data_at_ Blake2s.CS Tsh t_blake2s_ctx v_blake;
      @data_at Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte ih) v_i_hash;
      data_at Tsh (tarray tuchar 64) (bytes (map (Byte.xor (Byte.repr 106)) (sublist 0 i ik) ++ sublist i 64 ik)) v_x_key;
      IO; bytes_at ksh key kp; blake2s_globals gv; @curve25519_globals Noise.CS gv; @zero_page Noise.CS gv;
      cookie_globals gv)).
    * entailer!. rewrite app_nil_l, sublist_same by auto. apply derives_refl.
    * forward.
      { entailer!. apply WgNoise.proof.libc.libc_piece.is_int_Vubyte. }
      forward.
      match goal with |- context [@Znth val ?d i (bytes ?l)] =>
        replace (@Znth val d i (bytes l)) with (Vubyte (Znth i ik)) by (unfold bytes; list_solve) end.
      rewrite prot3_kdf_xor_val by (compute; split; congruence).
      replace (Int.unsigned (Int.xor (Int.repr 92) (Int.repr 54))) with 106 by reflexivity.
      rewrite prot3_kdf_xor_step by lia.
      entailer!.
    * set (ok := map (Byte.xor (Byte.repr 92)) xk).
      assert (Hok: map (Byte.xor (Byte.repr 106)) (sublist 0 64 ik) ++ sublist 64 64 ik = ok).
      { rewrite sublist_same by auto. rewrite sublist_nil, app_nil_r. unfold ik, ok. rewrite map_map.
        apply map_ext. intros; apply prot3_kdf_xor_xor. }
      rewrite Hok.
      assert (Hokl: Zlength ok = 64) by (unfold ok; rewrite Zlength_map; auto).
      forward_call (Tsh, v_blake, 32).
      rewrite (prot3_kdf_data_at_b2s Tsh 64 ok v_x_key) by lia.
      forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, Tsh, v_x_key, ok, gv).
      { entailer!. rewrite Hokl. reflexivity. }
      replace (@data_at Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte ih) v_i_hash)
        with (spec.b2s_bytes Tsh ih v_i_hash)
        by (rewrite spec.b2s_bytes_nonempty by lia; rewrite Hih; reflexivity).
      forward_call (Tsh, v_blake, @nil byte, 32, [] ++ ok, Tsh, v_i_hash, ih, gv).
      rewrite spec.b2s_bytes_nonempty by lia. rewrite Hih.
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte ih) v_i_hash).
      forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ ok) ++ ih, Tsh, v_i_hash, gv).
      rewrite !app_nil_l.
      replace (blake2s [] 32 (ok ++ ih)) with (hmac key data) by reflexivity.
      rewrite HIO.
      sep_apply (prot3_kdf_out_v alias osh ish out inp buf data (hmac key data) (prot3_kdf_hmac_len _ _) H1).
      rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS Tsh 32).
      forward_call (osh, Tsh, out, v_i_hash, 32, hmac key data).
      { cancel. }
      sep_apply (wand_frame_elim (data_at osh (tarray tuchar 32) (bytes (hmac key data)) out)).
      rewrite <- (prot3_kdf_data_at_b2s Tsh 64 ok v_x_key) by lia.
      rewrite (@data_at_tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 64).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 64) (bytes ok) v_x_key).
      forward_call (Tsh, v_x_key, 64).
      rewrite (@data_at_tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 32).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte (hmac key data)) v_i_hash).
      forward_call (Tsh, v_i_hash, 32).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
      erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 64) (Zrepeat (Vubyte Byte.zero) 64) v_x_key).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_i_hash).
      rewrite !(@data_at__tarray_tuchar_cs Blake2s.CS Noise.CS).
      unfold wg_consts. entailer!.
      apply derives_refl.
Qed.

End Bodies.
