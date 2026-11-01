(* Body proof(s) of the BLAKE2s piece: see blake2s_piece.v and b2s_prog.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.cookie.code.

#[local] Existing Instance Cookie.CS.

#[local] Instance CCE_b2s_cookie : change_composite_env Blake2s.CS Cookie.CS.
Proof. make_cs_preserve Blake2s.CS Cookie.CS. Defined.
#[local] Instance CCE_cookie_b2s : change_composite_env Cookie.CS Blake2s.CS.
Proof. make_cs_preserve Cookie.CS Blake2s.CS. Defined.

(* h[0] = IV0 ^ (0x01010000 | keylen << 8 | outlen), computed in u64 and stored in a u32 *)
Definition b2s_inline_pw (vk vo: val) : val :=
  force_val (sem_cast_l2i I32 Unsigned
    (force_val (sem_xor tint tulong (Vint (Int.repr 1779033703))
       (force_val (sem_or tulong tulong
          (force_val (sem_or tint tulong (Vint (Int.repr 16842752))
             (force_val (sem_shift_li (fun (_ : signedness) (n1 n2 : int64) => Int64.shl n1 n2)
                Unsigned vk (Vint (Int.repr 8)))))) vo))))).

Definition b2s_inline_pw_ok (kl ol: Z) : bool :=
  match b2s_inline_pw (Vlong (Int64.repr kl)) (Vlong (Int64.repr ol)) with
  | Vint i => Int.eq i (Int.xor (Znth 0 b2s_IV) (Int.repr (16842752 + kl * 256 + ol)))
  | _ => false
  end.

Lemma b2s_inline_pw_all :
  forallb (fun kl => forallb (fun ol => b2s_inline_pw_ok kl ol) (upto 33)) (upto 33) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b2s_inline_pw_eq kl ol :
  0 <= kl <= 32 -> 0 <= ol <= 32 ->
  b2s_inline_pw (Vlong (Int64.repr kl)) (Vlong (Int64.repr ol)) =
  Vint (Int.xor (Znth 0 b2s_IV) (Int.repr (16842752 + kl * 256 + ol))).
Proof.
  intros Hk Ho.
  pose proof b2s_inline_pw_all as A.
  rewrite forallb_forall in A.
  assert (Ik: In kl (upto 33)) by (apply In_upto; simpl; lia).
  assert (Io: In ol (upto 33)) by (apply In_upto; simpl; lia).
  specialize (A kl Ik). rewrite forallb_forall in A. specialize (A ol Io).
  unfold b2s_inline_pw_ok in A.
  destruct (b2s_inline_pw _ _); try discriminate.
  apply Int.same_if_eq in A. subst; reflexivity.
Qed.

(* the state after __blake2s_init with a key: one full block (the padded key), not compressed yet *)
Lemma b2s_inline_keyed_stream key outlen :
  0 < Zlength key <= 32 ->
  b2s_lastblock (b2s_stream key []) = key ++ Zrepeat Byte.zero (64 - Zlength key) /\
  b2s_h_nonfinal (Zlength key) outlen (b2s_stream key []) = b2s_h0 (Zlength key) outlen /\
  b2s_nfull (b2s_stream key []) = 0.
Proof.
  intros Hk.
  assert (Hs: b2s_stream key [] = key ++ Zrepeat Byte.zero (64 - Zlength key)).
  { unfold b2s_stream, b2s_keyblock. rewrite app_nil_r.
    destruct (Zlength key =? 0) eqn:E; [lia | reflexivity]. }
  assert (Hl: Zlength (b2s_stream key []) = 64) by (rewrite Hs; list_solve).
  assert (Hn: b2s_nfull (b2s_stream key []) = 0).
  { unfold b2s_nfull. rewrite Hl. reflexivity. }
  split; [| split]; auto.
  - unfold b2s_lastblock. rewrite Hn, Hl, Hs. apply sublist_same; list_solve.
  - unfold b2s_h_nonfinal, b2s_blocks. rewrite Hn. reflexivity.
Qed.

Lemma body___blake2s_init :
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f___blake2s_init __blake2s_init_spec.
Proof.
start_function.
erewrite (@data_at__change_composite Blake2s.CS Cookie.CS _ sh t_blake2s_ctx); [| prove_cs_preserve_type].
remember (Vlong (Int64.repr (Zlength key))) as vk.
remember (Vlong (Int64.repr outlen)) as vo.
forward.
fold (b2s_inline_pw vk vo). rewrite Heqvk, Heqvo, b2s_inline_pw_eq by lia.
do 11 forward.
forward.
forward.
match goal with |- context [data_at sh t_blake2s_ctx ?v ctx] =>
  replace v with (b2s_ctx_val (b2s_h0 (Zlength key) outlen) 0 Int.zero (Zrepeat Vundef 64) 0 outlen) end.
2:{ rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. simpl default_val.
    unfold b2s_ctx_val, b2s_h0, b2s_IV, b2s_t0, b2s_t1.
    rewrite <- (Int.eqm_samerepr 3144134277 (-1150833019)) by (exists 1; reflexivity).
    rewrite <- (Int.eqm_samerepr 2773480762 (-1521486534)) by (exists 1; reflexivity).
    rewrite <- (Int.eqm_samerepr 2600822924 (-1694144372)) by (exists 1; reflexivity).
    reflexivity. }
clear vk Heqvk vo Heqvo.
forward_if (PROP () LOCAL () SEP (blake2s_state sh key outlen [] ctx; b2s_bytes ksh key k)).
- (* keylen <> 0 *)
  rewrite b2s_bytes_nonempty by auto.
  erewrite (@data_at_change_composite Blake2s.CS Cookie.CS _ ksh (tarray tuchar (Zlength key)));
    [| apply JMeq_refl | reflexivity].
  unfold b2s_ctx_val.
  unfold_data_at (data_at sh t_blake2s_ctx _ ctx).
  rewrite (field_at_data_at sh t_blake2s_ctx (DOT _buf)).
  assert_PROP (field_compatible (tarray tuchar 64) [] (field_address t_blake2s_ctx (DOT _buf) ctx)) as Hfb
    by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh 64 (Zlength key)) by (try list_solve; lia).
  Intros.
  rewrite sublist_Zrepeat by lia. rewrite sublist_Zrepeat by lia.
  assert_PROP (field_compatible t_blake2s_ctx (DOT _buf) ctx) by entailer!.
  forward_call (sh, ksh, field_address t_blake2s_ctx (DOT _buf) ctx, k, Zlength key, key).
  replace (field_address0 (Tarray tuchar 64 noattr) (SUB Zlength key) (field_address t_blake2s_ctx (DOT _buf) ctx))
    with (offset_val (Zlength key) (field_address t_blake2s_ctx (DOT _buf) ctx)).
  2:{ rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia). simpl. f_equal. lia. }
  forward_call (sh, offset_val (Zlength key) (field_address t_blake2s_ctx (DOT _buf) ctx), 0, 64 - Zlength key).
  { entailer!. rewrite field_address_offset by auto. simpl. rewrite offset_offset_val.
    destruct ctx; try contradiction; simpl; repeat f_equal; lia. }
  forward.
  unfold blake2s_state. Exists (@nil val).
  destruct (b2s_inline_keyed_stream key outlen) as [E1 [E2 E3]]; [lia |].
  rewrite E1, E2, E3.
  rewrite b2s_bytes_nonempty by auto.
  erewrite (@data_at_change_composite Blake2s.CS Cookie.CS _ ksh (tarray tuchar (Zlength key)));
    [| apply JMeq_refl | reflexivity].
  erewrite (@data_at_change_composite Blake2s.CS Cookie.CS _ sh t_blake2s_ctx);
    [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite prop_true_andp by (rewrite Zlength_nil; list_solve).
  rewrite app_nil_r.
  replace (Zlength (key ++ Zrepeat Byte.zero (64 - Zlength key))) with 64 by list_solve.
  unfold b2s_ctx_val.
  unfold_data_at (data_at sh t_blake2s_ctx _ ctx).
  rewrite (field_at_data_at sh t_blake2s_ctx (DOT _buf)).
  rewrite (split2_data_at_Tarray_tuchar sh 64 (Zlength key)) by list_solve.
  replace (field_address0 (Tarray tuchar 64 noattr) (SUB Zlength key) (field_address t_blake2s_ctx (DOT _buf) ctx))
    with (offset_val (Zlength key) (field_address t_blake2s_ctx (DOT _buf) ctx)).
  2:{ rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia). simpl. f_equal. lia. }
  replace (sublist 0 (Zlength key) (map Vubyte (key ++ Zrepeat Byte.zero (64 - Zlength key))))
    with (map Vubyte key) by list_solve.
  replace (sublist (Zlength key) 64 (map Vubyte (key ++ Zrepeat Byte.zero (64 - Zlength key))))
    with (Zrepeat (Vubyte (Byte.repr 0)) (64 - Zlength key)) by list_solve.
  entailer!.
- (* keylen = 0: no key *)
  apply (f_equal Int64.unsigned) in H1. rewrite Int64.unsigned_repr in H1 by rep_lia.
  apply Zlength_nil_inv in H1. subst key.
  forward.
  unfold blake2s_state. Exists (Zrepeat Vundef 64).
  erewrite (@data_at_change_composite Cookie.CS Blake2s.CS _ sh t_blake2s_ctx);
    [| apply JMeq_refl | prove_cs_preserve_type].
  unfold b2s_h_nonfinal, b2s_lastblock, b2s_nfull, b2s_stream, b2s_keyblock, b2s_blocks.
  rewrite !Zlength_nil.
  entailer!.
Qed.

Lemma body_blake2s_init :
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f_blake2s_init blake2s_init_spec.
Proof.
start_function.
forward_call (sh, ctx, outlen, Ews, nullval, @nil byte).
{ rewrite b2s_bytes_nil. cancel. }
{ rewrite Zlength_nil. lia. }
entailer!.
Qed.

Lemma body_blake2s_init_key :
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f_blake2s_init_key blake2s_init_key_spec.
Proof.
start_function.
forward.
forward_call (sh, ctx, outlen, ksh, k, key).
entailer!.
Qed.

Lemma body_blake2s :
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f_blake2s blake2s_spec3.
Proof.
start_function.
forward.
erewrite (@data_at__change_composite Cookie.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_ctx, outlen, ksh, k, key).
forward_call (Tsh, v_ctx, key, outlen, @nil byte, dsh, d, data, gv).
rewrite app_nil_l.
forward_call (Tsh, v_ctx, key, outlen, data, osh, out, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_ctx).
erewrite (@data_at__change_composite Blake2s.CS Cookie.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
entailer!.
Qed.

Lemma b2s_inline_bodies :
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f___blake2s_init __blake2s_init_spec /\
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f_blake2s_init blake2s_init_spec /\
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f_blake2s_init_key blake2s_init_key_spec /\
  semax_body (QPvarspecs Cookie.qp) b2s_Gprog3_cookie WgNoise.cookie.code.f_blake2s blake2s_spec3.
Proof.
  exact (conj body___blake2s_init (conj body_blake2s_init (conj body_blake2s_init_key body_blake2s))).
Qed.
