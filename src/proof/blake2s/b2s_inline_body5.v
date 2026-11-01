(* the blake2s.h inlines __blake2s_init, blake2s_init and blake2s on noise.c's copies (the same Clight
   functions as cookie.c's), in the context b2s_Gprog5_noise; the proofs are those of b2s_inline_body3.v,
   whose helper lemmas are reused. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require Import WgNoise.proof.blake2s.b2s_inline_body3.
Require WgNoise.noise.code.

#[local] Existing Instance Noise.CS.

#[local] Instance CCE_b2s_noise : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.
#[local] Instance CCE_noise_b2s : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.

Lemma body___blake2s_init :
  semax_body (QPvarspecs Noise.qp) b2s_Gprog5_noise WgNoise.noise.code.f___blake2s_init __blake2s_init_spec.
Proof.
start_function.
erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ sh t_blake2s_ctx); [| prove_cs_preserve_type].
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
  erewrite (@data_at_change_composite Blake2s.CS Noise.CS _ ksh (tarray tuchar (Zlength key)));
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
  erewrite (@data_at_change_composite Blake2s.CS Noise.CS _ ksh (tarray tuchar (Zlength key)));
    [| apply JMeq_refl | reflexivity].
  erewrite (@data_at_change_composite Blake2s.CS Noise.CS _ sh t_blake2s_ctx);
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
  erewrite (@data_at_change_composite Noise.CS Blake2s.CS _ sh t_blake2s_ctx);
    [| apply JMeq_refl | prove_cs_preserve_type].
  unfold b2s_h_nonfinal, b2s_lastblock, b2s_nfull, b2s_stream, b2s_keyblock, b2s_blocks.
  rewrite !Zlength_nil.
  entailer!.
Qed.

Lemma body_blake2s_init :
  semax_body (QPvarspecs Noise.qp) b2s_Gprog5_noise WgNoise.noise.code.f_blake2s_init blake2s_init_spec.
Proof.
start_function.
forward_call (sh, ctx, outlen, Ews, nullval, @nil byte).
{ rewrite b2s_bytes_nil. cancel. }
{ rewrite Zlength_nil. lia. }
entailer!.
Qed.

Lemma body_blake2s :
  semax_body (QPvarspecs Noise.qp) b2s_Gprog5_noise WgNoise.noise.code.f_blake2s blake2s_spec3.
Proof.
start_function.
forward.
erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_ctx, outlen, ksh, k, key).
forward_call (Tsh, v_ctx, key, outlen, @nil byte, dsh, d, data, gv).
rewrite app_nil_l.
forward_call (Tsh, v_ctx, key, outlen, data, osh, out, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_ctx).
erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
entailer!.
Qed.

(* the blake2s.h inlines (noise.c's copies) *)
Lemma b2s_inline_bodies5 :
  semax_body (QPvarspecs Noise.qp) b2s_Gprog5_noise WgNoise.noise.code.f___blake2s_init __blake2s_init_spec /\
  semax_body (QPvarspecs Noise.qp) b2s_Gprog5_noise WgNoise.noise.code.f_blake2s_init blake2s_init_spec /\
  semax_body (QPvarspecs Noise.qp) b2s_Gprog5_noise WgNoise.noise.code.f_blake2s blake2s_spec3.
Proof.
  exact (conj body___blake2s_init (conj body_blake2s_init body_blake2s)).
Qed.
