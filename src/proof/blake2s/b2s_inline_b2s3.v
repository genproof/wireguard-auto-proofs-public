(* The blake2s.h inlines (__blake2s_init, blake2s_init, blake2s_init_key, blake2s) proved under Blake2s.CS, and
   the BLAKE2s piece over blake2s.c and any unit that compiles these inlines.

   The inlines are static in include/crypto/blake2s.h: every unit that uses them has its own copy, with the same
   Clight (cookie.c, noise.c, and the harnesses that call the BLAKE2s API directly).  b2s_inline_body3.v proves
   cookie.c's copies under Cookie.CS, which only programs linking cookie.c contain.  Here the same specifications
   are proved on the same Clight under Blake2s.CS (struct blake2s_ctx only), with the context of blake2s.c's
   bodies (b2s_Gprog3), so they move into every program that links blake2s.c, whichever unit compiles the
   inlines: blake2s_piece3_in gives the BLAKE2s piece (the same G, blake2s_G3) for a program whose unit `prog`
   holds the four inlines with cookie.c's Clight (checked by computation). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.proof.blake2s.b2s_inline_body3.
Require WgNoise.proof.blake2s.b2s_small_body3 WgNoise.proof.blake2s.b2s_compress_body3
        WgNoise.proof.blake2s.b2s_update_body3 WgNoise.proof.blake2s.b2s_final_body3.
Require WgNoise.cookie.code.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

(* __blake2s_init: the parameter block, the zeroed counters and, with a key, the key padded to one block *)
Lemma body___blake2s_init_b2s :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f___blake2s_init __blake2s_init_spec.
Proof.
start_function.
remember (Vlong (Int64.repr (Zlength key))) as vk.
remember (Vlong (Int64.repr outlen)) as vo.
forward.
fold (b2s_inline_body3.b2s_inline_pw vk vo).
rewrite Heqvk, Heqvo, b2s_inline_body3.b2s_inline_pw_eq by lia.
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
  destruct (b2s_inline_body3.b2s_inline_keyed_stream key outlen) as [E1 [E2 E3]]; [lia |].
  rewrite E1, E2, E3.
  rewrite b2s_bytes_nonempty by auto.
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
  unfold b2s_h_nonfinal, b2s_lastblock, b2s_nfull, b2s_stream, b2s_keyblock, b2s_blocks.
  rewrite !Zlength_nil.
  entailer!.
Qed.

(* blake2s_init: __blake2s_init without a key *)
Lemma body_blake2s_init_b2s :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f_blake2s_init blake2s_init_spec.
Proof.
start_function.
forward_call (sh, ctx, outlen, Ews, nullval, @nil byte).
{ rewrite b2s_bytes_nil. cancel. }
{ rewrite Zlength_nil. lia. }
entailer!.
Qed.

(* blake2s_init_key: __blake2s_init with the key *)
Lemma body_blake2s_init_key_b2s :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f_blake2s_init_key blake2s_init_key_spec.
Proof.
start_function.
forward.
forward_call (sh, ctx, outlen, ksh, k, key).
entailer!.
Qed.

(* blake2s: init (keyed or not), one update with the whole message, final, on a local context *)
Lemma body_blake2s_b2s :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f_blake2s blake2s_spec3.
Proof.
start_function.
forward.
forward_call (Tsh, v_ctx, outlen, ksh, k, key).
forward_call (Tsh, v_ctx, key, outlen, @nil byte, dsh, d, data, gv).
rewrite app_nil_l.
forward_call (Tsh, v_ctx, key, outlen, data, osh, out, gv).
sep_apply (data_at_data_at_ Tsh t_blake2s_ctx b2s_ctx_zero v_ctx).
entailer!.
Qed.

(* the four bodies, on cookie.c's Clight (the same in every unit), under Blake2s.CS *)
Lemma b2s_inline_bodies_b2s :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f___blake2s_init __blake2s_init_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f_blake2s_init blake2s_init_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f_blake2s_init_key blake2s_init_key_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.cookie.code.f_blake2s blake2s_spec3.
Proof.
  exact (conj body___blake2s_init_b2s (conj body_blake2s_init_b2s (conj body_blake2s_init_key_b2s body_blake2s_b2s))).
Qed.

(* a unit compiling the blake2s.h inlines, seen under Blake2s.CS with blake2s.c's varspecs *)
Definition u_b2s_inl (prog: Clight.program) : unit_ctx := mk_unit Blake2s.CS (QPvarspecs Blake2s.qp) prog.

(* the BLAKE2s piece: blake2s.c's bodies, and the inlines of a unit prog whose copies are cookie.c's *)
Theorem blake2s_piece3_in (prog: Clight.program) :
  find_internal prog ___blake2s_init = Some WgNoise.cookie.code.f___blake2s_init ->
  find_internal prog _blake2s_init = Some WgNoise.cookie.code.f_blake2s_init ->
  find_internal prog _blake2s_init_key = Some WgNoise.cookie.code.f_blake2s_init_key ->
  find_internal prog _blake2s = Some WgNoise.cookie.code.f_blake2s ->
  piece_ok [u_blake2s; u_b2s_inl prog] blake2s_imports3 blake2s_G3.
Proof.
  intros F0 F1 F2 F3.
  destruct b2s_small_body3.b2s_small_bodies as [Hror [Hinc [Hlast [Hle32 Hmz]]]].
  destruct b2s_inline_bodies_b2s as [Hinit0 [Hinit [Hinitk Hb2s]]].
  split; [repeat constructor; simpl; intuition discriminate |].
  change (blake2s_imports3 Blake2s.CS ++ blake2s_G3) with b2s_Gprog3 in *.
  repeat constructor.
  all: try (exists (u_b2s_inl prog); split; [simpl; auto |]; eexists; split;
            [eassumption | assumption]).
  all: exists u_blake2s; split; [simpl; auto |]; eexists; split; [reflexivity |];
       first [ assumption
             | exact b2s_compress_body3.body_blake2s_compress_generic
             | exact b2s_update_body3.body_blake2s_update3
             | exact b2s_final_body3.body_blake2s_final ].
Qed.
