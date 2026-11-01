(* Body proof(s) of the BLAKE2s piece: see blake2s_piece.v and b2s_prog.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stmts.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_round3.
Require Import WgNoise.proof.blake2s.b2s_compress_step3.

#[local] Existing Instance Blake2s.CS.

Local Open Scope Z_scope.

Lemma body_blake2s_compress_generic :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_blake2s_compress_generic
    blake2s_compress_generic_spec.
Proof.
start_function.
assert_PROP (64 * n < Ptrofs.modulus) as Hnmax.
{ entailer!. destruct H12 as [Hp [_ [Hsz _]]]. destruct data; try contradiction. simpl in Hsz.
  rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i). lia. }
forward.
forward_while (EX k: Z,
  PROP (0 <= k <= n)
  LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
         temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
  SEP (data_at_ Tsh (tarray tuint 16) v_v; data_at_ Tsh (tarray tuint 16) v_m;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat k) h t f0 inc bs)) ctx;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (t + k * inc)); Vint (b2s_t1 (t + k * inc))] ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
       blake2s_globals gv))%assert.
{ Exists 0. rewrite Z.mul_0_l, Z.add_0_r. entailer!. }
{ entailer!. }
2: { forward. assert (k = n) by lia. subst k. entailer!. }
eapply semax_post; cycle 4.
{ apply b2s_compress_step; auto. }
all: unfold POSTCONDITION, abbreviate; simpl_ret_assert.
- apply ENTAIL_refl.
- normalize.
- normalize.
- intros; normalize.
Qed.
