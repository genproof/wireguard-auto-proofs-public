(* memcpy and memset of quickproof/libc/libc.c as a piece of their own, with no imports.

   libc_piece.v proves them with the context of the whole libc piece (libc_G: also calloc and the memneq functions
   of wg_shim.c and curve25519.c).  A body moves into a per-law program only if every function of its context is
   in that program, and the short laws that link libc.c without wg_shim.c / curve25519.c (ae_split_blake2s, whose
   blake2s.h inlines call memcpy and memset) cannot take that context.  memcpy and memset call nothing: the same
   proofs with the context of these two functions only. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.

#[local] Existing Instance Libc.CS.
Local Open Scope Z_scope.

Definition libc_mem_imports (cs: compspecs) : funspecs := nil.

Definition libc_mem_G : funspecs := [@memcpy_spec Libc.CS; @memset_spec Libc.CS].

Lemma body_memcpy_mem:
  semax_body (QPvarspecs Libc.qp) (libc_mem_imports Libc.CS ++ libc_mem_G)
    WgNoise.libc.code.f_memcpy (@memcpy_spec Libc.CS).
Proof.
  start_function.
  forward. forward.
  forward_for_simple_bound n (EX i:Z,
    PROP ()
    LOCAL (temp WgNoise.libc.code._d dst; temp WgNoise.libc.code._s src;
           temp WgNoise.libc.code._dest dst; temp WgNoise.libc.code._n (Vlong (Int64.repr n)))
    SEP (data_at dsh (tarray tuchar n) (map Vubyte (sublist 0 i bs) ++ Zrepeat Vundef (n - i)) dst;
         data_at ssh (tarray tuchar n) (map Vubyte bs) src)).
  - entailer!. simpl app. apply derives_refl.
  - forward.
    { entailer!. apply is_int_Vubyte. }
    forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - forward. entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma body_memset_mem:
  semax_body (QPvarspecs Libc.qp) (libc_mem_imports Libc.CS ++ libc_mem_G)
    WgNoise.libc.code.f_memset (@memset_spec Libc.CS).
Proof.
  start_function.
  forward.
  forward_for_simple_bound n (EX i:Z,
    PROP ()
    LOCAL (temp WgNoise.libc.code._p p; temp WgNoise.libc.code._s p;
           temp WgNoise.libc.code._c (Vint (Int.repr c)); temp WgNoise.libc.code._n (Vlong (Int64.repr n)))
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte (Byte.repr c)) i ++ Zrepeat Vundef (n - i)) p)).
  - entailer!. simpl app. apply derives_refl.
  - forward. entailer!. apply derives_refl'. f_equal.
    rewrite zero_ext_8_Vubyte. list_solve.
  - forward. entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Theorem libc_mem_piece : piece_ok [u_libc] libc_mem_imports libc_mem_G.
Proof.
  split.
  - apply compute_list_norepet_e. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memcpy. split; [reflexivity | apply body_memcpy_mem].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memset. split; [reflexivity | apply body_memset_mem].
Qed.
