(* law replay (harness/replay.c): the law's own piece interface.
   The harness unit's functions outside common.h are main and copy_init (common.h's are hc_G3_replay, proved by
   hc_pieces3).  Both are proved in the world compspecs W_replay (wg3_worlds.v), as law create_any's main; the
   imports are everything common.h's functions import (hc_imports3 at CSw := W_replay: the environment, libc,
   the lower pieces' interfaces, the protocol piece prot_G3) and the common.h functions themselves.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

Module RC := WgNoise.harness.x_replay.code.

(* the WHOLE program's variables (main_pre describes every global; VST's main_pre_InitGpred needs each of them
   in main's Delta) *)
Definition hrp3_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_replay.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs (as law prim_aead's u_haead) *)
Definition u_hrp3 : unit_ctx := mk_unit W_replay hrp3_V WgNoise.harness.x_replay.code.prog.

Definition hrp3_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hrp3_main_spec : ident * funspec :=
  (RC._main, QPmain_spec_ext' WgNoise.contracts.x_replay.whole_prog tt hrp3_post).

(* copy_init(d, s): d becomes a copy of the message s (field by field); returns 1 *)
Definition hrp3_copy_init_spec :=
  DECLARE RC._copy_init
  WITH shd: share, d: val, shs: share, s: val, M: init_msg
  PRE [ tptr t_init, tptr t_init ]
    PROP (writable_share shd; readable_share shs)
    PARAMS (d; s)
    SEP (@data_at_ Noise.CS shd t_init d; init_rep shs s M)
  POST [ tint ]
    PROP () RETURN (Vint Int.one)
    SEP (init_rep shd d M; init_rep shs s M).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hrp3_imports (cs: compspecs) : funspecs :=
  hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec W_replay cs ++
  hc_G3_replay x25519 aead_enc aead_dec.

End Piece.

Definition hrp3_G : funspecs := [hrp3_copy_init_spec; hrp3_main_spec].
