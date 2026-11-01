(* blake2s_compress_generic: the eight G macros of a round, one semax lemma each, in the context
   b2s_Gprog5 (b2s_compress_G3.v's lemmas against that context; the state and the tactics are reused from there). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stmts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

(* the type context of blake2s_compress_generic's body in the context b2s_Gprog5 *)
Definition b2s_cDelta5 : tycontext :=
  func_tycontext WgNoise.blake2s.code.f_blake2s_compress_generic (QPvarspecs Blake2s.qp) b2s_Gprog5 nil.

Section G.
Context {Espec: OracleKind}.
Variables (r: Z) (m: list int) (vv vm ctx data nb inc: val) (gv: globals) (FR: mpred).
Hypotheses (Hr: 0 <= r < 10) (Hm: Zlength m = 16).
Let x (j: Z) : int := Znth (Znth j (Znth r b2s_sigma)) m.

Lemma b2s_G5_ok_1 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_1
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 0 4 8 12 (x 0) (x 1)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_1.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_2 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_2
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 1 5 9 13 (x 2) (x 3)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_2.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_3 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_3
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 2 6 10 14 (x 4) (x 5)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_3.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_4 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_4
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 3 7 11 15 (x 6) (x 7)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_4.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_5 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_5
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 0 5 10 15 (x 8) (x 9)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_5.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_6 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_6
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 1 6 11 12 (x 10) (x 11)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_6.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_7 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_7
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 2 7 8 13 (x 12) (x 13)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_7.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

Lemma b2s_G5_ok_8 v : Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_8
    (normal_ret_assert
       (b2s_rstate r (WgNoise.proof.blake2s.model.b2s_G v 3 4 9 14 (x 14) (x 15)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hv. unfold b2s_G_stmt_8.
  match goal with |- semax _ ?P _ (normal_ret_assert ?Q) =>
    abbreviate_semax; forward_loop P continue: Q break: Q end;
  [ apply ENTAIL_refl | | forward; apply ENTAIL_refl | apply ENTAIL_refl ].
  unfold b2s_rstate, blake2s_globals.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward.
  { entailer!. apply b2s_sigma_is_int; lia. }
  b2s_sig r.
  forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  forward. forward. forward. b2s_upd.
  forward. forward. forward_call. forward. b2s_upd.
  b2s_fin.
Qed.

End G.
