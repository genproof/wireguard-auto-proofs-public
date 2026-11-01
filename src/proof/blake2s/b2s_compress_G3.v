(* blake2s_compress_generic: the eight G macros of a round, one semax lemma each. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require Import WgNoise.proof.blake2s.b2s_compress_stmts.
Require WgNoise.blake2s.code.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Definition b2s_cDelta : tycontext :=
  func_tycontext WgNoise.blake2s.code.f_blake2s_compress_generic (QPvarspecs Blake2s.qp) b2s_Gprog3 nil.

(* the state inside the round loop: v, m, and the rest (locals as values, the other resources as FR) *)
Definition b2s_rstate (r: Z) (v m: list int) (vv vm ctx data nb inc: val) (gv: globals) (FR: mpred)
  : environ -> mpred :=
  PROP ()
  LOCAL (temp code._r (Vint (Int.repr r)); lvar code._v (tarray tuint 16) vv;
         lvar code._m (tarray tuint 16) vm; gvars gv; temp code._ctx ctx; temp code._data data;
         temp code._nblocks nb; temp code._inc inc)
  SEP (data_at Tsh (tarray tuint 16) (map Vint v) vv; data_at Tsh (tarray tuint 16) (map Vint m) vm;
       blake2s_globals gv; FR).

Lemma b2s_sigma_range r j : 0 <= r < 10 -> 0 <= j < 16 -> 0 <= Znth j (Znth r b2s_sigma) < 16.
Proof.
  intros Hr Hj.
  assert (Forall (fun l => Zlength l = 16 /\ Forall (fun z => 0 <= z < 16) l) b2s_sigma) as HF
    by (repeat constructor; lia).
  rewrite Forall_Znth in HF. assert (Zlength b2s_sigma = 10) by reflexivity. specialize (HF r ltac:(lia)).
  destruct HF as [Hl HF]. rewrite Forall_Znth in HF. apply HF. lia.
Qed.

Lemma b2s_Znth_inh {A} (d d': A) i l : 0 <= i < Zlength l -> @Znth A d i l = @Znth A d' i l.
Proof.
  intros. unfold Znth. rewrite !if_false by lia. apply nth_indep.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma b2s_sigma_val_Znth (d: val) (dl: list val) r j : 0 <= r < 10 -> 0 <= j < 16 ->
  @Znth val d j (@Znth (list val) dl r blake2s_sigma_val) = Vint (Int.repr (Znth j (Znth r b2s_sigma))).
Proof.
  intros. assert (Zlength b2s_sigma = 10) by reflexivity.
  assert (Zlength (Znth r b2s_sigma) = 16) as Hl.
  { assert (Forall (fun l => Zlength l = 16) b2s_sigma) as HF by (repeat constructor).
    rewrite Forall_Znth in HF. apply HF. lia. }
  rewrite (b2s_Znth_inh dl (@Inhabitant_list val)) by (unfold blake2s_sigma_val; rewrite Zlength_map; lia).
  unfold blake2s_sigma_val. rewrite Znth_map by lia.
  rewrite (b2s_Znth_inh d Vundef) by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.

Lemma b2s_sigma_is_int (d: val) (dl: list val) r j : 0 <= r < 10 -> 0 <= j < 16 ->
  is_int I8 Unsigned (@Znth val d j (@Znth (list val) dl r blake2s_sigma_val)).
Proof.
  intros. rewrite b2s_sigma_val_Znth by lia. pose proof (b2s_sigma_range r j H H0).
  simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Ltac b2s_sig r :=
  match goal with |- context [Znth ?j (Znth r blake2s_sigma_val)] =>
    rewrite (b2s_sigma_val_Znth _ _ r j) by lia; pose proof (b2s_sigma_range r j ltac:(lia) ltac:(lia))
  end.

Ltac b2s_upd :=
  match goal with |- context [upd_Znth ?i (map Vint ?w) (Vint ?y)] =>
    rewrite (upd_Znth_map Vint i w y);
    let w' := fresh "w" in let Hw' := fresh "Hw" in
    remember (upd_Znth i w y) as w' eqn:Hw';
    assert (Zlength w' = 16) by (subst w'; rewrite Zlength_upd_Znth; lia)
  end.

Ltac b2s_fin :=
  unfold b2s_rstate, blake2s_globals;
  match goal with |- ENTAIL _, PROPx _ (LOCALx _ (SEPx (data_at _ _ (map Vint ?wf) _ :: _)))
                   |-- PROPx _ (LOCALx _ (SEPx (data_at _ _ (map Vint ?wg) _ :: _))) =>
    replace wf with wg by (subst; reflexivity)
  end;
  repeat match goal with H: _ = upd_Znth _ _ _ |- _ => clear H end;
  entailer!.

Section G.
Context {Espec: OracleKind}.
Variables (r: Z) (m: list int) (vv vm ctx data nb inc: val) (gv: globals) (FR: mpred).
Hypotheses (Hr: 0 <= r < 10) (Hm: Zlength m = 16).
Let x (j: Z) : int := Znth (Znth j (Znth r b2s_sigma)) m.

Lemma b2s_G_ok_1 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_1
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

Lemma b2s_G_ok_2 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_2
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

Lemma b2s_G_ok_3 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_3
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

Lemma b2s_G_ok_4 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_4
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

Lemma b2s_G_ok_5 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_5
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

Lemma b2s_G_ok_6 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_6
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

Lemma b2s_G_ok_7 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_7
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

Lemma b2s_G_ok_8 v : Zlength v = 16 ->
  semax b2s_cDelta (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_G_stmt_8
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
