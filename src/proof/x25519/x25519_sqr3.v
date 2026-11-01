(* part of x25519_part3: the body of fe_sqr_impl (two aliasing modes).
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Ltac fw3_ HALL :=
  forward;
  match goal with
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vlong ?e) :: _) _)) _ _ =>
      let y := fresh "y" in let Hn := fresh "Hn" in
      remember e as y eqn:Hn; apply (conj Hn) in HALL; clear Hn
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vint ?e) :: _) _)) _ _ =>
      let y := fresh "y" in let Hn := fresh "Hn" in
      remember e as y eqn:Hn; apply (conj Hn) in HALL; clear Hn
  end.

Definition sq3_temps : Maps.PTree.t type :=
  ltac:(let t := eval compute in (make_tycontext_t (fn_params F.f_fe_sqr_impl) (fn_temps F.f_fe_sqr_impl)) in exact t).

(* the tycontext of the body after start_function, with Delta_specs abstract (forward clears its body) *)
Definition sq3_Delta (DS: Maps.PTree.t funspec) : tycontext :=
  mk_tycontext sq3_temps (Maps.PTree.empty type) Tvoid (Maps.PTree.empty type) DS (Maps.PTree.empty Annotation).

(* put a lemma's goal [semax (sq3_Delta DS) ..] into the shape forward expects *)
Ltac sq3_start :=
  unfold sq3_Delta, sq3_temps;
  match goal with |- semax ?D _ _ _ => pose (Delta := @abbreviate tycontext D); change D with Delta end.

Definition sq3_store (k: Z) (e: expr) : statement :=
  Sassign (Ederef (Ebinop Oadd (Etempvar F._out (tptr tuint)) (Econst_int (Int.repr k) tint) (tptr tuint)) tuint) e.

Lemma sq3_st0 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x96 (Vint a0); temp F._x99 (Vint a1); temp F._x98 (Vint b2); temp F._x72 (Vint c2); temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 0 (Etempvar F._x96 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x99 (Vint a1); temp F._x98 (Vint b2); temp F._x72 (Vint c2); temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 0 vl (Vint a0)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st1 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x99 (Vint a1); temp F._x98 (Vint b2); temp F._x72 (Vint c2); temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 1 (Etempvar F._x99 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x98 (Vint b2); temp F._x72 (Vint c2); temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 1 vl (Vint a1)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st2 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x98 (Vint b2); temp F._x72 (Vint c2); temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 2 (Ebinop Oadd (Etempvar F._x98 tuint) (Etempvar F._x72 tuint) tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 2 vl (Vint (Int.add b2 c2))) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st3 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 3 (Etempvar F._x75 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 3 vl (Vint a3)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st4 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 4 (Etempvar F._x78 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 4 vl (Vint a4)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st5 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 5 (Etempvar F._x81 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 5 vl (Vint a5)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st6 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 6 (Etempvar F._x84 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 6 vl (Vint a6)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st7 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 7 (Etempvar F._x87 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 7 vl (Vint a7)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st8 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 8 (Etempvar F._x90 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._x93 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 8 vl (Vint a8)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_st9 {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (sq3_store 9 (Etempvar F._x93 tuint))
   (normal_ret_assert (PROP () LOCAL (temp F._out out)
     SEP (data_at osh t_limbs (upd_Znth 9 vl (Vint a9)) out; FR))).
Proof.
  intros SH LV. unfold sq3_store. sq3_start. forward. entailer!.
Qed.

Lemma sq3_upd_list (vl: list val) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9: int) :
  Zlength vl = 10 ->
  upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2
    (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint a2)) (Vint a3)) (Vint a4)) (Vint a5))
    (Vint a6)) (Vint a7)) (Vint a8)) (Vint a9)
  = map Vint [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9].
Proof. intros. list_solve. Qed.

Lemma sq3_stores_ok {Espec: OracleKind} DS osh out (FR: mpred) (vl: list val)
  (a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9: int) :
  writable_share osh -> Zlength vl = 10 ->
  semax (sq3_Delta DS)
   (PROP () LOCAL (temp F._x96 (Vint a0); temp F._x99 (Vint a1); temp F._x98 (Vint b2); temp F._x72 (Vint c2); temp F._x75 (Vint a3); temp F._x78 (Vint a4); temp F._x81 (Vint a5); temp F._x84 (Vint a6); temp F._x87 (Vint a7); temp F._x90 (Vint a8); temp F._x93 (Vint a9); temp F._out out) SEP (data_at osh t_limbs vl out; FR))
   (Ssequence (sq3_store 0 (Etempvar F._x96 tuint)) (Ssequence (sq3_store 1 (Etempvar F._x99 tuint)) (Ssequence (sq3_store 2 (Ebinop Oadd (Etempvar F._x98 tuint) (Etempvar F._x72 tuint) tuint))
    (Ssequence (sq3_store 3 (Etempvar F._x75 tuint)) (Ssequence (sq3_store 4 (Etempvar F._x78 tuint)) (Ssequence (sq3_store 5 (Etempvar F._x81 tuint))
    (Ssequence (sq3_store 6 (Etempvar F._x84 tuint)) (Ssequence (sq3_store 7 (Etempvar F._x87 tuint)) (Ssequence (sq3_store 8 (Etempvar F._x90 tuint))
    (sq3_store 9 (Etempvar F._x93 tuint)))))))))))
   (normal_ret_assert (PROP () LOCAL (temp F._out out)
     SEP (data_at osh t_limbs (map Vint [a0; a1; Int.add b2 c2; a3; a4; a5; a6; a7; a8; a9]) out; FR))).
Proof.
  intros SH LV.

  eapply semax_seq'; [apply (sq3_st0 DS osh out FR vl a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st1 DS osh out FR (upd_Znth 0 vl (Vint a0)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st2 DS osh out FR (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st3 DS osh out FR (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st4 DS osh out FR (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) (Vint a3)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st5 DS osh out FR (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) (Vint a3)) (Vint a4)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st6 DS osh out FR (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) (Vint a3)) (Vint a4)) (Vint a5)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st7 DS osh out FR (upd_Znth 6 (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) (Vint a3)) (Vint a4)) (Vint a5)) (Vint a6)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  eapply semax_seq'; [apply (sq3_st8 DS osh out FR (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) (Vint a3)) (Vint a4)) (Vint a5)) (Vint a6)) (Vint a7)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve | ].

  rewrite <- (sq3_upd_list vl) by auto.
  apply (sq3_st9 DS osh out FR (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 vl (Vint a0)) (Vint a1)) (Vint (Int.add b2 c2))) (Vint a3)) (Vint a4)) (Vint a5)) (Vint a6)) (Vint a7)) (Vint a8)) a0 a1 b2 c2 a3 a4 a5 a6 a7 a8 a9); auto; list_solve.
Qed.

Theorem x25519_sqr3 : semax_body x25_V x25_Gprog F.f_fe_sqr_impl fe_sqr_impl_spec.
Proof.
  start_function.
  destruct m; simpl fe2_pre; simpl fe2_ok in *.
  - Intros. assert (HALL: True) by trivial. do 10 (fw3_ HALL).
    do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL).
    do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 1 (fw3_ HALL).
    assert (HM: fe_sqr_m f = [y86; y89; Int.add y88 y62; y65; y68; y71; y74; y77; y80; y83]).
    { clear - HALL. repeat match goal with H: _ /\ _ |- _ => destruct H end. subst.
      unfold fe_sqr_m. reflexivity. }
    clear HALL. deadvars!. unfold MORE_COMMANDS, abbreviate.
    change Delta with (sq3_Delta Delta_specs).
    eapply semax_pre; [ | eapply semax_post; [ | | | |
      apply (sq3_stores_ok Delta_specs osh out (data_at sh1 t_limbs (map Vint f) in1) (default_val t_limbs)
        y86 y89 y88 y62 y65 y68 y71 y74 y77 y80 y83); auto ] ].
    { entailer!. }
    { unfold POSTCONDITION, abbreviate; simpl_ret_assert. rewrite HM. simpl fe2_post. entailer!. }
    all: unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
  - subst in1. assert (HALL: True) by trivial. do 10 (fw3_ HALL).
    do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL).
    do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 10 (fw3_ HALL). do 1 (fw3_ HALL).
    assert (HM: fe_sqr_m f = [y86; y89; Int.add y88 y62; y65; y68; y71; y74; y77; y80; y83]).
    { clear - HALL. repeat match goal with H: _ /\ _ |- _ => destruct H end. subst.
      unfold fe_sqr_m. reflexivity. }
    clear HALL. deadvars!. unfold MORE_COMMANDS, abbreviate.
    change Delta with (sq3_Delta Delta_specs).
    eapply semax_pre; [ | eapply semax_post; [ | | | |
      apply (sq3_stores_ok Delta_specs osh out emp (map Vint f)
        y86 y89 y88 y62 y65 y68 y71 y74 y77 y80 y83); auto; list_solve ] ].
    { entailer!. }
    { unfold POSTCONDITION, abbreviate; simpl_ret_assert. rewrite HM. simpl fe2_post. entailer!. }
    all: unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
Qed.
