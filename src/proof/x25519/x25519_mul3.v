(* part of x25519_part3: the body of fe_mul_impl (three aliasing modes).
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Local Open Scope Z_scope.

Lemma limbs10_3 (f: list int) : Zlength f = 10 ->
  exists a0 a1 a2 a3 a4 a5 a6 a7 a8 a9, f = [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9].
Proof.
  intros H.
  do 10 (destruct f as [|? f]; [rewrite ?Zlength_cons, ?Zlength_nil in H; rep_lia|]).
  destruct f; [|rewrite !Zlength_cons in H; pose proof (Zlength_nonneg f); rep_lia].
  eauto 20.
Qed.

Lemma upd10_3 (v: list val) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9: val) : Zlength v = 10 ->
  upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2
    (upd_Znth 1 (upd_Znth 0 v x0) x1) x2) x3) x4) x5) x6) x7) x8) x9 = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9].
Proof.
  intros H.
  do 10 (destruct v as [|? v]; [rewrite ?Zlength_cons, ?Zlength_nil in H; rep_lia|]).
  destruct v as [|w v]; [|rewrite !Zlength_cons in H; pose proof (Zlength_nonneg v); rep_lia].
  reflexivity.
Qed.

Fixpoint seq_drop3 (n: nat) (s: statement) : statement :=
  match n with O => s | S n' => match s with Ssequence _ s2 => seq_drop3 n' s2 | _ => s end end.

(* fe_mul_impl after its 20 loads *)
Definition mul_rest3 : statement :=
  Eval cbv beta iota zeta delta [seq_drop3 F.f_fe_mul_impl fn_body] in seq_drop3 20 (fn_body F.f_fe_mul_impl).

(* the type context of fe_mul_impl after start_function, with abstract function specs DS *)
Definition temps3 : Maps.PTree.t type :=
  ltac:(let t := eval compute in (make_tycontext_t (fn_params F.f_fe_mul_impl) (fn_temps F.f_fe_mul_impl)) in exact t).
Definition mD3 (DS: Maps.PTree.t funspec) : tycontext :=
  mk_tycontext temps3 (Maps.PTree.empty _) Tvoid (Maps.PTree.empty _) DS (Maps.PTree.empty _).

(* the i-th store statement out[i] = ... (i < 9), and the last one *)
Definition seq_head3 (s: statement) : statement := match s with Ssequence a _ => a | _ => s end.
Definition st3_0 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 81 mul_rest3).
Definition st3_1 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 82 mul_rest3).
Definition st3_2 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 83 mul_rest3).
Definition st3_3 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 84 mul_rest3).
Definition st3_4 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 85 mul_rest3).
Definition st3_5 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 86 mul_rest3).
Definition st3_6 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 87 mul_rest3).
Definition st3_7 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 88 mul_rest3).
Definition st3_8 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_head3 (seq_drop3 89 mul_rest3).
Definition st3_9 : statement := Eval cbv beta iota zeta delta [seq_head3 seq_drop3 mul_rest3] in seq_drop3 90 mul_rest3.

(* forward one Sset, then name the new temp's value (keeps LOCAL terms small) *)
Ltac abs_new3 :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vlong ?e) :: _) _)) _ _ =>
      is_var e || (let y := fresh "y" in remember e as y)
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vint ?e) :: _) _)) _ _ =>
      is_var e || (let y := fresh "y" in remember e as y)
  | _ => idtac
  end.
Ltac fwd_abs3 := forward; abs_new3.

(* one lemma per store: 10 stores in one proof make the kernel check explode (Qed > 600 s) *)
Lemma store3_0 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 0 w (Vint z2)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_0 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_0. forward. apply ENTAIL_refl.
Qed.

Lemma store3_1 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 1 w (Vint z0)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_1 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_1. forward. apply ENTAIL_refl.
Qed.

Lemma store3_2 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 2 w (Vint (Int.add z1 z10))) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_2 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_2. forward. apply ENTAIL_refl.
Qed.

Lemma store3_3 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 3 w (Vint z9)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_3 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_3. forward. apply ENTAIL_refl.
Qed.

Lemma store3_4 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 4 w (Vint z8)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_4 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_4. forward. apply ENTAIL_refl.
Qed.

Lemma store3_5 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 5 w (Vint z7)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_5 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_5. forward. apply ENTAIL_refl.
Qed.

Lemma store3_6 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 6 w (Vint z6)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_6 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_6. forward. apply ENTAIL_refl.
Qed.

Lemma store3_7 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 7 w (Vint z5)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_7 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_7. forward. apply ENTAIL_refl.
Qed.

Lemma store3_8 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) (rest: statement) (R: ret_assert) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 8 w (Vint z4)) out; FR)) rest R ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) (Ssequence st3_8 rest) R.
Proof.
  intros Hosh Hw Hrest. eapply semax_seq'; [ | exact Hrest ].
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_8. forward. apply ENTAIL_refl.
Qed.

Lemma store3_9 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (w: list val) (FR: mpred)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10: int) :
  writable_share osh -> Zlength w = 10 ->
  semax (mD3 DS) (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs w out; FR)) st3_9 (normal_ret_assert (PROP () LOCAL (temp F._x120 (Vint z0); temp F._x119 (Vint z1); temp F._x117 (Vint z2); temp F._x114 (Vint z3); temp F._x111 (Vint z4); temp F._x108 (Vint z5); temp F._x105 (Vint z6); temp F._x102 (Vint z7); temp F._x99 (Vint z8); temp F._x96 (Vint z9); temp F._x93 (Vint z10); temp F._out out) SEP (data_at osh t_limbs (upd_Znth 9 w (Vint z3)) out; FR))).
Proof.
  intros Hosh Hw.
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  unfold st3_9. forward. apply ENTAIL_refl.
Qed.

Lemma updlen3 (i: Z) (w: list val) (x: val) : Zlength w = 10 -> 0 <= i < 10 -> Zlength (upd_Znth i w x) = 10.
Proof. intros. rewrite upd_Znth_Zlength; lia. Qed.

Lemma mul_rest3_ok {Espec: OracleKind} (DS: Maps.PTree.t funspec) (osh: share) (out: val) (v: list val) (FR: mpred)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9: int) :
  writable_share osh -> Zlength v = 10 ->
  semax (mD3 DS)
    (PROP () LOCAL (temp F._x23 (Vint b0); temp F._x25 (Vint b1); temp F._x27 (Vint b2);
                    temp F._x29 (Vint b3); temp F._x31 (Vint b4); temp F._x33 (Vint b5);
                    temp F._x35 (Vint b6); temp F._x37 (Vint b7); temp F._x39 (Vint b8);
                    temp F._x38 (Vint b9);
                    temp F._x5 (Vint a0); temp F._x7 (Vint a1); temp F._x9 (Vint a2);
                    temp F._x11 (Vint a3); temp F._x13 (Vint a4); temp F._x15 (Vint a5);
                    temp F._x17 (Vint a6); temp F._x19 (Vint a7); temp F._x21 (Vint a8);
                    temp F._x20 (Vint a9); temp F._out out)
     SEP (data_at osh t_limbs v out; FR))
    mul_rest3
    (normal_ret_assert (PROP () LOCAL ()
      SEP (data_at osh t_limbs (map Vint (fe_mul_m [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9]
                                                 [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9])) out; FR))).
Proof.
  intros Hosh Hv. unfold mul_rest3.
  pose (Delta := @abbreviate tycontext (mD3 DS)); change (mD3 DS) with Delta.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  do 10 fwd_abs3. deadvars!.
  fwd_abs3. deadvars!.
  try unfold MORE_COMMANDS; try unfold POSTCONDITION; unfold abbreviate.
  eapply store3_0; [exact Hosh | exact Hv | ].
  eapply store3_1; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_2; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_3; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_4; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_5; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_6; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_7; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply store3_8; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv | ].
  eapply semax_post'; [ | apply store3_9; [exact Hosh | repeat (apply updlen3; [ | lia]); exact Hv] ].
  match goal with |- context [data_at _ _ (upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5
      (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 v (Vint ?e0)) (Vint ?e1)) (Vint ?e2))
      (Vint ?e3)) (Vint ?e4)) (Vint ?e5)) (Vint ?e6)) (Vint ?e7)) (Vint ?e8)) (Vint ?e9)) _] =>
    assert (E: fe_mul_m [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9] =
               [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9]) by (subst; unfold fe_mul_m, u64, lo; cbv zeta; f_equal);
    rewrite E, (upd10_3 v _ _ _ _ _ _ _ _ _ _ Hv)
  end.
  clear E; repeat match goal with H: _ = _ |- _ => clear H end.
  go_lower. apply derives_refl.
Qed.

Theorem x25519_mul3 : semax_body x25_V x25_Gprog F.f_fe_mul_impl fe_mul_impl_spec.
Proof.
  start_function.
  destruct (limbs10_3 f H) as (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & ->).
  destruct (limbs10_3 g H0) as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & ->).
  destruct m; simpl in H1 |- *; [ | subst out | subst out]; Intros.
  - do 20 forward. unfold MORE_COMMANDS, abbreviate.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?A :: ?B :: ?C :: nil)))) _ _ =>
      eapply semax_pre; [ | eapply semax_post; [ | | | | apply (mul_rest3_ok Delta_specs osh out (Zrepeat Vundef 10) (B * C)%logic a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 SH eq_refl) ] ]
    end.
    + entailer!.
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert.
      match goal with |- context [fe_mul_m ?x ?y] => generalize (fe_mul_m x y); intro h end.
      entailer!. try (unfold fe3_post; cancel).
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
    + intros; unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
  - do 20 forward. unfold MORE_COMMANDS, abbreviate.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?A :: ?B :: nil)))) _ _ =>
      eapply semax_pre; [ | eapply semax_post; [ | | | | apply (mul_rest3_ok Delta_specs osh in1 (map Vint [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9]) B a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 SH eq_refl) ] ]
    end.
    + entailer!.
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert.
      match goal with |- context [fe_mul_m ?x ?y] => generalize (fe_mul_m x y); intro h end.
      entailer!. try (unfold fe3_post; cancel).
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
    + intros; unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
  - do 20 forward. unfold MORE_COMMANDS, abbreviate.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?A :: ?B :: nil)))) _ _ =>
      eapply semax_pre; [ | eapply semax_post; [ | | | | apply (mul_rest3_ok Delta_specs osh in2 (map Vint [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9]) A a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 SH eq_refl) ] ]
    end.
    + entailer!.
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert.
      match goal with |- context [fe_mul_m ?x ?y] => generalize (fe_mul_m x y); intro h end.
      entailer!. try (unfold fe3_post; cancel).
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
    + unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
    + intros; unfold POSTCONDITION, abbreviate; simpl_ret_assert; normalize.
Qed.
