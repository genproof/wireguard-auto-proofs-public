(* body of rp_mul (harness/common.h, TweetNaCl Poly1305) of law prim_aead, against hrp_mul of
   hrp1305_math3.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Module C := WgNoise.harness.x_prim_aead.code.

(* ---------------------------------------------------------------------- *)
(* helpers (proved here: hrp1305_math3.v's length lemmas are not used)      *)
(* ---------------------------------------------------------------------- *)

Lemma hram_loop_inv {A: Type} (P: A -> Prop) (f: A -> Z -> A) (n: Z) (a: A) :
  0 <= n -> P a -> (forall a j, 0 <= j < n -> P a -> P (f a j)) -> P (hrp_loop f n a).
Proof.
  intros Hn Ha Hf.
  assert (forall k, 0 <= k -> k <= n -> P (hrp_loop f k a)) as HK.
  { intros k Hk. pattern k. apply natlike_ind; [ | | exact Hk].
    - intros _. exact Ha.
    - intros x Hx IH Hle. unfold Z.succ in *. rewrite hrp_loop_succ by lia.
      apply Hf; [lia | ]. apply IH; lia. }
  apply HK; lia.
Qed.

Lemma hram_add_length h c : Zlength h = 17 -> Zlength (hrp_add h c) = 17.
Proof.
  intros Hh. unfold hrp_add.
  apply (hram_loop_inv (fun st => Zlength (fst st) = 17)); [lia | exact Hh | ].
  intros [l u] j Hj Hl. simpl in *. list_solve.
Qed.

Lemma hram_carry_length n x u :
  0 <= n <= 17 -> Zlength x = 17 -> Zlength (fst (hrp_loop hrp_carry_step n (x, u))) = 17.
Proof.
  intros Hn Hx.
  apply (hram_loop_inv (fun st => Zlength (fst st) = 17)); [lia | exact Hx | ].
  intros [l v] j Hj Hl. simpl in *. list_solve.
Qed.

Lemma hram_prods_length h r : Zlength (hrp_prods h r) = 17.
Proof. unfold hrp_prods. rewrite !Zlength_map. reflexivity. Qed.

Lemma hram_prods_Znth h r i : 0 <= i < 17 -> Znth i (hrp_prods h r) = hrp_prod h r i.
Proof.
  intros Hi. unfold hrp_prods. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; lia). f_equal.
  unfold Znth. rewrite if_false by lia. rewrite (nth_indep _ _ (Z.of_nat 0)) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. lia.
Qed.

(* the statement after rp_add(p->h, c) *)
Definition hra3_rpmul_rest : statement :=
  ltac:(let b := eval cbv delta [C.f_rp_mul fn_body] beta iota in (fn_body C.f_rp_mul) in
        match b with Ssequence _ ?r => exact r end).

Lemma hra3_rpmul_rest_ok {Espec: OracleKind} sh p r h1 s csh cp c v_x X :
  writable_share sh -> readable_share csh -> Zlength r = 17 -> Zlength h1 = 17 -> Zlength c = 17 ->
  Zlength X = 17 -> (forall i, 0 <= i < 17 -> Znth i X = hrp_prod h1 r i) ->
  semax (func_tycontext C.f_rp_mul haead_V haead_Gprog nil)
    (PROP () LOCAL (lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
     SEP (data_at sh t_rpoly (rpoly_val r h1 s) p; data_at csh (tarray tuint 17) (map Vint c) cp;
          data_at_ Tsh (tarray tuint 17) v_x))
    hra3_rpmul_rest
    (normal_ret_assert
      ((PROP () RETURN () SEP (data_at sh t_rpoly (rpoly_val r (hrp_reduce X) s) p;
                               data_at csh (tarray tuint 17) (map Vint c) cp)) * stackframe_of C.f_rp_mul)%logic).
Proof.
  intros SH SH0 H Hh1 H1 HXl HX.
  remember (hrp_reduce X) as hm eqn:Hm.
  unfold hra3_rpmul_rest. simplify_func_tycontext. abbreviate_semax.
  forward_for_simple_bound 17 (EX i: Z,
    PROP () LOCAL (lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
    SEP (data_at sh t_rpoly (rpoly_val r h1 s) p; data_at csh (tarray tuint 17) (map Vint c) cp;
         data_at Tsh (tarray tuint 17) (map Vint (sublist 0 i X) ++ Zrepeat Vundef (17 - i)) v_x))%assert.
  { entailer!. }
  { forward.
    forward_for_simple_bound 17 (EX j: Z,
      PROP () LOCAL (temp C._i (Vint (Int.repr i)); lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
      SEP (data_at sh t_rpoly (rpoly_val r h1 s) p; data_at csh (tarray tuint 17) (map Vint c) cp;
           data_at Tsh (tarray tuint 17)
             (map Vint (sublist 0 i X) ++ Vint (hrp_loop (hrp_prod_step h1 r i) j Int.zero) :: Zrepeat Vundef (16 - i)) v_x))%assert.
    { entailer!. apply derives_refl'. f_equal. rewrite hrp_loop_0. list_solve. }
    2: { entailer!. apply derives_refl'. f_equal. rewrite (sublist_split 0 i (i+1)) by lia.
         rewrite (sublist_one i (i+1)) by lia. rewrite HX by lia. unfold hrp_prod. list_solve. }
    forward_if (PROP () LOCAL (temp C._t'1 (Vint (hrp_coef r i i0)); temp C._j (Vint (Int.repr i0));
        temp C._i (Vint (Int.repr i)); lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
      SEP (data_at sh t_rpoly (rpoly_val r h1 s) p; data_at csh (tarray tuint 17) (map Vint c) cp;
           data_at Tsh (tarray tuint 17)
             (map Vint (sublist 0 i X) ++ Vint (hrp_loop (hrp_prod_step h1 r i) i0 Int.zero) :: Zrepeat Vundef (16 - i)) v_x)).
    { unfold rpoly_val. forward. forward. entailer!. unfold hrp_coef. rewrite if_true by lia. reflexivity. }
    { unfold rpoly_val. forward. forward. entailer!. unfold hrp_coef. rewrite if_false by lia. reflexivity. }
    remember (hrp_loop (hrp_prod_step h1 r i) i0 Int.zero) as acc eqn:Eacc.
    unfold rpoly_val. forward. { entailer!. list_solve. }
    match goal with |- semax _ (PROPx _ (LOCALx (temp _ ?v :: _) _)) _ _ =>
      assert (Hv: v = Vint acc) by list_solve; rewrite Hv; clear Hv end.
    forward. forward.
    entailer!. apply derives_refl'. f_equal. rewrite hrp_loop_succ by lia. unfold hrp_prod_step at 1. list_solve. }
  clear HX.
  replace (map Vint (sublist 0 17 X) ++ Zrepeat Vundef (17 - 17)) with (map Vint X) by list_solve.
  replace h1 with (sublist 0 0 X ++ sublist 0 17 h1) by list_solve.
  forward_for_simple_bound 17 (EX i: Z,
    PROP () LOCAL (lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
    SEP (data_at sh t_rpoly (rpoly_val r (sublist 0 i X ++ sublist i 17 h1) s) p;
         data_at csh (tarray tuint 17) (map Vint c) cp; data_at Tsh (tarray tuint 17) (map Vint X) v_x))%assert.
  { entailer!. }
  { unfold rpoly_val. forward.
    forward.
    assert (Hu: upd_Znth i (map Vint (sublist 0 i X ++ sublist i 17 h1)) (Vint (Znth i X))
              = map Vint (sublist 0 (i + 1) X ++ sublist (i + 1) 17 h1)) by list_solve.
    rewrite Hu. unfold rpoly_val. entailer!. }
  replace (sublist 0 17 X ++ sublist 17 17 h1) with X by list_solve.
  clear Hh1 h1.
  forward.
  forward_for_simple_bound 16 (EX j: Z,
    PROP () LOCAL (temp C._u (Vint (snd (hrp_loop hrp_carry_step j (X, Int.zero))));
                   lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
    SEP (data_at sh t_rpoly (rpoly_val r (fst (hrp_loop hrp_carry_step j (X, Int.zero))) s) p;
         data_at csh (tarray tuint 17) (map Vint c) cp; data_at Tsh (tarray tuint 17) (map Vint X) v_x))%assert.
  { entailer!. }
  { assert (Hl: Zlength (fst (hrp_loop hrp_carry_step i (X, Int.zero))) = 17) by (apply hram_carry_length; lia).
    destruct (hrp_loop hrp_carry_step i (X, Int.zero)) as [hj uj] eqn:Ej. cbn [fst snd] in Hl |- *.
    unfold rpoly_val. forward. forward. forward. forward.
    rewrite hrp_loop_succ, Ej by lia. unfold hrp_carry_step. cbn [fst snd]. rewrite upd_Znth_map.
    unfold rpoly_val. entailer!. }
  assert (Hl1: Zlength (fst (hrp_loop hrp_carry_step 16 (X, Int.zero))) = 17) by (apply hram_carry_length; lia).
  destruct (hrp_loop hrp_carry_step 16 (X, Int.zero)) as [h1 u1] eqn:E1. cbn [fst snd] in Hl1 |- *.
  unfold rpoly_val. forward. forward. forward. forward.
  rewrite upd_Znth_map.
  assert (Hl2: Zlength (upd_Znth 16 h1 (Int.and (Int.add u1 (Znth 16 h1)) (Int.repr 3))) = 17) by list_solve.
  remember (upd_Znth 16 h1 (Int.and (Int.add u1 (Znth 16 h1)) (Int.repr 3))) as h2 eqn:Eh2.
  remember (Int.mul (Int.repr 5) (Int.shru (Int.add u1 (Znth 16 h1)) (Int.repr 2))) as u2 eqn:Eu2.
  assert (Hfin: hrp_reduce X = upd_Znth 16 (fst (hrp_loop hrp_carry_step 16 (h2, u2)))
            (Int.add (snd (hrp_loop hrp_carry_step 16 (h2, u2))) (Znth 16 (fst (hrp_loop hrp_carry_step 16 (h2, u2)))))).
  { unfold hrp_reduce. cbv zeta. rewrite E1. cbn [fst snd]. subst h2 u2. reflexivity. }
  rewrite Hfin in Hm. clear Hfin Eh2 Eu2 E1.
  forward_for_simple_bound 16 (EX j: Z,
    PROP () LOCAL (temp C._u (Vint (snd (hrp_loop hrp_carry_step j (h2, u2))));
                   lvar C._x (tarray tuint 17) v_x; temp C._p p; temp C._c cp)
    SEP (data_at sh t_rpoly (rpoly_val r (fst (hrp_loop hrp_carry_step j (h2, u2))) s) p;
         data_at csh (tarray tuint 17) (map Vint c) cp; data_at Tsh (tarray tuint 17) (map Vint X) v_x))%assert.
  { entailer!. }
  { assert (Hl: Zlength (fst (hrp_loop hrp_carry_step i (h2, u2))) = 17) by (apply hram_carry_length; lia).
    destruct (hrp_loop hrp_carry_step i (h2, u2)) as [hj uj] eqn:Ej. cbn [fst snd] in Hl |- *.
    unfold rpoly_val. forward. forward. forward. forward.
    rewrite hrp_loop_succ, Ej by lia. unfold hrp_carry_step. cbn [fst snd]. rewrite upd_Znth_map.
    unfold rpoly_val. entailer!. }
  assert (Hl3: Zlength (fst (hrp_loop hrp_carry_step 16 (h2, u2))) = 17) by (apply hram_carry_length; lia).
  destruct (hrp_loop hrp_carry_step 16 (h2, u2)) as [h3 u3] eqn:E3. cbn [fst snd] in Hl3 |- *.
  unfold rpoly_val. forward.
  forward.
  cbn [fst snd] in Hm. subst hm. clear E3.
  forward.
  rewrite upd_Znth_map. unfold rpoly_val. entailer!.
Qed.

Lemma hra3_rpmul_body :
  semax_body haead_V haead_Gprog C.f_rp_mul rp_mul_spec.
Proof.
  start_function.
  unfold rpoly_val. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_rpoly [StructField C._h]).
  assert_PROP (field_compatible t_rpoly (DOT C._h) p) by entailer!.
  forward_call (sh, field_address t_rpoly [StructField C._h] p, h, csh, cp, c).
  replace (data_at sh (tarray tuint 17) (map Vint (hrp_add h c)) (field_address t_rpoly (DOT C._h) p))
    with (field_at sh t_rpoly (DOT C._h) (map Vint (hrp_add h c)) p) by (rewrite field_at_data_at; reflexivity).
  gather_SEP 0 3 4.
  replace_SEP 0 (data_at sh t_rpoly (rpoly_val r (hrp_add h c) s) p).
  { entailer!. unfold_data_at (data_at _ _ _ p). unfold rpoly_val; cbn [fst snd]; unfold C._h; cancel. }
  assert (Hm: hrp_mul r h c = hrp_reduce (hrp_prods (hrp_add h c) r)) by reflexivity.
  assert (Hh1: Zlength (hrp_add h c) = 17) by (apply hram_add_length; auto).
  remember (hrp_add h c) as h1 eqn:Eh1. clear Eh1.
  unfold POSTCONDITION, MORE_COMMANDS, abbreviate. rewrite Hm.
  apply hra3_rpmul_rest_ok; auto using hram_prods_length.
  intros; apply hram_prods_Znth; auto.
Qed.
