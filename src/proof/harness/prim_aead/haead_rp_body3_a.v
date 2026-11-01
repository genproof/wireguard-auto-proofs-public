(* bodies of rp_add, rp_init, rp_block, rp_final (harness/common.h, TweetNaCl Poly1305) of law
   prim_poly1305, against the models of hrp1305_math3.v. *)
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
(* lengths (proved here: hrp1305_math3.v's length lemmas are not used)     *)
(* ---------------------------------------------------------------------- *)

Lemma hra3_rp_loop_ind {A: Type} (P: A -> Prop) (f: A -> Z -> A) (n: Z) (a: A) :
  0 <= n -> P a -> (forall b j, 0 <= j < n -> P b -> P (f b j)) -> P (hrp_loop f n a).
Proof.
  intros Hn Ha Hf.
  assert (H: forall k, 0 <= k -> k <= n -> P (hrp_loop f k a)).
  { intros k Hk. pattern k. apply natlike_ind; [ | | exact Hk].
    - intros _. rewrite hrp_loop_0. exact Ha.
    - intros x Hx IH Hxn. unfold Z.succ. rewrite hrp_loop_succ by lia.
      apply Hf; [lia | apply IH; lia]. }
  apply H; lia.
Qed.

Lemma hra3_rp_add_loop_len c n s :
  0 <= n -> Zlength (fst (hrp_loop (hrp_add_step c) n s)) = Zlength (fst s).
Proof.
  intros Hn. apply (hra3_rp_loop_ind (fun t => Zlength (fst t) = Zlength (fst s))); auto.
  intros b j Hj Hb. unfold hrp_add_step. simpl. rewrite Zlength_upd_Znth; exact Hb.
Qed.

Lemma hra3_rp_add_len h c : Zlength (hrp_add h c) = Zlength h.
Proof. unfold hrp_add. rewrite hra3_rp_add_loop_len by lia. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* rp_add                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hra3_rp_add_body : semax_body haead_V haead_Gprog C.f_rp_add rp_add_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 17 (EX j: Z,
    PROP ()
    LOCAL (temp C._u (Vint (snd (hrp_loop (hrp_add_step c) j (h, Int.zero)))); temp C._h hp; temp C._c cp)
    SEP (data_at hsh (tarray tuint 17) (map Vint (fst (hrp_loop (hrp_add_step c) j (h, Int.zero)))) hp;
         data_at csh (tarray tuint 17) (map Vint c) cp)).
  - entailer!.
  - assert (Hl: Zlength (fst (hrp_loop (hrp_add_step c) i (h, Int.zero))) = 17)
      by (rewrite hra3_rp_add_loop_len by lia; simpl; lia).
    forward. forward. forward. forward. forward.
    rewrite hrp_loop_succ by lia. unfold hrp_add_step at 1 2. cbn [fst snd]. rewrite upd_Znth_map.
    entailer!.
  - entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* rp_init                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hra3_rp_mask_len j m r : Zlength (hrp_mask j m r) = Zlength r.
Proof. unfold hrp_mask. apply Zlength_upd_Znth. Qed.

Lemma hra3_rp_mask_map j m r :
  upd_Znth j (map Vint r) (Vint (Int.and (Znth j r) (Int.repr m))) = map Vint (hrp_mask j m r).
Proof. unfold hrp_mask. rewrite upd_Znth_map. reflexivity. Qed.

Lemma hra3_rp_is_int_ubyte b : is_int I8 Unsigned (Vubyte b).
Proof.
  simpl. pose proof (Byte.unsigned_range_2 b). rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(* a struct rpoly value from three lists of values *)
Definition hra3_rpv (r h s: list val) : reptype t_rpoly := (r, (h, s)).

Lemma hra3_rp_init_body : semax_body haead_V haead_Gprog C.f_rp_init rp_init_spec.
Proof.
  start_function.
  forward_for_simple_bound 17 (EX j: Z,
    PROP ()
    LOCAL (temp C._p p; temp C._key k)
    SEP (data_at sh t_rpoly (hra3_rpv (map Vint (Zrepeat Int.zero j) ++ Zrepeat Vundef (17 - j))
                             (map Vint (Zrepeat Int.zero j) ++ Zrepeat Vundef (17 - j)) (Zrepeat Vundef 16)) p;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k)).
  - entailer!.
  - unfold hra3_rpv. forward. forward.
    entailer!. apply derives_refl'. unfold hra3_rpv.
    assert (E: upd_Znth i (map Vint (Zrepeat Int.zero i) ++ Zrepeat Vundef (17 - i)) (Vint (Int.repr 0)) =
               map Vint (Zrepeat Int.zero (i + 1)) ++ Zrepeat Vundef (17 - (i + 1))) by list_solve.
    rewrite E. reflexivity.
  - forward_for_simple_bound 16 (EX j: Z,
      PROP ()
      LOCAL (temp C._p p; temp C._key k)
      SEP (data_at sh t_rpoly (hra3_rpv (map Vint (map hrp_u8 (sublist 0 j kbuf) ++ Zrepeat Int.zero (17 - j)))
                               (map Vint hrp_zero17)
                               (map Vubyte (sublist 16 (16 + j) kbuf) ++ Zrepeat Vundef (16 - j))) p;
           data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k)).
    + entailer!. apply derives_refl'. rewrite sublist_nil. unfold hrp_zero17.
      rewrite Z.sub_diag, app_nil_l. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r. reflexivity.
    + unfold hra3_rpv. forward.
      entailer!. apply hra3_rp_is_int_ubyte.
      rewrite Znth_map by lia.
      forward. forward.
      entailer!. apply hra3_rp_is_int_ubyte.
      rewrite Znth_map by lia.
      forward. entailer!.
      apply derives_refl'. unfold hra3_rpv.
      change (Vint (Int.repr (Byte.unsigned (Znth i kbuf)))) with (Vint (hrp_u8 (Znth i kbuf))).
      change (Vint (Int.repr (Byte.unsigned (Znth (16 + i) kbuf)))) with (Vubyte (Znth (16 + i) kbuf)).
      assert (E1: upd_Znth i (map Vint (map hrp_u8 (sublist 0 i kbuf) ++ Zrepeat Int.zero (17 - i)))
                    (Vint (hrp_u8 (Znth i kbuf))) =
                  map Vint (map hrp_u8 (sublist 0 (i + 1) kbuf) ++ Zrepeat Int.zero (17 - (i + 1))))
        by list_solve.
      assert (E2: upd_Znth i (map Vubyte (sublist 16 (16 + i) kbuf) ++ Zrepeat Vundef (16 - i))
                    (Vubyte (Znth (16 + i) kbuf)) =
                  map Vubyte (sublist 16 (16 + (i + 1)) kbuf) ++ Zrepeat Vundef (16 - (i + 1)))
        by list_solve.
      rewrite E1, E2. reflexivity.
    + unfold hra3_rpv.
      change (Zrepeat Int.zero (17 - 16)) with [Int.zero].
      change (Zrepeat Vundef (16 - 16)) with (@nil val). rewrite app_nil_r.
      assert (HR0: Zlength (map hrp_u8 (sublist 0 16 kbuf) ++ [Int.zero]) = 17)
        by (rewrite Zlength_app, Zlength_map, Zlength_sublist by lia; reflexivity).
      remember (map hrp_u8 (sublist 0 16 kbuf) ++ [Int.zero]) as R0 eqn:HR0e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR1: Zlength (hrp_mask 3 15 R0) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 3 15 R0) as R1 eqn:HR1e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR2: Zlength (hrp_mask 4 252 R1) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 4 252 R1) as R2 eqn:HR2e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR3: Zlength (hrp_mask 7 15 R2) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 7 15 R2) as R3 eqn:HR3e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR4: Zlength (hrp_mask 8 252 R3) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 8 252 R3) as R4 eqn:HR4e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR5: Zlength (hrp_mask 11 15 R4) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 11 15 R4) as R5 eqn:HR5e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR6: Zlength (hrp_mask 12 252 R5) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 12 252 R5) as R6 eqn:HR6e.
      forward. forward. rewrite hra3_rp_mask_map.
      assert (HR7: Zlength (hrp_mask 15 15 R6) = 17) by (rewrite hra3_rp_mask_len; lia).
      remember (hrp_mask 15 15 R6) as R7 eqn:HR7e.
      entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* rp_block                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hra3_rp_block_body : semax_body haead_V haead_Gprog C.f_rp_block rp_block_spec.
Proof.
  start_function.
  forward_for_simple_bound 16 (EX j: Z,
    PROP ()
    LOCAL (temp C._p p; temp C._m (offset_val i mp); lvar C._c (tarray tuint 17) v_c)
    SEP (data_at Tsh (tarray tuint 17) (map Vint (map hrp_u8 (sublist i (i + j) bs)) ++ Zrepeat Vundef (17 - j)) v_c;
         data_at sh t_rpoly (rpoly_val r h s) p;
         data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) mp)).
  - entailer!. rewrite sublist_nil. simpl app. apply derives_refl.
  - assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val i mp) (Vint (Int.repr i0))) =
                 field_address (tarray tuchar (Zlength bs)) [ArraySubsc (i + i0)] mp) as Ea.
    { entailer!. simpl. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia. }
    forward.
    { entailer!. apply hra3_rp_is_int_ubyte. }
    rewrite Znth_map by lia.
    forward. entailer!.
    apply derives_refl'. f_equal.
    change (Vint (Int.repr (Byte.unsigned (Znth (i + i0) bs)))) with (Vint (hrp_u8 (Znth (i + i0) bs))).
    list_solve.
  - forward.
    assert (Ec: upd_Znth 16 (map Vint (map hrp_u8 (sublist i (i + 16) bs)) ++ Zrepeat Vundef (17 - 16))
                  (Vint (Int.repr 1)) = map Vint (hrp_block_c (sublist i (i + 16) bs))).
    { unfold hrp_block_c. list_solve. }
    rewrite Ec.
    forward_call (sh, p, r, h, s, Tsh, v_c, hrp_block_c (sublist i (i + 16) bs)).
    { unfold hrp_block_c. list_solve. }
    entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* rp_final                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hra3_rp_select_len sv g n h :
  0 <= n -> Zlength (hrp_loop (hrp_select_step sv g) n h) = Zlength h.
Proof.
  intros Hn. apply (hra3_rp_loop_ind (fun t => Zlength t = Zlength h)); auto.
  intros b j Hj Hb. unfold hrp_select_step. rewrite Zlength_upd_Znth. exact Hb.
Qed.

(* an equation that entailer! does not substitute (it would compute the model) *)
Definition hra3_rp_is {A: Type} (x y: A) : Prop := x = y.
#[global] Opaque hra3_rp_is.

Lemma hra3_rp_is_intro {A: Type} (x y: A) : x = y -> hra3_rp_is x y.
Proof. intros E. exact E. Qed.

Lemma hra3_rp_is_elim {A: Type} (x y: A) : hra3_rp_is x y -> x = y.
Proof. intros E. exact E. Qed.

Lemma hra3_rp_u8_cast w : Vint (Int.zero_ext 8 w) = Vubyte (Byte.repr (Int.unsigned w)).
Proof.
  unfold Vubyte. f_equal.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 w)). rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma hra3_rp_u8_cast2 w :
  Vint (Int.zero_ext 8 (Int.zero_ext 8 w)) = Vubyte (Byte.repr (Int.unsigned w)).
Proof. rewrite Int.zero_ext_idem by lia. apply hra3_rp_u8_cast. Qed.

Lemma hra3_rp_final_h_eq h s :
  hrp_final_h h s =
  hrp_add (hrp_loop (hrp_select_step (Int.neg (Int.shru (Znth 16 (hrp_add h hrp_minusp)) (Int.repr 7))) h) 17
                    (hrp_add h hrp_minusp))
          (map hrp_u8 s ++ [Int.zero]).
Proof. reflexivity. Qed.

(* p->h as an array of its own, for the calls rp_add(p->h, ...) *)
Lemma hra3_rp_split sh p r h s :
  data_at sh t_rpoly (rpoly_val r h s) p =
  (field_at sh t_rpoly (DOT C._r) (map Vint r) p *
   data_at sh (tarray tuint 17) (map Vint h) (field_address t_rpoly (DOT C._h) p) *
   field_at sh t_rpoly (DOT C._s) (map Vubyte s) p)%logic.
Proof.
  unfold_data_at (data_at sh t_rpoly (rpoly_val r h s) p).
  rewrite (field_at_data_at sh t_rpoly (DOT C._h)). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hra3_rp_join sh p r h s :
  (field_at sh t_rpoly (DOT C._r) (map Vint r) p *
   data_at sh (tarray tuint 17) (map Vint h) (field_address t_rpoly (DOT C._h) p) *
   field_at sh t_rpoly (DOT C._s) (map Vubyte s) p)%logic |--
  data_at sh t_rpoly (rpoly_val r h s) p.
Proof. rewrite hra3_rp_split. apply derives_refl. Qed.

(* The two calls rp_add(p->h, ...) of rp_final as lemmas of their own: inside the body proof, the kernel
   check of a forward_call (and of the statements after it) took > 600 s at Qed; as separate lemmas, 1 s. *)
Definition hra3_rp_final_call1 : statement :=
  Scall None
    (Evar C._rp_add (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid cc_default))
    ((Efield (Ederef (Etempvar C._p (tptr (Tstruct C._rpoly noattr))) (Tstruct C._rpoly noattr)) C._h
       (tarray tuint 17)) :: (Evar C._x_prim_aead__minusp (tarray tuint 17)) :: nil).

Definition hra3_rp_final_call2 : statement :=
  Scall None
    (Evar C._rp_add (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid cc_default))
    ((Efield (Ederef (Etempvar C._p (tptr (Tstruct C._rpoly noattr))) (Tstruct C._rpoly noattr)) C._h
       (tarray tuint 17)) :: (Evar C._c (tarray tuint 17)) :: nil).

Lemma hra3_rp_final_call1_ok (Espec: OracleKind) sh p r h s v_c vj out v_g gv Fa Fb Fc :
  writable_share sh -> Zlength h = 17 -> field_compatible t_rpoly (DOT C._h) p ->
  semax (func_tycontext C.f_rp_final haead_V haead_Gprog nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (Fa; Fb; field_at sh t_rpoly (DOT C._r) (map Vint r) p;
          data_at sh (tarray tuint 17) (map Vint h) (field_address t_rpoly (DOT C._h) p);
          field_at sh t_rpoly (DOT C._s) (map Vubyte s) p; Fc;
          data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp)))
    hra3_rp_final_call1
    (normal_ret_assert
      (PROP ()
       LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
              lvar C._c (tarray tuint 17) v_c; gvars gv)
       SEP (data_at sh t_rpoly (rpoly_val r (hrp_add h hrp_minusp) s) p;
            data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp);
            Fa; Fb; Fc))).
Proof.
  intros SH Hh Fh.
  unfold hra3_rp_final_call1. abbreviate_semax.
  forward_call (sh, field_address t_rpoly (DOT C._h) p, h, Ers, gv C._x_prim_aead__minusp, hrp_minusp).
  sep_apply (hra3_rp_join sh p r (hrp_add h hrp_minusp) s).
  entailer!.
Qed.

Lemma hra3_rp_final_call2_ok (Espec: OracleKind) sh p r h2 s v_c cl vj out v_g gv Fa Fb Fc :
  writable_share sh -> Zlength h2 = 17 -> Zlength cl = 17 -> field_compatible t_rpoly (DOT C._h) p ->
  semax (func_tycontext C.f_rp_final haead_V haead_Gprog nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (field_at sh t_rpoly (DOT C._r) (map Vint r) p;
          data_at sh (tarray tuint 17) (map Vint h2) (field_address t_rpoly (DOT C._h) p);
          field_at sh t_rpoly (DOT C._s) (map Vubyte s) p; Fa; Fb;
          data_at Tsh (tarray tuint 17) (map Vint cl) v_c; Fc))
    hra3_rp_final_call2
    (normal_ret_assert
      (PROP ()
       LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
              lvar C._c (tarray tuint 17) v_c; gvars gv)
       SEP (data_at sh t_rpoly (rpoly_val r (hrp_add h2 cl) s) p; Fa; Fb;
            data_at Tsh (tarray tuint 17) (map Vint cl) v_c; Fc))).
Proof.
  intros SH Hh2 Hcl Fh.
  unfold hra3_rp_final_call2. abbreviate_semax.
  forward_call (sh, field_address t_rpoly (DOT C._h) p, h2, Tsh, v_c, cl).
  sep_apply (hra3_rp_join sh p r (hrp_add h2 cl) s).
  entailer!.
Qed.

(* rp_final after the first call, and its last loop: statements of the body *)
Definition hra3_rp_final_rest1 : statement :=
  match fn_body C.f_rp_final with Ssequence _ (Ssequence _ r) => r | _ => Sskip end.

Definition hra3_rp_final_rest2 : statement :=
  match hra3_rp_final_rest1 with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ r)))) => r | _ => Sskip end.

(* the output loop out[j] = (u8)p->h[j] and the end of the function *)
Lemma hra3_rp_final_tail2 (Espec: OracleKind) sh p r h s osh out gv v_g v_c h3 cl vj :
  writable_share sh -> writable_share osh -> Zlength s = 16 -> Zlength h3 = 17 ->
  hra3_rp_is (hrp_final_h h s) h3 ->
  semax (func_tycontext C.f_rp_final haead_V haead_Gprog nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (data_at sh t_rpoly (rpoly_val r h3 s) p;
          data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp);
          data_at Tsh (tarray tuint 17) (map Vint h) v_g;
          data_at Tsh (tarray tuint 17) (map Vint cl) v_c; data_at_ osh (tarray tuchar 16) out))
    hra3_rp_final_rest2
    (normal_ret_assert
      (PROP () RETURN () SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
          data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out; haead_globals gv) *
       stackframe_of C.f_rp_final)%logic).
Proof.
  intros SH SH0 Hs Hh3 Ef. apply hra3_rp_is_elim in Ef.
  unfold hra3_rp_final_rest2, hra3_rp_final_rest1. simpl fn_body. cbv match.
  abbreviate_semax.
  forward_for_simple_bound 16 (EX j: Z,
    PROP ()
    LOCAL (temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
           lvar C._c (tarray tuint 17) v_c; gvars gv)
    SEP (data_at sh t_rpoly (rpoly_val r h3 s) p;
         data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp);
         data_at Tsh (tarray tuint 17) (map Vint h) v_g;
         data_at Tsh (tarray tuint 17) (map Vint cl) v_c;
         data_at osh (tarray tuchar 16)
           (map Vubyte (map (fun w => Byte.repr (Int.unsigned w)) (sublist 0 j h3)) ++ Zrepeat Vundef (16 - j))
           out)).
  - entailer!.
  - unfold rpoly_val. forward. forward. entailer!.
    rewrite hra3_rp_u8_cast2. apply derives_refl'. f_equal. list_solve.
  - unfold haead_globals. rewrite Ef. unfold hrp_final_out. rewrite <- Ef.
    change (Zrepeat Vundef (16 - 16)) with (@nil val). rewrite app_nil_r.
    entailer!.
Qed.

(* from t'6 = p->h[16] to the second call *)
Lemma hra3_rp_final_tail1 (Espec: OracleKind) sh p r h s osh out gv v_g v_c h1 vj :
  writable_share sh -> writable_share osh -> Zlength r = 17 -> Zlength h = 17 -> Zlength s = 16 ->
  field_compatible t_rpoly (DOT C._h) p -> Zlength h1 = 17 -> hra3_rp_is h1 (hrp_add h hrp_minusp) ->
  semax (func_tycontext C.f_rp_final haead_V haead_Gprog nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (data_at sh t_rpoly (rpoly_val r h1 s) p;
          data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp);
          data_at Tsh (tarray tuint 17) (map Vint h) v_g;
          data_at_ Tsh (tarray tuint 17) v_c; data_at_ osh (tarray tuchar 16) out))
    hra3_rp_final_rest1
    (normal_ret_assert
      (PROP () RETURN () SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
          data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out; haead_globals gv) *
       stackframe_of C.f_rp_final)%logic).
Proof.
  intros SH SH0 H H0 Hs Fh Hh1 Eh1.
  unfold hra3_rp_final_rest1. simpl fn_body. cbv match.
  abbreviate_semax.
  forward. forward.
  remember (Int.neg (Int.shru (Znth 16 h1) (Int.repr 7))) as sv eqn:Esv. apply hra3_rp_is_intro in Esv.
  forward_for_simple_bound 17 (EX j: Z,
    PROP ()
    LOCAL (temp C._s (Vint sv); temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
           lvar C._c (tarray tuint 17) v_c; gvars gv)
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_loop (hrp_select_step sv h) j h1) s) p;
         data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp);
         data_at Tsh (tarray tuint 17) (map Vint h) v_g;
         data_at_ Tsh (tarray tuint 17) v_c;
         data_at_ osh (tarray tuchar 16) out)).
  - entailer!. rewrite (hra3_rp_is_elim _ _ Esv). reflexivity.
  - assert (Hl: Zlength (hrp_loop (hrp_select_step sv h) i h1) = 17)
      by (rewrite hra3_rp_select_len by lia; exact Hh1).
    unfold rpoly_val. forward. forward. forward. forward.
    rewrite hrp_loop_succ by lia. unfold hrp_select_step at 2. rewrite upd_Znth_map. unfold rpoly_val.
    entailer!.
  - assert (Hh2: Zlength (hrp_loop (hrp_select_step sv h) 17 h1) = 17)
      by (rewrite hra3_rp_select_len by lia; exact Hh1).
    remember (hrp_loop (hrp_select_step sv h) 17 h1) as h2 eqn:Eh2. apply hra3_rp_is_intro in Eh2.
    forward_for_simple_bound 16 (EX j: Z,
      PROP ()
      LOCAL (temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
             lvar C._c (tarray tuint 17) v_c; gvars gv)
      SEP (data_at sh t_rpoly (rpoly_val r h2 s) p;
           data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_prim_aead__minusp);
           data_at Tsh (tarray tuint 17) (map Vint h) v_g;
           data_at Tsh (tarray tuint 17) (map Vint (map hrp_u8 (sublist 0 j s)) ++ Zrepeat Vundef (17 - j)) v_c;
           data_at_ osh (tarray tuchar 16) out)).
    + entailer!.
    + unfold rpoly_val. forward.
      { entailer!. apply hra3_rp_is_int_ubyte. }
      rewrite Znth_map by lia.
      forward. entailer!.
      apply derives_refl'. f_equal.
      change (Vint (Int.repr (Byte.unsigned (Znth i s)))) with (Vint (hrp_u8 (Znth i s))).
      list_solve.
    + forward.
      assert (Ec: upd_Znth 16 (map Vint (map hrp_u8 (sublist 0 16 s)) ++ Zrepeat Vundef (17 - 16))
                    (Vint (Int.repr 0)) = map Vint (map hrp_u8 s ++ [Int.zero])).
      { rewrite sublist_same by lia. list_solve. }
      rewrite Ec. rewrite hra3_rp_split. Intros.
      eapply semax_seq';
        [ apply hra3_rp_final_call2_ok; auto; rewrite Zlength_app, Zlength_map, Hs; reflexivity | ].
      assert (Hh3: Zlength (hrp_add h2 (map hrp_u8 s ++ [Int.zero])) = 17) by (rewrite hra3_rp_add_len; lia).
      assert (Ef: hra3_rp_is (hrp_final_h h s) (hrp_add h2 (map hrp_u8 s ++ [Int.zero]))).
      { apply hra3_rp_is_intro.
        apply hra3_rp_is_elim in Eh1, Esv, Eh2. subst h2 sv h1. apply hra3_rp_final_h_eq. }
      exact (hra3_rp_final_tail2 Espec sh p r h s osh out gv v_g v_c _ _ _ SH SH0 Hs Hh3 Ef).
Qed.

Lemma hra3_rp_final_body : semax_body haead_V haead_Gprog C.f_rp_final rp_final_spec.
Proof.
  start_function.
  assert_PROP (Zlength s = 16) as Hs.
  { rewrite hra3_rp_split. entailer!. rewrite value_fits_eq in H9. simpl in H9. destruct H9 as [H9 _].
    rewrite <- (Zlength_map _ _ Vubyte s). exact H9. }
  assert_PROP (field_compatible t_rpoly (DOT C._h) p) as Fh.
  { entailer!. }
  forward_for_simple_bound 17 (EX j: Z,
    PROP ()
    LOCAL (temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g; lvar C._c (tarray tuint 17) v_c;
           gvars gv)
    SEP (data_at Tsh (tarray tuint 17) (map Vint (sublist 0 j h) ++ Zrepeat Vundef (17 - j)) v_g;
         data_at_ Tsh (tarray tuint 17) v_c;
         data_at sh t_rpoly (rpoly_val r h s) p;
         data_at_ osh (tarray tuchar 16) out; haead_globals gv)).
  - entailer!.
  - forward. forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - rewrite sublist_same by lia. change (Zrepeat Vundef (17 - 17)) with (@nil val). rewrite app_nil_r.
    rewrite hra3_rp_split. unfold haead_globals. Intros.
    eapply semax_seq'; [ apply hra3_rp_final_call1_ok; auto | ].
    assert (Hh1: Zlength (hrp_add h hrp_minusp) = 17) by (rewrite hra3_rp_add_len; lia).
    exact (hra3_rp_final_tail1 Espec sh p r h s osh out gv v_g v_c _ _ SH SH0 H H0 Hs Fh Hh1
             (hra3_rp_is_intro _ _ eq_refl)).
Qed.

Lemma hra3_rp_bodies :
  semax_body haead_V haead_Gprog C.f_rp_add rp_add_spec /\
  semax_body haead_V haead_Gprog C.f_rp_init rp_init_spec /\
  semax_body haead_V haead_Gprog C.f_rp_block rp_block_spec /\
  semax_body haead_V haead_Gprog C.f_rp_final rp_final_spec.
Proof.
  split; [exact hra3_rp_add_body |].
  split; [exact hra3_rp_init_body |].
  split; [exact hra3_rp_block_body | exact hra3_rp_final_body].
Qed.
