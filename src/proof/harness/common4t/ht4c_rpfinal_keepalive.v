(* rp_final of common.h for law transport_keepalive (its static minusp is
   x_transport_keepalive__minusp): haead_rp_body3_a.v's proof with the varspecs ht4c_Vmp mp and the Gprog ht4c_G0 mp
   (ht4c_spec.v), mp = x_transport_keepalive__minusp. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4c_rp_body.
Require WgNoise.harness.x_transport_keepalive.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Module C := WgNoise.harness.x_transport_keepalive.code.

(* The two calls rp_add(p->h, ...) of rp_final as lemmas of their own: inside the body proof, the kernel
   check of a forward_call (and of the statements after it) took > 600 s at Qed; as separate lemmas, 1 s. *)
Definition ht4ck_rp_final_call1 : statement :=
  Scall None
    (Evar C._rp_add (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid cc_default))
    ((Efield (Ederef (Etempvar C._p (tptr (Tstruct C._rpoly noattr))) (Tstruct C._rpoly noattr)) C._h
       (tarray tuint 17)) :: (Evar C._x_transport_keepalive__minusp (tarray tuint 17)) :: nil).

Definition ht4ck_rp_final_call2 : statement :=
  Scall None
    (Evar C._rp_add (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid cc_default))
    ((Efield (Ederef (Etempvar C._p (tptr (Tstruct C._rpoly noattr))) (Tstruct C._rpoly noattr)) C._h
       (tarray tuint 17)) :: (Evar C._c (tarray tuint 17)) :: nil).

Lemma ht4ck_rp_final_call1_ok (Espec: OracleKind) sh p r h s v_c vj out v_g gv Fa Fb Fc :
  writable_share sh -> Zlength h = 17 -> field_compatible t_rpoly (DOT C._h) p ->
  semax (func_tycontext C.f_rp_final (ht4c_Vmp C._x_transport_keepalive__minusp) (ht4c_G0 C._x_transport_keepalive__minusp) nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (Fa; Fb; field_at sh t_rpoly (DOT C._r) (map Vint r) p;
          data_at sh (tarray tuint 17) (map Vint h) (field_address t_rpoly (DOT C._h) p);
          field_at sh t_rpoly (DOT C._s) (map Vubyte s) p; Fc;
          data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp)))
    ht4ck_rp_final_call1
    (normal_ret_assert
      (PROP ()
       LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
              lvar C._c (tarray tuint 17) v_c; gvars gv)
       SEP (data_at sh t_rpoly (rpoly_val r (hrp_add h hrp_minusp) s) p;
            data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp);
            Fa; Fb; Fc))).
Proof.
  intros SH Hh Fh.
  unfold ht4ck_rp_final_call1. abbreviate_semax.
  forward_call (sh, field_address t_rpoly (DOT C._h) p, h, Ers, gv C._x_transport_keepalive__minusp, hrp_minusp).
  sep_apply (ht4cr_rp_join sh p r (hrp_add h hrp_minusp) s).
  entailer!.
Qed.

Lemma ht4ck_rp_final_call2_ok (Espec: OracleKind) sh p r h2 s v_c cl vj out v_g gv Fa Fb Fc :
  writable_share sh -> Zlength h2 = 17 -> Zlength cl = 17 -> field_compatible t_rpoly (DOT C._h) p ->
  semax (func_tycontext C.f_rp_final (ht4c_Vmp C._x_transport_keepalive__minusp) (ht4c_G0 C._x_transport_keepalive__minusp) nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (field_at sh t_rpoly (DOT C._r) (map Vint r) p;
          data_at sh (tarray tuint 17) (map Vint h2) (field_address t_rpoly (DOT C._h) p);
          field_at sh t_rpoly (DOT C._s) (map Vubyte s) p; Fa; Fb;
          data_at Tsh (tarray tuint 17) (map Vint cl) v_c; Fc))
    ht4ck_rp_final_call2
    (normal_ret_assert
      (PROP ()
       LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
              lvar C._c (tarray tuint 17) v_c; gvars gv)
       SEP (data_at sh t_rpoly (rpoly_val r (hrp_add h2 cl) s) p; Fa; Fb;
            data_at Tsh (tarray tuint 17) (map Vint cl) v_c; Fc))).
Proof.
  intros SH Hh2 Hcl Fh.
  unfold ht4ck_rp_final_call2. abbreviate_semax.
  forward_call (sh, field_address t_rpoly (DOT C._h) p, h2, Tsh, v_c, cl).
  sep_apply (ht4cr_rp_join sh p r (hrp_add h2 cl) s).
  entailer!.
Qed.

(* rp_final after the first call, and its last loop: statements of the body *)
Definition ht4ck_rp_final_rest1 : statement :=
  match fn_body C.f_rp_final with Ssequence _ (Ssequence _ r) => r | _ => Sskip end.

Definition ht4ck_rp_final_rest2 : statement :=
  match ht4ck_rp_final_rest1 with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ r)))) => r | _ => Sskip end.

(* the output loop out[j] = (u8)p->h[j] and the end of the function *)
Lemma ht4ck_rp_final_tail2 (Espec: OracleKind) sh p r h s osh out gv v_g v_c h3 cl vj :
  writable_share sh -> writable_share osh -> Zlength s = 16 -> Zlength h3 = 17 ->
  ht4cr_rp_is (hrp_final_h h s) h3 ->
  semax (func_tycontext C.f_rp_final (ht4c_Vmp C._x_transport_keepalive__minusp) (ht4c_G0 C._x_transport_keepalive__minusp) nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (data_at sh t_rpoly (rpoly_val r h3 s) p;
          data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp);
          data_at Tsh (tarray tuint 17) (map Vint h) v_g;
          data_at Tsh (tarray tuint 17) (map Vint cl) v_c; data_at_ osh (tarray tuchar 16) out))
    ht4ck_rp_final_rest2
    (normal_ret_assert
      (PROP () RETURN () SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
          data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out; ht4_minusp C._x_transport_keepalive__minusp gv) *
       stackframe_of C.f_rp_final)%logic).
Proof.
  intros SH SH0 Hs Hh3 Ef. apply ht4cr_rp_is_elim in Ef.
  unfold ht4ck_rp_final_rest2, ht4ck_rp_final_rest1. simpl fn_body. cbv match.
  abbreviate_semax.
  forward_for_simple_bound 16 (EX j: Z,
    PROP ()
    LOCAL (temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
           lvar C._c (tarray tuint 17) v_c; gvars gv)
    SEP (data_at sh t_rpoly (rpoly_val r h3 s) p;
         data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp);
         data_at Tsh (tarray tuint 17) (map Vint h) v_g;
         data_at Tsh (tarray tuint 17) (map Vint cl) v_c;
         data_at osh (tarray tuchar 16)
           (map Vubyte (map (fun w => Byte.repr (Int.unsigned w)) (sublist 0 j h3)) ++ Zrepeat Vundef (16 - j))
           out)).
  - entailer!.
  - unfold rpoly_val. forward. forward. entailer!.
    rewrite ht4cr_rp_u8_cast2. apply derives_refl'. f_equal. list_solve.
  - unfold ht4_minusp. rewrite Ef. unfold hrp_final_out. rewrite <- Ef.
    change (Zrepeat Vundef (16 - 16)) with (@nil val). rewrite app_nil_r.
    entailer!.
Qed.

(* from t'6 = p->h[16] to the second call *)
Lemma ht4ck_rp_final_tail1 (Espec: OracleKind) sh p r h s osh out gv v_g v_c h1 vj :
  writable_share sh -> writable_share osh -> Zlength r = 17 -> Zlength h = 17 -> Zlength s = 16 ->
  field_compatible t_rpoly (DOT C._h) p -> Zlength h1 = 17 -> ht4cr_rp_is h1 (hrp_add h hrp_minusp) ->
  semax (func_tycontext C.f_rp_final (ht4c_Vmp C._x_transport_keepalive__minusp) (ht4c_G0 C._x_transport_keepalive__minusp) nil)
    (PROP ()
     LOCAL (temp C._j vj; temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
            lvar C._c (tarray tuint 17) v_c; gvars gv)
     SEP (data_at sh t_rpoly (rpoly_val r h1 s) p;
          data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp);
          data_at Tsh (tarray tuint 17) (map Vint h) v_g;
          data_at_ Tsh (tarray tuint 17) v_c; data_at_ osh (tarray tuchar 16) out))
    ht4ck_rp_final_rest1
    (normal_ret_assert
      (PROP () RETURN () SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
          data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out; ht4_minusp C._x_transport_keepalive__minusp gv) *
       stackframe_of C.f_rp_final)%logic).
Proof.
  intros SH SH0 H H0 Hs Fh Hh1 Eh1.
  unfold ht4ck_rp_final_rest1. simpl fn_body. cbv match.
  abbreviate_semax.
  forward. forward.
  remember (Int.neg (Int.shru (Znth 16 h1) (Int.repr 7))) as sv eqn:Esv. apply ht4cr_rp_is_intro in Esv.
  forward_for_simple_bound 17 (EX j: Z,
    PROP ()
    LOCAL (temp C._s (Vint sv); temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
           lvar C._c (tarray tuint 17) v_c; gvars gv)
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_loop (hrp_select_step sv h) j h1) s) p;
         data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp);
         data_at Tsh (tarray tuint 17) (map Vint h) v_g;
         data_at_ Tsh (tarray tuint 17) v_c;
         data_at_ osh (tarray tuchar 16) out)).
  - entailer!. rewrite (ht4cr_rp_is_elim _ _ Esv). reflexivity.
  - assert (Hl: Zlength (hrp_loop (hrp_select_step sv h) i h1) = 17)
      by (rewrite ht4cr_rp_select_len by lia; exact Hh1).
    unfold rpoly_val. forward. forward. forward. forward.
    rewrite hrp_loop_succ by lia. unfold hrp_select_step at 2. rewrite upd_Znth_map. unfold rpoly_val.
    entailer!.
  - assert (Hh2: Zlength (hrp_loop (hrp_select_step sv h) 17 h1) = 17)
      by (rewrite ht4cr_rp_select_len by lia; exact Hh1).
    remember (hrp_loop (hrp_select_step sv h) 17 h1) as h2 eqn:Eh2. apply ht4cr_rp_is_intro in Eh2.
    forward_for_simple_bound 16 (EX j: Z,
      PROP ()
      LOCAL (temp C._p p; temp C._out out; lvar C._g (tarray tuint 17) v_g;
             lvar C._c (tarray tuint 17) v_c; gvars gv)
      SEP (data_at sh t_rpoly (rpoly_val r h2 s) p;
           data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv C._x_transport_keepalive__minusp);
           data_at Tsh (tarray tuint 17) (map Vint h) v_g;
           data_at Tsh (tarray tuint 17) (map Vint (map hrp_u8 (sublist 0 j s)) ++ Zrepeat Vundef (17 - j)) v_c;
           data_at_ osh (tarray tuchar 16) out)).
    + entailer!.
    + unfold rpoly_val. forward.
      { entailer!. apply ht4cr_rp_is_int_ubyte. }
      rewrite Znth_map by lia.
      forward. entailer!.
      apply derives_refl'. f_equal.
      change (Vint (Int.repr (Byte.unsigned (Znth i s)))) with (Vint (hrp_u8 (Znth i s))).
      list_solve.
    + forward.
      assert (Ec: upd_Znth 16 (map Vint (map hrp_u8 (sublist 0 16 s)) ++ Zrepeat Vundef (17 - 16))
                    (Vint (Int.repr 0)) = map Vint (map hrp_u8 s ++ [Int.zero])).
      { rewrite sublist_same by lia. list_solve. }
      rewrite Ec. rewrite ht4cr_rp_split. Intros.
      eapply semax_seq';
        [ apply ht4ck_rp_final_call2_ok; auto; rewrite Zlength_app, Zlength_map, Hs; reflexivity | ].
      assert (Hh3: Zlength (hrp_add h2 (map hrp_u8 s ++ [Int.zero])) = 17) by (rewrite ht4cr_rp_add_len; lia).
      assert (Ef: ht4cr_rp_is (hrp_final_h h s) (hrp_add h2 (map hrp_u8 s ++ [Int.zero]))).
      { apply ht4cr_rp_is_intro.
        apply ht4cr_rp_is_elim in Eh1, Esv, Eh2. subst h2 sv h1. apply ht4cr_rp_final_h_eq. }
      exact (ht4ck_rp_final_tail2 Espec sh p r h s osh out gv v_g v_c _ _ _ SH SH0 Hs Hh3 Ef).
Qed.

Lemma ht4ck_rp_final_body : semax_body (ht4c_Vmp C._x_transport_keepalive__minusp) (ht4c_G0 C._x_transport_keepalive__minusp) C.f_rp_final (rp_final_spec_of C._x_transport_keepalive__minusp).
Proof.
  start_function.
  assert_PROP (Zlength s = 16) as Hs.
  { rewrite ht4cr_rp_split. entailer!. rewrite value_fits_eq in H9. simpl in H9. destruct H9 as [H9 _].
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
         data_at_ osh (tarray tuchar 16) out; ht4_minusp C._x_transport_keepalive__minusp gv)).
  - entailer!.
  - forward. forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - rewrite sublist_same by lia. change (Zrepeat Vundef (17 - 17)) with (@nil val). rewrite app_nil_r.
    rewrite ht4cr_rp_split. unfold ht4_minusp. Intros.
    eapply semax_seq'; [ apply ht4ck_rp_final_call1_ok; auto | ].
    assert (Hh1: Zlength (hrp_add h hrp_minusp) = 17) by (rewrite ht4cr_rp_add_len; lia).
    exact (ht4ck_rp_final_tail1 Espec sh p r h s osh out gv v_g v_c _ _ SH SH0 H H0 Hs Fh Hh1
             (ht4cr_rp_is_intro _ _ eq_refl)).
Qed.

