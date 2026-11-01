(* body of ref_poly1305 (harness/common.h) of law prim_poly1305: = poly1305_tag, by the rp_* specs and
   the proven math of hp1305_ref_math3.v / hp1305_ref_pf3.v / hp1305_ref_initr3.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

Module C := WgNoise.harness.x_prim_poly1305.code.

Require Import WgNoise.proof.harness.prim_poly1305.hp1305_refmath3.
(* proven math (no unproved dependency): hpf_inv_zero, hpr_acc_block, hpr_acc_last, hpr_tag *)
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_ref_pf3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_ref_math3.

(* ---------------------------------------------------------------------- *)
(* The statements of ref_poly1305: pos = 0; rp_init; while; if; rp_final   *)

(* ---------------------------------------------------------------------- *)

Definition hp1305_ref_init_call : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence ?r _) => exact r end).
Definition hp1305_ref_while : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence _ (Ssequence ?r _)) => exact r end).
Definition hp1305_ref_loop_body : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence _ (Ssequence (Swhile _ ?r) _)) => exact r end).
Definition hp1305_ref_block_call : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence _ (Ssequence (Swhile _ (Ssequence ?r _)) _)) => exact r end).
Definition hp1305_ref_if : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _))) => exact r end).
Definition hp1305_ref_mul_call : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence
          (Sifthenelse _ (Ssequence _ (Ssequence _ (Ssequence _ ?r))) _) _))) => exact r end).
Definition hp1305_ref_final_call : statement :=
  ltac:(let b := eval cbv delta [C.f_ref_poly1305 fn_body] beta iota in (fn_body C.f_ref_poly1305) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r))) => exact r end).

Lemma hp1305_ref_init_r_len key : 16 <= Zlength key -> Zlength (hrp_init_r key) = 17.
Proof. intros. unfold hrp_init_r, hrp_mask. list_solve. Qed.

(* rp_init(&p, key) *)
Lemma hp1305_ref_init_call_ok (Espec: OracleKind) p ksh k key vpos vc gv vout m vlen Fa Fb Fc Fd :
  readable_share ksh -> Zlength key = 32 ->
  semax (func_tycontext C.f_ref_poly1305 hp1305_V hp1305_Gprog nil)
    (PROP () LOCAL (temp C._pos vpos; lvar C._c (tarray tuint 17) vc;
      lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out vout; temp C._key k; temp C._m m;
      temp C._len vlen)
    SEP (Fa; data_at_ Tsh (Tstruct C._rpoly noattr) p; Fb;
      data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k; Fc; Fd))
    hp1305_ref_init_call
    (normal_ret_assert
      (PROP () LOCAL (temp C._pos vpos; lvar C._c (tarray tuint 17) vc;
        lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out vout; temp C._key k; temp C._m m;
        temp C._len vlen)
      SEP (data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) hrp_zero17 (hrp_init_s key)) p;
        data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k; Fa; Fb; Fc; Fd))).
Proof.
  intros SH0 H.
  unfold hp1305_ref_init_call. abbreviate_semax.
  forward_call (Tsh, p, ksh, k, key).
  entailer!.
Qed.

(* rp_block(&p, m + pos) *)
Lemma hp1305_ref_block_call_ok (Espec: OracleKind) p r h s msh m msg pos vc vout vk gv Fa Fb Fc Fd :
  readable_share msh -> 0 <= pos -> pos + 16 <= Zlength msg -> Zlength msg <= Int64.max_unsigned ->
  Zlength r = 17 -> Zlength h = 17 ->
  semax (func_tycontext C.f_ref_poly1305 hp1305_V hp1305_Gprog nil)
    (PROP () LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) vc;
      lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out vout; temp C._key vk; temp C._m m;
      temp C._len (Vlong (Int64.repr (Zlength msg))))
    SEP (Fa; data_at Tsh t_rpoly (rpoly_val r h s) p; Fb; Fc;
      data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m; Fd))
    hp1305_ref_block_call
    (normal_ret_assert
      (PROP () LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) vc;
        lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out vout; temp C._key vk; temp C._m m;
        temp C._len (Vlong (Int64.repr (Zlength msg))))
      SEP (data_at Tsh t_rpoly (rpoly_val r (hrp_block r h (sublist pos (pos + 16) msg)) s) p;
        data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m; Fa; Fb; Fc; Fd))).
Proof.
  intros SH1 Hp Hp16 Hmax Hr Hh.
  unfold hp1305_ref_block_call. abbreviate_semax.
  forward_call (Tsh, p, r, h, s, msh, m, msg, pos).
  { entailer!. }
  entailer!.
Qed.

(* rp_mul(&p, c) *)
Lemma hp1305_ref_mul_call_ok (Espec: OracleKind) p r h s vc c vj vpos vout vk m vlen gv Fb Fc Fd Fe :
  Zlength r = 17 -> Zlength h = 17 -> Zlength c = 17 ->
  semax (func_tycontext C.f_ref_poly1305 hp1305_V hp1305_Gprog nil)
    (PROP () LOCAL (temp C._j vj; temp C._pos vpos; lvar C._c (tarray tuint 17) vc;
      lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out vout; temp C._key vk; temp C._m m;
      temp C._len vlen)
    SEP (data_at Tsh (tarray tuint 17) (map Vint c) vc; data_at Tsh t_rpoly (rpoly_val r h s) p;
      Fb; Fc; Fd; Fe))
    hp1305_ref_mul_call
    (normal_ret_assert
      (PROP () LOCAL (temp C._j vj; temp C._pos vpos; lvar C._c (tarray tuint 17) vc;
        lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out vout; temp C._key vk; temp C._m m;
        temp C._len vlen)
      SEP (data_at Tsh t_rpoly (rpoly_val r (hrp_mul r h c) s) p;
        data_at Tsh (tarray tuint 17) (map Vint c) vc; Fb; Fc; Fd; Fe))).
Proof.
  intros Hr Hh Hc.
  unfold hp1305_ref_mul_call. abbreviate_semax.
  forward_call (Tsh, p, r, h, s, Tsh, vc, c).
  entailer!.
Qed.

(* rp_final(&p, out) *)
Lemma hp1305_ref_final_call_ok (Espec: OracleKind) p r h s vc osh out vk m vlen gv Fa Fb Fc :
  writable_share osh -> Zlength r = 17 -> Zlength h = 17 ->
  semax (func_tycontext C.f_ref_poly1305 hp1305_V hp1305_Gprog nil)
    (PROP () LOCAL (lvar C._c (tarray tuint 17) vc;
      lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out out; temp C._key vk; temp C._m m;
      temp C._len vlen)
    SEP (Fa; data_at Tsh t_rpoly (rpoly_val r h s) p; data_at_ osh (tarray tuchar 16) out; Fb; Fc;
      hp1305_globals gv))
    hp1305_ref_final_call
    (normal_ret_assert
      (PROP () LOCAL (lvar C._c (tarray tuint 17) vc;
        lvar C._p (Tstruct C._rpoly noattr) p; gvars gv; temp C._out out; temp C._key vk; temp C._m m;
        temp C._len vlen)
      SEP (data_at Tsh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
        data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out; hp1305_globals gv;
        Fa; Fb; Fc))).
Proof.
  intros SH Hr Hh.
  unfold hp1305_ref_final_call. abbreviate_semax.
  forward_call (Tsh, p, r, h, s, osh, out, gv).
  entailer!.
Qed.

(* the loop over the full blocks *)
Lemma hp1305_ref_while_ok (Espec: OracleKind) osh out ksh k key msh m msg gv v_p v_c vpos :
  readable_share msh -> Zlength key = 32 -> Zlength msg <= Int64.max_unsigned ->
  vpos = Vlong (Int64.repr 0) ->
  semax (func_tycontext C.f_ref_poly1305 hp1305_V hp1305_Gprog nil)
    (PROP () LOCAL (temp C._pos vpos; lvar C._c (tarray tuint 17) v_c;
      lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
      temp C._len (Vlong (Int64.repr (Zlength msg))))
    SEP (data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) hrp_zero17 (hrp_init_s key)) v_p;
      data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
      data_at_ Tsh (tarray tuint 17) v_c; data_at_ osh (tarray tuchar 16) out;
      data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m; hp1305_globals gv))
    hp1305_ref_while
    (normal_ret_assert (EX pos: Z, EX h: list int,
      PROP (0 <= pos <= Zlength msg; Zlength msg - pos < 16; pos mod 16 = 0; hrp_inv h;
            hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 pos msg))
      LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) v_c;
        lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
        temp C._len (Vlong (Int64.repr (Zlength msg))))
      SEP (data_at_ Tsh (tarray tuint 17) v_c;
        data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h (hrp_init_s key)) v_p;
        data_at_ osh (tarray tuchar 16) out;
        data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
        data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
        hp1305_globals gv))%assert).
Proof.
  intros SH1 H H0 Hvpos. subst vpos.
  assert (Hr: Zlength (hrp_init_r key) = 17) by (apply hp1305_ref_init_r_len; lia).
  unfold hp1305_ref_while. abbreviate_semax.
  forward_while (EX pos: Z, EX h: list int,
    PROP (0 <= pos <= Zlength msg; pos mod 16 = 0; hrp_inv h;
          hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 pos msg))
    LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) v_c;
      lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
      temp C._len (Vlong (Int64.repr (Zlength msg))))
    SEP (data_at_ Tsh (tarray tuint 17) v_c;
      data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h (hrp_init_s key)) v_p;
      data_at_ osh (tarray tuchar 16) out;
      data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
      data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
      hp1305_globals gv))%assert.
  { Exists 0 hrp_zero17. destruct hpf_inv_zero as [Hi Hv]. entailer!. }
  { entailer!. }
  { eapply semax_seq'.
    { apply hp1305_ref_block_call_ok; auto; try lia. apply H3. }
    unfold MORE_COMMANDS, abbreviate. forward.
    destruct (hpr_acc_block key msg pos h) as [Hi' Hv']; auto; try lia.
    Exists (pos + 16, hrp_block (hrp_init_r key) h (sublist pos (pos + 16) msg)).
    entailer!. split; [lia | rewrite Zplus_mod, H2; reflexivity]. }
  forward. Exists pos h. entailer!.
Qed.

(* the last partial block *)
Lemma hp1305_ref_if_ok (Espec: OracleKind) osh out ksh k key msh m msg gv v_p v_c pos h :
  readable_share msh -> Zlength key = 32 -> Zlength msg <= Int64.max_unsigned ->
  0 <= pos <= Zlength msg -> Zlength msg - pos < 16 -> pos mod 16 = 0 -> hrp_inv h ->
  hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 pos msg) ->
  semax (func_tycontext C.f_ref_poly1305 hp1305_V hp1305_Gprog nil)
    (PROP () LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) v_c;
      lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
      temp C._len (Vlong (Int64.repr (Zlength msg))))
    SEP (data_at_ Tsh (tarray tuint 17) v_c;
      data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h (hrp_init_s key)) v_p;
      data_at_ osh (tarray tuchar 16) out;
      data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
      data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
      hp1305_globals gv))
    hp1305_ref_if
    (normal_ret_assert (EX h': list int,
      PROP (hrp_inv h'; hrp_val h' mod p1305_p = p1305_acc (p1305_r key) 0 msg)
      LOCAL (lvar C._c (tarray tuint 17) v_c;
        lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
        temp C._len (Vlong (Int64.repr (Zlength msg))))
      SEP (data_at_ Tsh (tarray tuint 17) v_c;
        data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h' (hrp_init_s key)) v_p;
        data_at_ osh (tarray tuchar 16) out;
        data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
        data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
        hp1305_globals gv))%assert).
Proof.
  intros SH1 H H0 H1 HRE H2 H3 H4.
  assert (Hr: Zlength (hrp_init_r key) = 17) by (apply hp1305_ref_init_r_len; lia).
  assert (Hsub: Int64.sub (Int64.repr (Zlength msg)) (Int64.repr pos) = Int64.repr (Zlength msg - pos))
    by (unfold Int64.sub; rewrite (Int64.unsigned_repr (Zlength msg)), (Int64.unsigned_repr pos) by rep_lia;
        reflexivity).
  unfold hp1305_ref_if. abbreviate_semax.
  forward_if (EX h': list int,
    PROP (hrp_inv h'; hrp_val h' mod p1305_p = p1305_acc (p1305_r key) 0 msg)
    LOCAL (lvar C._c (tarray tuint 17) v_c;
      lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
      temp C._len (Vlong (Int64.repr (Zlength msg))))
    SEP (data_at_ Tsh (tarray tuint 17) v_c;
      data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h' (hrp_init_s key)) v_p;
      data_at_ osh (tarray tuchar 16) out;
      data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
      data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
      hp1305_globals gv))%assert.
  { rewrite Hsub, !Int64.unsigned_repr in H5 by rep_lia.
    forward_for_simple_bound 17 (EX j: Z,
      PROP () LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) v_c;
        lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
        temp C._len (Vlong (Int64.repr (Zlength msg))))
      SEP (data_at Tsh (tarray tuint 17) (Zrepeat (Vint Int.zero) j ++ Zrepeat Vundef (17 - j)) v_c;
        data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h (hrp_init_s key)) v_p;
        data_at_ osh (tarray tuchar 16) out;
        data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
        data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
        hp1305_globals gv))%assert.
    { entailer!. }
    { forward. entailer!. apply derives_refl'. f_equal. list_solve. }
    forward_for_simple_bound (Zlength msg - pos) (EX j: Z,
      PROP () LOCAL (temp C._pos (Vlong (Int64.repr pos)); lvar C._c (tarray tuint 17) v_c;
        lvar C._p (Tstruct C._rpoly noattr) v_p; gvars gv; temp C._out out; temp C._key k; temp C._m m;
        temp C._len (Vlong (Int64.repr (Zlength msg))))
      SEP (data_at Tsh (tarray tuint 17)
             (map (fun b => Vint (hrp_u8 b)) (sublist pos (pos + j) msg) ++ Zrepeat (Vint Int.zero) (17 - j)) v_c;
        data_at Tsh t_rpoly (rpoly_val (hrp_init_r key) h (hrp_init_s key)) v_p;
        data_at_ osh (tarray tuchar 16) out;
        data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k;
        data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
        hp1305_globals gv))%assert.
    { entailer!. apply derives_refl'. f_equal. list_solve. }
    { forward.
      { entailer!. unfold Vubyte; simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward. entailer!. apply derives_refl'. f_equal.
      replace (force_val _) with (Vint (hrp_u8 (Znth (pos + i) msg))) by reflexivity.
      list_solve. }
    forward.
    replace (pos + (Zlength msg - pos)) with (Zlength msg) by lia.
    remember (sublist pos (Zlength msg) msg) as rest eqn:Erest.
    assert (Hrl: Zlength rest = Zlength msg - pos) by (subst rest; list_solve).
    replace (upd_Znth _ _ _) with (map Vint (hp_last_c rest)) by (unfold hp_last_c; list_solve).
    destruct (hpr_acc_last key msg pos h) as [Hi' Hv']; auto; try lia.
    rewrite <- Erest in Hi', Hv'.
    eapply ConseqFacts.semax_post''.
    2: { apply hp1305_ref_mul_call_ok; auto. apply H3. unfold hp_last_c; list_solve. }
    Exists (hrp_mul (hrp_init_r key) h (hp_last_c rest)).
    entailer!. }
  { rewrite Hsub, !Int64.unsigned_repr in H5 by rep_lia.
    assert (pos = Zlength msg) by lia. subst pos.
    forward. Exists h. rewrite sublist_same in H4 by lia. entailer!. }
Qed.

Lemma hp1305_ref_body :
  semax_body hp1305_V hp1305_Gprog C.f_ref_poly1305 ref_poly1305_spec.
Proof.
  start_function.
  forward.
  replace_SEP 3 (data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) k) by (rewrite H; entailer!).
  eapply semax_seq'.
  { apply hp1305_ref_init_call_ok; auto. }
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_seq'.
  { apply hp1305_ref_while_ok; auto. }
  Intros pos h.
  eapply semax_seq'.
  { apply hp1305_ref_if_ok; auto. }
  Intros h'.
  assert (Hr: Zlength (hrp_init_r key) = 17) by (apply hp1305_ref_init_r_len; lia).
  eapply ConseqFacts.semax_post''.
  2: { apply hp1305_ref_final_call_ok; auto. apply H6. }
  rewrite (hpr_tag key msg h') by auto. rewrite H.
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!.
Qed.
