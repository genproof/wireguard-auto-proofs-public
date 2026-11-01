(* the body of blake2s_final in the context b2s_Gprog5 (the helper lemmas are those of
   b2s_final_body3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_zero_ctx.
Require Import WgNoise.proof.blake2s.b2s_final_zero.
Require Import WgNoise.proof.blake2s.b2s_final_body3.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma body_blake2s_final :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_blake2s_final blake2s_final_spec.
Proof.
start_function.
unfold blake2s_state. Intros junk.
set (s := b2s_stream key msg) in *.
set (last := b2s_lastblock s) in *.
set (hn := b2s_h_nonfinal (Zlength key) outlen s) in *.
assert_PROP (field_compatible t_blake2s_ctx [] ctx) by entailer!.
destruct (b2s_final_last_len s) as (Hn0 & Hns & Hl64).
fold last in Hns, Hl64.
unfold_data_at (data_at _ _ _ ctx).
cbn [b2s_ctx_val fst snd].
forward.
forward_call (sh, ctx, [Vint Int.zero; Vint Int.zero]).
forward.
forward.
pose proof (Zlength_nonneg last).
set (L := Zlength last) in *.
set (bp := field_address t_blake2s_ctx (DOT _buf) ctx).
assert (Hbuf: field_at sh t_blake2s_ctx (DOT _buf) (map Vubyte last ++ junk) ctx =
              data_at sh (tarray tuchar 64) (map Vubyte last ++ junk) bp)
  by (rewrite field_at_data_at; reflexivity).
change WgNoise.blake2s.code._buf with _buf. rewrite Hbuf; clear Hbuf.
rewrite (split2_data_at_Tarray_tuchar sh 64 L) by (list_solve || lia).
replace (sublist 0 L (map Vubyte last ++ junk)) with (map Vubyte last) by list_solve.
replace (sublist L 64 (map Vubyte last ++ junk)) with junk by list_solve.
Intros.
assert (Ebp: bp = offset_val 48 ctx) by (unfold bp; rewrite field_address_offset by auto with field_compatible; reflexivity).
assert (Ebp2: field_address0 (tarray tuchar 64) (SUB L) bp = offset_val (48+L) ctx).
{ rewrite field_address0_offset. rewrite Ebp. simpl. rewrite offset_offset_val. f_equal. lia.
  unfold bp. apply field_compatible0_cons. split. auto.
  exact (field_compatible_app [] t_blake2s_ctx (DOT _buf) ctx ltac:(simpl app; auto with field_compatible)). }
change (Tarray tuchar 64 noattr) with (tarray tuchar 64). rewrite Ebp2.
forward_call (sh, offset_val (48 + L) ctx, 0, 64 - L).
rewrite <- Ebp2.
gather_SEP (data_at sh (Tarray tuchar L noattr) _ bp) (data_at sh (tarray tuchar (64-L)) _ _).
replace_SEP 0 (data_at sh (tarray tuchar 64) (map Vubyte (last ++ Zrepeat Byte.zero (64 - L))) bp).
{ unfold L in *. entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh 64 (Zlength last)) by list_solve.
  replace (sublist 0 (Zlength last) (map Vubyte (last ++ Zrepeat Byte.zero (64 - Zlength last))))
    with (map Vubyte last) by list_solve.
  replace (sublist (Zlength last) 64 (map Vubyte (last ++ Zrepeat Byte.zero (64 - Zlength last))))
    with (Zrepeat (Vubyte (Byte.repr 0)) (64 - Zlength last)) by list_solve.
  cancel. }
forward.
rewrite upd_Znth0.
forward_call (sh, ctx, hn, 64 * b2s_nfull s, Int.mone, sh, bp, 1, L, last ++ Zrepeat Byte.zero (64 - L), gv).
{ split. apply b2s_final_h_nonfinal_len. list_solve. }
set (blk := last ++ Zrepeat Byte.zero (64 - L)).
assert (Hblk: Zlength blk = 64) by (unfold blk; list_solve).
set (hf := b2s_compress_block hn blk (Zlength s) Int.mone).
assert (Ehf: b2s_compress_n (Z.to_nat 1) hn (64 * b2s_nfull s) Int.mone L blk = hf).
{ cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add b2s_compress_n]. unfold hf.
  rewrite sublist_same by lia. rewrite Hns. reflexivity. }
rewrite Ehf. replace (64 * b2s_nfull s + 1 * L) with (Zlength s) by lia.
set (dig := b2s_out outlen hf).
assert (Edig: blake2s key outlen msg = dig) by reflexivity.
assert (Hdig: Zlength dig = outlen) by (unfold dig, b2s_out; rewrite Zlength_map, Zlength_upto; lia).

forward.
forward_loop
  (@exp (environ -> mpred) _ Z (fun i =>
   PROP (0 <= i <= outlen)
   LOCAL (temp WgNoise.blake2s.code._i (Vint (Int.repr i)); gvars gv; temp WgNoise.blake2s.code._ctx ctx;
          temp WgNoise.blake2s.code._out out)
   SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint hf) ctx;
        field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (Zlength s)); Vint (b2s_t1 (Zlength s))] ctx;
        field_at sh t_blake2s_ctx (DOT _f) [Vint Int.mone; Vint Int.zero] ctx;
        data_at sh (tarray tuchar (64 * 1)) (map Vubyte blk) bp;
        blake2s_globals gv;
        field_at sh t_blake2s_ctx (DOT _buflen) (Vint (Int.repr L)) ctx;
        field_at sh t_blake2s_ctx (DOT _outlen) (Vint (Int.repr outlen)) ctx;
        data_at osh (tarray tuchar outlen) (map Vubyte (sublist 0 i dig) ++ Zrepeat Vundef (outlen - i)) out)))
  continue:
  (@exp (environ -> mpred) _ Z (fun i =>
   PROP (0 <= i < outlen)
   LOCAL (temp WgNoise.blake2s.code._i (Vint (Int.repr i)); gvars gv; temp WgNoise.blake2s.code._ctx ctx;
          temp WgNoise.blake2s.code._out out)
   SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint hf) ctx;
        field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (Zlength s)); Vint (b2s_t1 (Zlength s))] ctx;
        field_at sh t_blake2s_ctx (DOT _f) [Vint Int.mone; Vint Int.zero] ctx;
        data_at sh (tarray tuchar (64 * 1)) (map Vubyte blk) bp;
        blake2s_globals gv;
        field_at sh t_blake2s_ctx (DOT _buflen) (Vint (Int.repr L)) ctx;
        field_at sh t_blake2s_ctx (DOT _outlen) (Vint (Int.repr outlen)) ctx;
        data_at osh (tarray tuchar outlen) (map Vubyte (sublist 0 (i + 1) dig) ++ Zrepeat Vundef (outlen - (i + 1))) out)))
  break:
  (PROP ()
   LOCAL (gvars gv; temp WgNoise.blake2s.code._ctx ctx)
   SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint hf) ctx;
        field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (Zlength s)); Vint (b2s_t1 (Zlength s))] ctx;
        field_at sh t_blake2s_ctx (DOT _f) [Vint Int.mone; Vint Int.zero] ctx;
        data_at sh (tarray tuchar (64 * 1)) (map Vubyte blk) bp;
        blake2s_globals gv;
        field_at sh t_blake2s_ctx (DOT _buflen) (Vint (Int.repr L)) ctx;
        field_at sh t_blake2s_ctx (DOT _outlen) (Vint (Int.repr outlen)) ctx;
        data_at osh (tarray tuchar outlen) (map Vubyte dig) out)).
{ Exists 0. entailer!. simpl app. apply derives_refl. }
{ Intros i. forward. forward_if.
  { assert (Hi4: 0 <= i / 4 < 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    assert (Hsh := b2s_final_shift_amount i ltac:(rep_lia)).
    pose proof (Z.mod_pos_bound i 4 ltac:(lia)).
    forward. forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    Exists i. entailer!.
    change (let (q, _) := Z.div_eucl i 4 in q) with (i / 4).
    rewrite Int.zero_ext_idem, b2s_final_zero_ext_Vubyte by lia.
    rewrite <- (b2s_final_Znth_out outlen) by lia.
    apply derives_refl'. f_equal. list_solve. }
  { forward. entailer!. apply derives_refl'. f_equal. list_solve. } }
{ Intros i. forward. Exists (i + 1). entailer!. }
pose proof (b2s_final_fc120 ctx H2) as Hfc120.
gather_SEP (field_at _ _ (DOT _h) _ ctx) (field_at _ _ (DOT _t) _ ctx) (field_at _ _ (DOT _f) _ ctx)
  (data_at sh (tarray tuchar (64 * 1)) _ bp) (field_at _ _ (DOT _buflen) _ ctx)
  (field_at _ _ (DOT _outlen) _ ctx).
replace_SEP 0 (data_at_ sh (tarray tuchar 120) ctx).
{ entailer!.
  rewrite <- (memory_block_data_at_ sh (tarray tuchar 120)) by exact Hfc120.
  change (sizeof (tarray tuchar 120)) with (sizeof t_blake2s_ctx).
  eapply derives_trans; [| apply data_at__memory_block_cancel].
  eapply derives_trans; [| apply (data_at_data_at_ sh t_blake2s_ctx
     (b2s_ctx_val (b2s_compress_block hn blk (Zlength s) Int.mone) (Zlength s) Int.mone
        (map Vubyte blk) (Zlength last) outlen))].
  unfold_data_at (data_at _ _ _ ctx). cbn [b2s_ctx_val fst snd].
  rewrite (field_at_data_at sh t_blake2s_ctx (DOT _buf)). cancel. }
forward_call (sh, ctx, 120).
sep_apply (b2s_final_zero_ctx sh ctx); auto.
entailer!.
Qed.
