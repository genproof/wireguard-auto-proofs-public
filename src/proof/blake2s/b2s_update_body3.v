(* the body of blake2s_update against blake2s_update_spec3 (chunk length <= PTRDIFF_MAX), in the
   context of the new interface (b2s_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_update3_model.

#[local] Existing Instance Blake2s.CS.

Lemma b2s_u3_split_bytes {cs: compspecs} sh n a (vals: list val) p :
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> Zlength vals = n ->
  data_at sh (tarray tuchar n) vals p =
  (data_at sh (tarray tuchar a) (sublist 0 a vals) p *
   data_at sh (tarray tuchar (n - a)) (sublist a n vals) (offset_val a p))%logic.
Proof.
  intros Hfc Ha Hv. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar sh n a) by auto.
  rewrite field_address0_offset.
  - simpl. f_equal. f_equal. f_equal. lia.
  - auto with field_compatible.
Qed.

Lemma b2s_u3_fc_offset {cs: compspecs} n a p :
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n ->
  field_compatible (tarray tuchar (n - a)) [] (offset_val a p).
Proof.
  intros Hfc Ha. destruct (proj1 (field_compatible_Tarray_split tuchar a n p Ha) Hfc) as [_ H2].
  rewrite field_address0_offset in H2.
  - simpl in H2. replace (0 + 1 * a) with a in H2 by lia. exact H2.
  - auto with field_compatible.
Qed.

Lemma b2s_u3_fc_prefix {cs: compspecs} n a p :
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n ->
  field_compatible (tarray tuchar a) [] p.
Proof.
  intros Hfc Ha. exact (proj1 (proj1 (field_compatible_Tarray_split tuchar a n p Ha) Hfc)).
Qed.

(* nblocks = DIV_ROUND_UP(inlen, 64): no wrap for inlen <= PTRDIFF_MAX *)
Lemma b2s_u3_nblocks r :
  64 < r <= Int64.max_signed ->
  Int64.divu (Int64.sub (Int64.add (Int64.repr r) (Int64.repr (Int.signed (Int.repr 64))))
                        (Int64.repr (Int.signed (Int.repr 1))))
             (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr ((r - 1) / 64 + 1).
Proof.
  intros Hr. change (Int.signed (Int.repr 64)) with 64. change (Int.signed (Int.repr 1)) with 1.
  unfold Int64.divu, Int64.sub, Int64.add.
  rewrite (Int64.unsigned_repr r), (Int64.unsigned_repr 64) by rep_lia.
  rewrite (Int64.unsigned_repr (r + 64)), (Int64.unsigned_repr 1) by rep_lia.
  rewrite (Int64.unsigned_repr (r + 64 - 1)) by rep_lia.
  f_equal. replace (r + 64 - 1) with ((r - 1) + 1 * 64) by lia.
  rewrite Z.div_add by lia. reflexivity.
Qed.

Lemma b2s_u3_split3_bytes {cs: compspecs} sh a c (vals: list val) p :
  field_compatible (tarray tuchar 64) [] p -> 0 <= a -> 0 <= c -> a + c <= 64 -> Zlength vals = 64 ->
  data_at sh (tarray tuchar 64) vals p =
  (data_at sh (tarray tuchar a) (sublist 0 a vals) p *
   data_at sh (tarray tuchar c) (sublist a (a + c) vals) (offset_val a p) *
   data_at sh (tarray tuchar (64 - (a + c))) (sublist (a + c) 64 vals) (offset_val (a + c) p))%logic.
Proof.
  intros Hfc Ha Hc Hac Hv.
  rewrite (b2s_u3_split_bytes sh 64 a) by (auto; lia).
  assert (Hfc2: field_compatible (tarray tuchar (64 - a)) [] (offset_val a p)).
  { apply b2s_u3_fc_offset; auto; lia. }
  rewrite (b2s_u3_split_bytes sh (64 - a) c _ (offset_val a p)) by (auto; try list_solve; lia).
  rewrite offset_offset_val. rewrite sepcon_assoc. f_equal. f_equal.
  - f_equal. list_solve.
  - replace (64 - a - c) with (64 - (a + c)) by lia. f_equal. list_solve.
Qed.

Lemma body_blake2s_update3 :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_blake2s_update blake2s_update_spec3.
Proof.
start_function.
unfold blake2s_state. Intros junk.
set (s := b2s_stream key msg) in *.
destruct (b2s_u3_decomp s) as (Hk0 & Es & HP & Hl64 & Hl1).
set (k := b2s_nfull s) in *. set (last := b2s_lastblock s) in *.
set (P := sublist 0 (64*k) s) in *.
set (h0 := b2s_h0 (Zlength key) outlen).
change (b2s_h_nonfinal (Zlength key) outlen s) with (b2s_blocks h0 0 P).
set (L := Zlength last) in *. assert (HL0: 0 <= L) by apply Zlength_nonneg.
set (n := Zlength data) in *. assert (Hn0: 0 <= n) by apply Zlength_nonneg.
assert_PROP (field_compatible t_blake2s_ctx [] ctx) by entailer!.
unfold_data_at (data_at _ _ _ ctx).
cbn [b2s_ctx_val fst snd].
forward.
forward.
forward_if.
{ assert (En: n = 0).
  { match goal with Hz: Int64.repr n = Int64.zero |- _ =>
      apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia; exact Hz end. }
  assert (Ed: data = []) by (apply Zlength_nil_inv; auto).
  forward.
  rewrite app_nil_r. unfold blake2s_state. Exists junk.
  change (b2s_h_nonfinal (Zlength key) outlen (b2s_stream key msg)) with (b2s_blocks h0 0 P).
  subst last L k P h0.
  entailer!.
  unfold_data_at (data_at _ _ _ ctx). cbn [b2s_ctx_val fst snd]. cancel. }
assert (Hn1: 1 <= n).
{ assert (n <> 0); [|lia]. intro E.
  match goal with Hz: Int64.repr n <> Int64.zero |- _ => apply Hz; rewrite E; reflexivity end. }
rewrite b2s_bytes_nonempty by (unfold n in *; lia). change (Zlength data) with n.
assert (Efill: Int.unsigned (Int.sub (Int.repr 64) (Int.repr L)) = 64 - L)
  by (unfold Int.sub; rewrite (Int.unsigned_repr 64), (Int.unsigned_repr L), Int.unsigned_repr by rep_lia; lia).
rewrite Efill.
assert_PROP (field_compatible (tarray tuchar n) [] d) by entailer!.
set (bp := field_address t_blake2s_ctx (DOT _buf) ctx).
assert (Hbuf: forall v, field_at sh t_blake2s_ctx (DOT _buf) v ctx = data_at sh (tarray tuchar 64) v bp)
  by (intros; rewrite field_at_data_at; reflexivity).
change WgNoise.blake2s.code._buf with _buf. rewrite Hbuf.
assert_PROP (field_compatible (tarray tuchar 64) [] bp) by entailer!.
assert (Ebp: bp = offset_val 48 ctx)
  by (unfold bp; rewrite field_address_offset by auto with field_compatible; reflexivity).
forward_if (@exp (environ -> mpred) _ Z (fun off => @exp (environ -> mpred) _ Z (fun kc =>
  @exp (environ -> mpred) _ (list byte) (fun Pc => @exp (environ -> mpred) _ (list byte) (fun bc =>
  @exp (environ -> mpred) _ (list val) (fun junkc =>
  PROP (s ++ data = Pc ++ bc ++ sublist off n data; (Zlength Pc = 64 * kc)%Z; (0 <= kc)%Z;
        (0 <= off < n)%Z; (Zlength bc = 0 \/ Zlength bc + (n - off) <= 64)%Z; (Zlength bc <= 64)%Z;
        (Zlength junkc = 64 - Zlength bc)%Z)
  LOCAL (temp WgNoise.blake2s.code._in (offset_val off d);
         temp WgNoise.blake2s.code._inlen (Vlong (Int64.repr (n - off)));
         gvars gv; temp WgNoise.blake2s.code._ctx ctx)
  SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_blocks h0 0 Pc)) ctx;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (64 * kc)); Vint (b2s_t1 (64 * kc))] ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint Int.zero; Vint Int.zero] ctx;
       data_at sh (tarray tuchar 64) (map Vubyte bc ++ junkc) bp;
       field_at sh t_blake2s_ctx (DOT _buflen) (Vint (Int.repr (Zlength bc))) ctx;
       field_at sh t_blake2s_ctx (DOT _outlen) (Vint (Int.repr outlen)) ctx;
       data_at dsh (tarray tuchar off) (map Vubyte (sublist 0 off data)) d;
       data_at dsh (tarray tuchar (n - off)) (map Vubyte (sublist off n data)) (offset_val off d);
       blake2s_globals gv))))))).
{ (* the chunk overflows the buffer: fill it, compress it *)
  forward.
  rewrite (b2s_u3_split_bytes sh 64 L) by (auto; unfold L in *; list_solve).
  replace (sublist 0 L (map Vubyte last ++ junk)) with (map Vubyte last) by (unfold L in *; list_solve).
  replace (sublist L 64 (map Vubyte last ++ junk)) with junk by (unfold L in *; list_solve).
  rewrite (b2s_u3_split_bytes dsh n (64 - L) (map Vubyte data) d) by (auto; unfold n in *; list_solve).
  rewrite !sublist_map.
  sep_apply (data_at_data_at_ sh (tarray tuchar (64 - L)) junk (offset_val L bp)).
  forward_call (sh, dsh, offset_val L bp, d, 64 - L, sublist 0 (64 - L) data).
  { entailer!. simpl. rewrite Ebp, offset_offset_val.
    destruct ctx; try contradiction; destruct d; try contradiction; reflexivity. }
  { unfold n in *; list_solve. }
  set (B0 := last ++ sublist 0 (64 - L) data).
  assert (HB0: Zlength B0 = 64) by (unfold B0, n, L in *; list_solve).
  gather_SEP (data_at sh (tarray tuchar L) _ bp) (data_at sh (tarray tuchar (64 - L)) _ (offset_val L bp)).
  replace_SEP 0 (data_at sh (tarray tuchar 64) (map Vubyte B0) bp).
  { assert (EB: data_at sh (tarray tuchar 64) (map Vubyte B0) bp =
      (data_at sh (tarray tuchar L) (map Vubyte last) bp *
       data_at sh (tarray tuchar (64 - L)) (map Vubyte (sublist 0 (64 - L) data)) (offset_val L bp))%logic).
    { rewrite (b2s_u3_split_bytes sh 64 L (map Vubyte B0) bp) by (auto; list_solve).
      f_equal; f_equal; unfold B0, L, n in *; list_solve. }
    rewrite EB. entailer!. }
  forward_call (sh, ctx, b2s_blocks h0 0 P, 64 * k, Int.zero, sh, bp, 1, 64, B0, gv).
  { apply b2s_u3_blocks_len. }
  rewrite (b2s_u3_blocks_n _ _ B0 1) by lia.
  replace (b2s_blocks (b2s_blocks h0 0 P) (64 * k) B0) with (b2s_blocks h0 0 (P ++ B0))
    by (rewrite b2s_u3_blocks_app by (rewrite HP, Z.mul_comm, Z_mod_mult; reflexivity); f_equal; lia).
  replace (64 * k + 1 * 64) with (64 * (k + 1)) by lia.
  change (64 * 1) with 64.
  forward. forward. forward.
  Exists (64 - L) (k + 1) (P ++ B0) (@nil byte) (map Vubyte B0).
  entailer!.
  split3; [rewrite Es; unfold B0, n in *; list_solve | rewrite Zlength_app, HP, HB0; lia | list_solve]. }
{ (* the chunk fits in the buffer *)
  rewrite (b2s_u3_split_bytes dsh n 0 (map Vubyte data) d) by (auto; try lia; unfold n in *; list_solve).
  rewrite !sublist_map.
  forward.
  Exists 0 k P last junk.
  entailer!.
  unfold n; rewrite sublist_same by lia. rewrite Es, app_assoc. reflexivity. }
Intros off kc Pc bc junkc.
forward_if (@exp (environ -> mpred) _ Z (fun off => @exp (environ -> mpred) _ Z (fun kc =>
  @exp (environ -> mpred) _ (list byte) (fun Pc => @exp (environ -> mpred) _ (list byte) (fun bc =>
  @exp (environ -> mpred) _ (list val) (fun junkc =>
  PROP (s ++ data = Pc ++ bc ++ sublist off n data; (Zlength Pc = 64 * kc)%Z; (0 <= kc)%Z;
        (0 <= off < n)%Z; (Zlength bc + (n - off) <= 64)%Z;
        (Zlength junkc = 64 - Zlength bc)%Z)
  LOCAL (temp WgNoise.blake2s.code._in (offset_val off d);
         temp WgNoise.blake2s.code._inlen (Vlong (Int64.repr (n - off)));
         gvars gv; temp WgNoise.blake2s.code._ctx ctx)
  SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_blocks h0 0 Pc)) ctx;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (64 * kc)); Vint (b2s_t1 (64 * kc))] ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint Int.zero; Vint Int.zero] ctx;
       data_at sh (tarray tuchar 64) (map Vubyte bc ++ junkc) bp;
       field_at sh t_blake2s_ctx (DOT _buflen) (Vint (Int.repr (Zlength bc))) ctx;
       field_at sh t_blake2s_ctx (DOT _outlen) (Vint (Int.repr outlen)) ctx;
       data_at dsh (tarray tuchar off) (map Vubyte (sublist 0 off data)) d;
       data_at dsh (tarray tuchar (n - off)) (map Vubyte (sublist off n data)) (offset_val off d);
       blake2s_globals gv))))))).
{ (* the whole blocks of the rest but the last one, straight from the input *)
  match goal with Hgt: Int64.unsigned (Int64.repr 64) < _ |- _ =>
    rewrite !Int64.unsigned_repr in Hgt by rep_lia; rename Hgt into Hr64 end.
  assert (Hbc0: Zlength bc = 0) by (pose proof (Zlength_nonneg bc); lia).
  apply Zlength_nil_inv in Hbc0. subst bc.
  forward.
  set (m := (n - off - 1) / 64).
  assert (Hm: 1 <= m /\ 64 * m < n - off <= 64 * m + 64).
  { unfold m. pose proof (Z.div_mod (n - off - 1) 64 ltac:(lia)).
    pose proof (Z.mod_pos_bound (n - off - 1) 64 ltac:(lia)).
    assert (1 <= (n - off - 1) / 64) by (apply Z.div_le_lower_bound; lia). lia. }
  rewrite b2s_u3_nblocks by rep_lia. fold m.
  assert (Hfc_off: field_compatible (tarray tuchar (n - off)) [] (offset_val off d))
    by (apply b2s_u3_fc_offset; auto; lia).
  rewrite (b2s_u3_split_bytes dsh (n - off) (64 * m) (map Vubyte (sublist off n data)) (offset_val off d))
    by (auto; try lia; unfold n in *; list_solve).
  replace (sublist 0 (64 * m) (map Vubyte (sublist off n data)))
    with (map Vubyte (sublist off (off + 64 * m) data)) by (unfold n in *; list_solve).
  replace (sublist (64 * m) (n - off) (map Vubyte (sublist off n data)))
    with (map Vubyte (sublist (off + 64 * m) n data)) by (unfold n in *; list_solve).
  replace (n - off - 64 * m) with (n - (off + 64 * m)) by lia.
  rewrite offset_offset_val.
  Intros.
  forward_call (sh, ctx, b2s_blocks h0 0 Pc, 64 * kc, Int.zero, dsh, offset_val off d, m, 64,
                sublist off (off + 64 * m) data, gv).
  { entailer!. simpl. replace (m + 1 - 1) with m by lia. reflexivity. }
  { split; [apply b2s_u3_blocks_len | unfold n in *; list_solve]. }
  set (M := sublist off (off + 64 * m) data).
  rewrite (b2s_u3_blocks_n _ _ M m) by (try lia; unfold M, n in *; list_solve).
  replace (b2s_blocks (b2s_blocks h0 0 Pc) (64 * kc) M) with (b2s_blocks h0 0 (Pc ++ M))
    by (rewrite b2s_u3_blocks_app by (rewrite H8, Z.mul_comm, Z_mod_mult; reflexivity); f_equal; lia).
  replace (64 * kc + m * 64) with (64 * (kc + m)) by lia.
  forward. forward.
  assert (EM: data_at dsh (tarray tuchar (off + 64 * m)) (map Vubyte (sublist 0 (off + 64 * m) data)) d =
    (data_at dsh (tarray tuchar off) (map Vubyte (sublist 0 off data)) d *
     data_at dsh (tarray tuchar (64 * m)) (map Vubyte M) (offset_val off d))%logic).
  { rewrite (b2s_u3_split_bytes dsh (off + 64 * m) off)
      by (try (apply (b2s_u3_fc_prefix n); auto); try lia; unfold n in *; list_solve).
    replace (off + 64 * m - off) with (64 * m) by lia.
    f_equal; f_equal; unfold M, n in *; list_solve. }
  Exists (off + 64 * m) (kc + m) (Pc ++ M) (@nil byte) junkc.
  rewrite EM. entailer!.
  replace (m + 1 - 1) with m by lia.
  refine (conj _ (conj _ (conj eq_refl _))).
  - match goal with Hs: b2s_stream key msg ++ data = _ |- _ => rewrite Hs end.
    unfold M, n in *; list_solve.
  - rewrite Zlength_app, H8. unfold M. rewrite Zlength_sublist by (unfold n in *; lia). lia.
  - do 2 f_equal; lia. }
{ (* the rest fits in the buffer *)
  match goal with Hle: Int64.unsigned (Int64.repr 64) >= _ |- _ =>
    rewrite !Int64.unsigned_repr in Hle by rep_lia; rename Hle into Hr64 end.
  forward. Exists off kc Pc bc junkc. entailer!. }
clear dependent off. clear dependent bc. clear dependent kc. clear dependent Pc. clear dependent junkc.
Intros off kc Pc bc junkc.
forward.
set (Lc := Zlength bc) in *.
assert (HLc0: 0 <= Lc) by apply Zlength_nonneg.
rewrite (b2s_u3_split3_bytes sh Lc (n - off) (map Vubyte bc ++ junkc) bp) by (auto; try lia; unfold Lc in *; list_solve).
replace (sublist 0 Lc (map Vubyte bc ++ junkc)) with (map Vubyte bc) by (unfold Lc in *; list_solve).
replace (sublist Lc (Lc + (n - off)) (map Vubyte bc ++ junkc)) with (sublist 0 (n - off) junkc)
  by (unfold Lc in *; list_solve).
replace (sublist (Lc + (n - off)) 64 (map Vubyte bc ++ junkc)) with (sublist (n - off) (64 - Lc) junkc)
  by (unfold Lc in *; list_solve).
sep_apply (data_at_data_at_ sh (tarray tuchar (n - off)) (sublist 0 (n - off) junkc) (offset_val Lc bp)).
forward_call (sh, dsh, offset_val Lc bp, offset_val off d, n - off, sublist off n data).
{ entailer!. simpl. rewrite Ebp, offset_offset_val.
  destruct ctx; try contradiction; reflexivity. }
{ unfold n in *; list_solve. }
forward.
forward.
assert (Ebl: Int64.Z_mod_modulus (Int64.Z_mod_modulus (Int.unsigned (Int.repr Lc)) + Int64.Z_mod_modulus (n - off))
             = Lc + (n - off)).
{ rewrite Int.unsigned_repr by rep_lia. rewrite !Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small Lc), (Z.mod_small (n - off)), Z.mod_small by rep_lia. reflexivity. }
rewrite Ebl.
set (rest := bc ++ sublist off n data).
assert (Hrest: Zlength rest = Lc + (n - off))
  by (unfold rest; rewrite Zlength_app, Zlength_sublist by (unfold n; lia); fold Lc; lia).
assert (Es': b2s_stream key (msg ++ data) = Pc ++ rest).
{ unfold b2s_stream. rewrite app_assoc. change (b2s_keyblock key ++ msg) with s.
  match goal with Hs: s ++ data = _ |- _ => rewrite Hs end. reflexivity. }
destruct (b2s_u3_split _ _ _ Es' ltac:(rewrite H8, Z.mul_comm, Z_mod_mult; reflexivity) ltac:(lia))
  as (Hnf & Hlb & Hpre).
unfold blake2s_state. unfold b2s_h_nonfinal.
rewrite Hpre, Hlb, Hnf, H8, Z.mul_comm, Z.div_mul by lia. rewrite Z.mul_comm.
Exists (sublist (n - off) (64 - Lc) junkc).
unfold_data_at (data_at _ _ _ ctx). cbn [b2s_ctx_val fst snd].
change WgNoise.blake2s.code._buf with _buf. rewrite Hbuf.
rewrite (b2s_u3_split3_bytes sh Lc (n - off) (map Vubyte rest ++ sublist (n - off) (64 - Lc) junkc) bp)
  by (auto; try lia; unfold rest, Lc, n in *; list_solve).
rewrite (b2s_u3_split_bytes dsh n off (map Vubyte data) d) by (auto; try lia; unfold n in *; list_solve).
set (J := sublist (n - off) (64 - Lc) junkc).
assert (HJ: Zlength J = 64 - (Lc + (n - off))) by (unfold J; rewrite Zlength_sublist by lia; lia).
replace (sublist 0 Lc (map Vubyte rest ++ J)) with (map Vubyte bc) by (unfold rest, Lc, n in *; list_solve).
replace (sublist Lc (Lc + (n - off)) (map Vubyte rest ++ J)) with (map Vubyte (sublist off n data))
  by (unfold rest, Lc, n in *; list_solve).
replace (sublist (Lc + (n - off)) 64 (map Vubyte rest ++ J)) with J by (unfold rest, Lc, n in *; list_solve).
rewrite !sublist_map, Hrest.
entailer!.
Qed.
