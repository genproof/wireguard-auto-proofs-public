(* law transport_order: main's segment L2 (body statements 9..13): the nonce, the header stores, the ciphertext (authentic: malloc pt,
   NULL -> 3 frees + break, nondet_bytes, chacha20poly1305_encrypt, free pt, kind 1 flips a byte; kind 3: random).
   States and the cut: ht4o_main_defs.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.harness.transport_order.ht4o_main_defs.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

Lemma ht4oL2_splice_len (i: Z) (l: list byte) (c: list val) :
  0 <= i -> i + Zlength l <= Zlength c -> Zlength (haead_splice i l c) = Zlength c.
Proof. intros. unfold haead_splice. list_solve. Qed.

Lemma ht4oL2_l32 (w: int) : Zlength (le32_bytes w) = 4.
Proof. reflexivity. Qed.

Lemma ht4oL2_l64 (z: Z) : Zlength (le64_bytes z) = 8.
Proof. reflexivity. Qed.

Lemma ht4oL2_hdr (l1 l2 l3: list byte) (E: Z) :
  Zlength l1 = 4 -> Zlength l2 = 4 -> Zlength l3 = 8 -> 0 <= E ->
  haead_splice 8 l3 (haead_splice 4 l2 (haead_splice 0 l1 (Zrepeat Vundef (16 + E)))) =
  map Vubyte (l1 ++ l2 ++ l3) ++ Zrepeat Vundef E.
Proof. intros. unfold haead_splice. list_solve. Qed.

Lemma ht4oL2_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (l1 ++ l2) p =
  (data_at sh (tarray tuchar n1) l1 p * data_at sh (tarray tuchar n2) l2 (offset_val n1 p))%logic.
Proof.
  intros H1 H2 Hn Hf. subst n1 n2 n.
  rewrite (split2_data_at_Tarray_app (Zlength l1) (Zlength l1 + Zlength l2) sh tuchar l1 l2);
    [| reflexivity | exact (ltac:(lia) : Zlength (A:=val) l2 = Zlength l1 + Zlength l2 - Zlength l1)].
  replace (Zlength l1 + Zlength l2 - Zlength l1) with (Zlength l2) by lia.
  rewrite field_address0_offset.
  2: { pose proof (Zlength_nonneg l1); pose proof (Zlength_nonneg l2). auto with field_compatible. }
  simpl nested_field_offset. f_equal. f_equal. f_equal. simpl. lia.
Qed.

Lemma ht4oL2_merge sh n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 ->
  field_compatible (tarray tuchar (n1 + n2)) [] p ->
  (data_at sh (tarray tuchar n1) l1 p * data_at sh (tarray tuchar n2) l2 (offset_val n1 p))%logic |--
  data_at sh (tarray tuchar (n1 + n2)) (l1 ++ l2) p.
Proof. intros. rewrite (ht4oL2_split sh (n1 + n2) n1 n2) by auto. apply derives_refl. Qed.

Lemma ht4oL2_free_pre (n: Z) (v: list val) (p: val) : isptr p ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic |--
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.
Proof.
  intros Hp. destruct p; try contradiction. rewrite if_false by discriminate.
  apply sepcon_derives; [apply derives_refl | apply data_at_data_at_].
Qed.

Lemma ht4oL2_prim_nil (sh: share) (p: val) : prim_bytes sh [] p = emp.
Proof. reflexivity. Qed.

Lemma ht4oL2_prim (sh: share) (l: list byte) (p: val) :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma ht4oL2_prim_back (sh: share) (l: list byte) (p: val) :
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic
  |-- data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. rewrite <- ht4oL2_prim. apply derives_refl. Qed.

Lemma ht4oL2_ze8 (w: int) : Vint (Int.zero_ext 8 w) = Vubyte (Byte.repr (Int.unsigned w)).
Proof.
  unfold Vubyte. f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 w)).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma ht4oL2_bytes_Vubyte (bs: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; [reflexivity |]. simpl. rewrite IHForall. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma ht4oL2_flip (hdr: list val) (c: list byte) (j: Z) (x: byte) :
  Zlength hdr = 16 -> 0 <= j < Zlength c ->
  upd_Znth (16 + j) (hdr ++ map Vubyte c) (Vubyte x) = hdr ++ map Vubyte (upd_Znth j c x).
Proof. intros. list_solve. Qed.

(* a malloc result: NULL, or a token and an uninitialised buffer of n bytes (as ht4o_segL1.v) *)
Definition ht4oL2_mres (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.

Lemma ht4oL2_mres_valid (n: Z) (p: val) : ht4oL2_mres n p |-- valid_pointer p.
Proof.
  unfold ht4oL2_mres. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
      simpl. rewrite Z.max_r by lia. lia.
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

Lemma ht4oL2_mres_local (n: Z) (p: val) : ht4oL2_mres n p |-- !! is_pointer_or_null p.
Proof.
  unfold ht4oL2_mres. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

#[local] Hint Resolve ht4oL2_mres_valid : valid_pointer.
#[local] Hint Resolve ht4oL2_mres_local : saturate_local.

Lemma ht4o_segL2_ok {Espec: OracleKind} (F: ht4o_fix) (FR: mpred) (i: Z) (R: ret_assert) :
  semax ht4o_Delta (ht4o_PL1 F FR i) ht4o_segL2
    (overridePost (ht4o_PL2 F FR i) (loop1_ret_assert (ht4o_Icont F FR i) (overridePost (ht4o_Brk F FR) R))).
Proof.
  intros. destruct F as [gv vrc vwm vsnap vkey K steps]. destruct R as [Rn Rb Rc Rr].
  unfold ht4o_PL1, ht4o_Delta, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_tB, ht4o_segL2.
  cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app.
  simplify_func_tycontext. abbreviate_semax. Intros Y kind L pkt po rp.
  destruct H0 as [HK Hst]. destruct H1 as [Hinv Hln]. destruct H2 as [Hkd HL]. cbn [f_K f_steps] in HK, Hst.
  pose proof (cnt_top_range _ _ _ Hinv) as Htop. unfold CNT_R, CNT_W in Htop.
  (* the nonce *)
  forward_if (temp TO._t'12 (Vint (if (Z.eqb kind 2 && y_have Y)%bool then Int.one else Int.zero))).
  { forward. entailer!. destruct (y_have Y); reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq kind 2) H0). reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX n: Z, PROPx ((0 <= n <= Int64.max_unsigned) :: P) (LOCALx (temp TO._t'13 (Vlong (Int64.repr n)) :: Q) (SEPx R))) end.
  { forward. Exists (y_ln Y). entailer!. }
  { unfold ht4o_wm. Intros wp. forward. forward_call. Intros n. forward. Exists n. unfold ht4o_wm. Exists wp. entailer!. }
  Intros nonce. forward.
  (* the header *)
  assert (HE: L <= ht4o_enc kind L <= L + 16) by (unfold ht4o_enc; destruct (_ && _)%bool; lia).
  remember (ht4o_enc kind L) as E eqn:HEd.
  unfold ht4o_buf. Intros.
  set (c0 := Zrepeat Vundef (16 + E)).
  assert (Hc0: Zlength c0 = 16 + E) by (unfold c0; rewrite Zlength_Zrepeat; lia).
  forward_call (Ews, pkt, 0, c0, Int.repr 4).
  { entailer!. } { rewrite Hc0. cancel. }
  rewrite Hc0. set (c1 := haead_splice 0 _ c0).
  assert (Hc1: Zlength c1 = 16 + E) by (unfold c1; rewrite ht4oL2_splice_len; rewrite ?Hc0, ?ht4oL2_l32; lia).
  forward_call. Intros w.
  forward_call (Ews, pkt, 4, c1, Int.repr w).
  { entailer!. } { rewrite Hc1. cancel. }
  rewrite Hc1. set (c2 := haead_splice 4 _ c1).
  assert (Hc2: Zlength c2 = 16 + E) by (unfold c2; rewrite ht4oL2_splice_len; rewrite ?Hc1, ?ht4oL2_l32; lia).
  forward_call (Ews, pkt, 8, c2, nonce).
  { entailer!. } { rewrite Hc2. cancel. }
  rewrite Hc2. set (c3 := haead_splice 8 _ c2).
  assert (Hc3: c3 = map Vubyte (le32_bytes (Int.repr 4) ++ le32_bytes (Int.repr w) ++ le64_bytes nonce) ++ Zrepeat Vundef E).
  { unfold c3, c2, c1, c0. apply ht4oL2_hdr; reflexivity || lia. }
  rewrite Hc3. clearbody c3 c2 c1 c0. clear c3 Hc3 c2 Hc2 c1 Hc1 c0 Hc0.
  set (hdr := map Vubyte _).
  assert (Hh: Zlength hdr = 16) by (unfold hdr; rewrite Zlength_map, !Zlength_app, !ht4oL2_l32, ht4oL2_l64; reflexivity).
  clearbody hdr.
  assert_PROP (isptr pkt /\ isptr po /\ isptr rp) as Hptrs by entailer!. destruct Hptrs as (Hpk & Hpo & Hrp).
  (* the kind test *)
  forward_if (temp TO._t'19 (Vint (if (Z.eqb kind 0 || Z.eqb kind 1)%bool then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq kind 0) H2). unfold bool2val.
    destruct (zeq kind 1) as [E1|E1]; [subst; reflexivity | rewrite (proj2 (Z.eqb_neq kind 1) E1); reflexivity]. }
  forward_if (temp TO._t'20 (Vint (if Z.eqb kind 3 then Int.zero else Int.one))).
  { forward. entailer!. match goal with Hx: (if _ then _ else _) <> Int.zero |- _ =>
      destruct (Z.eqb_spec kind 3) as [->|]; [exfalso; apply Hx; reflexivity | reflexivity] end. }
  { forward. entailer!. match goal with Hx: (if _ then _ else _) = Int.zero |- _ =>
      assert (kind = 2 \/ kind = 3) as [->| ->]
        by (destruct (Z.eqb_spec kind 0), (Z.eqb_spec kind 1); try (simpl in Hx; contradiction (Int.one_not_zero Hx)); lia);
      reflexivity end. }
  assert_PROP (field_compatible (tarray tuchar (16 + E)) [] pkt) as Hfc by entailer!.
  forward_if.
  2:{ (* kind 3: ANY enc_len bytes *)
    assert (Hk3: kind = 3) by (destruct (Z.eqb_spec kind 3); [auto | match goal with Hx: _ = Int.zero |- _ => contradiction (Int.one_not_zero Hx) end]).
    rewrite (ht4oL2_split Ews (16 + E) 16 E hdr (Zrepeat Vundef E) pkt) by (rewrite ?Zlength_Zrepeat; auto; lia). Intros.
    forward_call (offset_val 16 pkt, E, Ews).
    Intros bs. rewrite ht4oL2_bytes_Vubyte by auto.
    sep_apply (ht4oL2_merge Ews 16 E hdr (map Vubyte (map Byte.repr bs)) pkt).
    { rewrite !Zlength_map; auto. }
    unfold ht4o_PL2. Exists Y kind L pkt po rp nonce hdr (map Byte.repr bs).
    unfold ht4o_tB, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_kL, ht4o_inv, ht4o_fix_ok, ht4o_buf.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app. rewrite <- HEd.
    entailer!. rewrite Zlength_map; auto. }
  (* kinds 0/1/2: an authentic packet *)
  assert (Hk3: kind <> 3) by (intros ->; apply H2; reflexivity).
  assert (HE16: E = L + 16) by (rewrite HEd; unfold ht4o_enc; rewrite (proj2 (Z.eqb_neq kind 3) Hk3); reflexivity).
  forward_call (tarray tuchar L, gv).
  { simpl sizeof. rep_lia. }
  Intros pt. fold (ht4oL2_mres L pt).
  forward_if.
  { (* malloc failed: 3 frees + break *)
    assert (pt = nullval) as -> by (destruct pt; try contradiction; simpl in *; subst; auto; match goal with Hx: _ |- _ => idtac end).
    unfold ht4oL2_mres. rewrite if_true by auto.
    sep_apply (ht4oL2_free_pre (16 + E) (hdr ++ Zrepeat Vundef E) pkt Hpk).
    forward_call (tarray tuchar (16 + E), pkt, gv).
    sep_apply (ht4oL2_free_pre (ht4o_plen E) (Zrepeat Vundef (ht4o_plen E)) po Hpo).
    forward_call (tarray tuchar (ht4o_plen E), po, gv).
    sep_apply (ht4oL2_free_pre (ht4o_plen E) (Zrepeat Vundef (ht4o_plen E)) rp Hrp).
    forward_call (tarray tuchar (ht4o_plen E), rp, gv).
    forward. unfold ht4o_Brk, ht4o_lvars.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
    Exists (y_top Y) (y_S Y). sep_apply (data_at_data_at_ Tsh ht4o_trc). entailer!. }
  unfold ht4oL2_mres. rewrite if_false by auto. Intros.
  forward_call (pt, L, Ews).
  Intros bs. rewrite ht4oL2_bytes_Vubyte by auto.
  set (m := map Byte.repr bs).
  assert (Hm: Zlength m = L) by (unfold m; rewrite Zlength_map; auto).
  clearbody m. clear H5.
  rewrite (ht4oL2_split Ews (16 + E) 16 E hdr (Zrepeat Vundef E) pkt) by (rewrite ?Zlength_Zrepeat; auto; lia). Intros.
  replace (data_at Ews (tarray tuchar E) (Zrepeat Vundef E) (offset_val 16 pkt))
    with (data_at_ Ews (tarray tuchar (Zlength m + 16)) (offset_val 16 pkt)) by (rewrite HE16, <- Hm; reflexivity).
  replace (data_at Ews (tarray tuchar L) (map Vubyte m) pt)
    with (data_at Ews (tarray tuchar (Zlength m)) (map Vubyte m) pt) by (rewrite Hm; reflexivity).
  rewrite (ht4oL2_prim Ews m pt). Intros.
  forward_call (Ews, offset_val 16 pkt, Ews, pt, m, Ews, nullval, @nil byte, nonce, Tsh, vkey, K, gv).
  { entailer!. rewrite Hm. reflexivity. }
  { rewrite ht4oL2_prim_nil, emp_sepcon. cancel. }
  { rewrite Zlength_nil; rep_lia. }
  rewrite ht4oL2_prim_nil.
  sep_apply (ht4oL2_prim_back Ews m pt).
  replace (data_at Ews (tarray tuchar (Zlength m)) (map Vubyte m) pt)
    with (data_at Ews (tarray tuchar L) (map Vubyte m) pt) by (rewrite Hm; reflexivity).
  assert_PROP (isptr pt) as Hpt by entailer!.
  sep_apply (ht4oL2_free_pre L (map Vubyte m) pt Hpt).
  forward_call (tarray tuchar L, pt, gv).
  set (c0 := aead_enc K nonce [] m).
  assert_PROP (Zlength (map Vubyte c0) = Zlength m + 16) as Hc0 by entailer!.
  rewrite Zlength_map in Hc0.
  replace (data_at Ews (tarray tuchar (Zlength m + 16)) (map Vubyte c0) (offset_val 16 pkt))
    with (data_at Ews (tarray tuchar E) (map Vubyte c0) (offset_val 16 pkt)) by (rewrite HE16, <- Hm; reflexivity).
  sep_apply (ht4oL2_merge Ews 16 E hdr (map Vubyte c0) pkt). { rewrite Zlength_map; lia. }
  clearbody c0. assert (Hc0E: Zlength c0 = E) by lia. clear Hc0 Hm H4 bs m.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    set (Post := EX ct: list byte, PROPx ((Zlength ct = E) :: P) (LOCALx Q
      (SEPx (data_at Ews (tarray tuchar (16 + E)) (hdr ++ map Vubyte ct) pkt :: R)))) end.
  forward_if Post.
  2:{ forward. unfold Post. Exists c0. entailer!. }
  { (* kind 1: flip one byte of the ciphertext||tag *)
    forward_call. Intros j. forward_if Post.
    2:{ forward. unfold Post. Exists c0. entailer!. }
    forward_call. Intros b.
    forward.
    { entailer!. rewrite Znth_app2 by lia. rewrite Hh, Znth_map by lia. unfold Vubyte; simpl.
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_app2 by lia. rewrite Hh, Znth_map by lia. replace (16 + j - 16) with j by lia.
    forward.
    { entailer!. pose proof (Z.mod_pos_bound b 255 ltac:(lia)).
      unfold Int.mods. rewrite (Int.signed_repr b), (Int.signed_repr 255) by rep_lia. rewrite Z.rem_mod_nonneg by lia.
      rewrite Int.signed_repr by rep_lia.
      split; [rep_lia | intros [_ X]; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate X]. }
    rewrite ht4oL2_ze8, ht4oL2_flip by lia.
    unfold Post. Exists (upd_Znth j c0 (Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned (Znth j c0)))
      (Int.zero_ext 8 (Int.add (Int.repr 1) (Int.mods (Int.repr b) (Int.repr 255)))))))).
    entailer!. rewrite Zlength_upd_Znth. auto. }
  unfold Post. Intros ct.
  unfold ht4o_PL2. Exists Y kind L pkt po rp nonce hdr ct.
  unfold ht4o_tB, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_kL, ht4o_inv, ht4o_fix_ok, ht4o_buf.
  cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app. rewrite <- HEd.
  entailer!.
Qed.
