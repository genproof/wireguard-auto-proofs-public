(* law transport_order: main's segment L3 (body statements 14..17): rc_take, the kernel decryption, the reference decryption,
   CHECK(ok == ref_ok).
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
Require WgNoise.proof.aead.aead_models_props3.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

(* splitting a byte array for exact-size callees (as har_split of haead_ref_body3.v) *)
Lemma ht4o_L3_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
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

(* exact byte array <-> the AEADs' prim_bytes (emp when empty) *)
Lemma ht4o_L3_prim (sh: share) (l: list byte) (n: Z) (p: val) : n = Zlength l ->
  data_at sh (tarray tuchar n) (map Vubyte l) p =
  (prim_bytes sh l p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) (map Vubyte l) p else emp))%logic.
Proof.
  intros ->. unfold prim_bytes. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma ht4o_L3_merge sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
  field_compatible (tarray tuchar n) [] p ->
  (data_at sh (tarray tuchar n1) l1 p * data_at sh (tarray tuchar n2) l2 (offset_val n1 p))%logic
  |-- data_at sh (tarray tuchar n) (l1 ++ l2) p.
Proof. intros. rewrite (ht4o_L3_split sh n n1 n2) by auto. apply derives_refl. Qed.

Lemma ht4o_L3_prim_back (sh: share) (l: list byte) (n: Z) (p: val) : n = Zlength l ->
  (prim_bytes sh l p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) (map Vubyte l) p else emp))%logic
  |-- data_at sh (tarray tuchar n) (map Vubyte l) p.
Proof. intros. rewrite <- ht4o_L3_prim by auto. apply derives_refl. Qed.

(* exact output array <-> prim_out (emp when empty) *)
Lemma ht4o_L3_out (sh: share) (v: list val) (n: Z) (p: val) : n = Zlength v ->
  data_at sh (tarray tuchar n) v p =
  (prim_out sh v p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) v p else emp))%logic.
Proof.
  intros ->. unfold prim_out. destruct (Z.eq_dec (Zlength v) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma ht4o_L3_out_back (sh: share) (v v': list val) (n: Z) (p: val) : n = Zlength v -> Zlength v' = n ->
  (prim_out sh v p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) v' p else emp))%logic
  |-- data_at sh (tarray tuchar n) v p.
Proof.
  intros -> Hv'. unfold prim_out. destruct (Z.eq_dec (Zlength v) 0) as [E|E].
  - rewrite emp_sepcon. apply Zlength_nil_inv in E. rewrite E in Hv' |- *. apply Zlength_nil_inv in Hv'.
    subst v'. apply derives_refl.
  - rewrite sepcon_emp; auto.
Qed.

Lemma ht4o_L3_null (sh: share) : prim_bytes sh [] nullval = emp.
Proof. reflexivity. Qed.

Lemma ht4o_L3_dec_len K nonce ct pt : aead_dec K nonce [] ct = Some pt -> Zlength pt = Zlength ct - 16.
Proof.
  intros H. eapply aead_models_props3.amp3_dec_len; [| exact H]. apply aead_models_props3.amp3_aead_st_len.
Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, exponential in the common
   bits of two identifiers (TO._ref_ok vs TO._ref_pt: > 300 s); this removes it by Pos.eqb computation instead *)
Lemma ht4o_L3_rlt (i: ident) (L: list localdef) :
  forallb (fun d => match d with temp j _ => negb (Pos.eqb i j) | _ => true end) L = true ->
  remove_localdef_temp i L = L.
Proof.
  induction L as [|d L IH]; intros H; [reflexivity |].
  simpl in H. apply andb_prop in H as [H1 H2].
  change (remove_localdef_temp i (d :: L)) with
    (match d with temp j _ => if rlt_ident_eq i j then remove_localdef_temp i L else d :: remove_localdef_temp i L
     | _ => d :: remove_localdef_temp i L end).
  rewrite IH by auto.
  destruct d; auto.
  destruct (rlt_ident_eq i i0); auto. subst. rewrite Pos.eqb_refl in H1. discriminate.
Qed.

Lemma ht4o_segL3_ok {Espec: OracleKind} (F: ht4o_fix) (FR: mpred) (i: Z) (R: ret_assert) :
  semax ht4o_Delta (ht4o_PL2 F FR i) ht4o_segL3
    (overridePost (ht4o_PL3 F FR i) (loop1_ret_assert (ht4o_Icont F FR i) (overridePost (ht4o_Brk F FR) R))).
Proof.
  intros. destruct F as [gv vrc vwm vsnap vkey K steps]. destruct R as [Rn Rb Rc Rr].
  cbn [overridePost loop1_ret_assert].
  unfold ht4o_PL2, ht4o_Delta, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_tB, ht4o_segL3.
  cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app. simplify_func_tycontext. abbreviate_semax.
  Intros Y kind L pkt po rp nonce hdr ct.
  destruct H0 as [HK Hst]. cbn [f_K f_steps] in HK, Hst.
  destruct H1 as [Hinv Hln]. pose proof (cnt_len _ _ _ Hinv) as Hbm.
  destruct H2 as [Hkind HL].
  forward_call (Tsh, vsnap, Tsh, vrc, y_top Y, y_bm Y).
  assert (Henc: 0 <= ht4o_enc kind L <= Int64.max_signed - 16).
  { unfold ht4o_enc. destruct (Z.eqb kind 3 && Z.ltb L 16)%bool eqn:E;
      [apply andb_prop in E; destruct E as [_ E]; apply Z.ltb_lt in E|]; lia. }
  set (enc := ht4o_enc kind L) in *.
  set (plen := ht4o_plen enc) in *.
  assert (Hplen: plen = Z.max 0 (Zlength ct - 16)) by (unfold plen, ht4o_plen; rewrite H5; reflexivity).
  unfold ht4o_buf. Intros.
  assert_PROP (field_compatible (tarray tuchar (16 + enc)) [] pkt) by entailer!.
  rewrite (ht4o_L3_split Ews (16 + enc) 16 enc hdr (map Vubyte ct) pkt) by (auto; rewrite Zlength_map; auto).
  rewrite (ht4o_L3_prim Ews ct enc (offset_val 16 pkt)) by auto.
  rewrite (ht4o_L3_out Ews (Zrepeat Vundef plen) plen po) by (rewrite Zlength_Zrepeat; lia).
  Intros.
  forward_call (Ews, po, Zrepeat Vundef plen, Ews, offset_val 16 pkt, ct, Ews, nullval, @nil byte, nonce, Tsh, vkey, K, gv).
  { rewrite <- H5. entailer!. }
  { rewrite ht4o_L3_null. cancel. }
  { split; [rewrite Zlength_nil; rep_lia | rewrite Zlength_Zrepeat by (unfold plen, ht4o_plen; lia); lia]. }
  rewrite (ht4o_L3_out Ews (Zrepeat Vundef plen) plen rp) by (rewrite Zlength_Zrepeat; lia).
  Intros.
  (* forward_call by hand: after_forward_call only once remove_localdef_temp is gone (ht4o_L3_rlt) *)
  eapply semax_seq'.
  - prove_call_setup (@nil Type) funspec_sub_refl
      (Ews, rp, Zrepeat Vundef plen, Ews, offset_val 16 pkt, ct, Ews, nullval, @nil byte, nonce, Tsh, vkey, K, gv);
      clear_Delta_specs; clear_MORE_POST; [ .. | forward_call_id1_y_wow ].
    + rewrite <- H5. entailer!.
    + split; [rewrite Zlength_nil; rep_lia | rewrite Zlength_Zrepeat by (unfold plen, ht4o_plen; lia); lia].
  - match goal with |- context [remove_localdef_temp ?i ?L] => rewrite (ht4o_L3_rlt i L) by reflexivity end.
    after_forward_call.
    rewrite ht4o_L3_null.
    assert (Hfix: ht4o_fix_ok (mkTFix gv vrc vwm vsnap vkey K steps)) by (split; auto).
    assert (HY: ht4o_inv Y) by (split; auto).
    assert (HkL: ht4o_kL kind L) by (split; auto).
    assert (Hp0: 0 <= plen) by (unfold plen, ht4o_plen; lia).
    destruct (aead_dec K nonce [] ct) as [pt|] eqn:Hd.
    + cbv [Val.of_bool].
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      * apply ENTAIL_refl.
      * match goal with |- semax _ ?P _ _ => forward_if P end.
        -- match goal with Hc: Int.repr (Z.b2z (Int.eq _ _)) = Int.zero |- _ =>
             rewrite Int.eq_true in Hc; discriminate Hc end.
        -- forward. entailer!.
        -- forward. entailer!.
      * assert (Hpt: Zlength pt = plen).
        { apply ht4o_L3_dec_len in Hd. rewrite Hplen. pose proof (Zlength_nonneg pt). lia. }
        sep_apply (ht4o_L3_out_back Ews (map Vubyte pt) (Zrepeat Vundef plen) plen rp
          ltac:(rewrite Zlength_map; lia) ltac:(rewrite Zlength_Zrepeat by lia; reflexivity)).
        sep_apply (ht4o_L3_out_back Ews (map Vubyte pt) (Zrepeat Vundef plen) plen po
          ltac:(rewrite Zlength_map; lia) ltac:(rewrite Zlength_Zrepeat by lia; reflexivity)).
        sep_apply (ht4o_L3_prim_back Ews ct enc (offset_val 16 pkt) ltac:(auto)).
        sep_apply (ht4o_L3_merge Ews (16 + enc) 16 enc hdr (map Vubyte ct) pkt H4
          ltac:(rewrite Zlength_map; auto) ltac:(lia) H0).
        unfold ht4o_PL3, ht4o_buf, ht4o_dec, ht4o_okv, ht4o_ptv, ht4o_tB, ht4o_temps, ht4o_lvars, ht4o_world.
        cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
        Exists Y kind L pkt po rp nonce hdr ct. rewrite Hd. simpl app.
        entailer!.
    + cbv [Val.of_bool].
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      * apply ENTAIL_refl.
      * match goal with |- semax _ ?P _ _ => forward_if P end.
        -- match goal with Hc: Int.repr (Z.b2z (Int.eq _ _)) = Int.zero |- _ =>
             rewrite Int.eq_true in Hc; discriminate Hc end.
        -- forward. entailer!.
        -- forward. entailer!.
      * sep_apply (ht4o_L3_out_back Ews (Zrepeat Vundef plen) (Zrepeat Vundef plen) plen rp
          ltac:(rewrite Zlength_Zrepeat by lia; reflexivity) ltac:(rewrite Zlength_Zrepeat by lia; reflexivity)).
        sep_apply (ht4o_L3_out_back Ews (Zrepeat Vundef plen) (Zrepeat Vundef plen) plen po
          ltac:(rewrite Zlength_Zrepeat by lia; reflexivity) ltac:(rewrite Zlength_Zrepeat by lia; reflexivity)).
        sep_apply (ht4o_L3_prim_back Ews ct enc (offset_val 16 pkt) ltac:(auto)).
        sep_apply (ht4o_L3_merge Ews (16 + enc) 16 enc hdr (map Vubyte ct) pkt H4
          ltac:(rewrite Zlength_map; auto) ltac:(lia) H0).
        unfold ht4o_PL3, ht4o_buf, ht4o_dec, ht4o_okv, ht4o_ptv, ht4o_tB, ht4o_temps, ht4o_lvars, ht4o_world.
        cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
        Exists Y kind L pkt po rp nonce hdr ct. rewrite Hd. simpl app.
        entailer!.
Qed.
