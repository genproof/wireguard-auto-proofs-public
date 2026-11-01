(* law create_any: Segment H = statements 28..31 (n = p.handshake.entry.hashed ? 1 : 0; CHECK(kents_same_but_next(kes, &ita)); for (ke = kes; ke; ke = ke->next) { CHECK(ke->kp.entry.hashed); n++; } CHECK(table_len(&ita) == n)), from hca5_SG to hca5_SG.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: same C where the C did not change). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.create_any.hca5_PH_pure.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hca5_PH_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.
#[local] Instance hca5_PH_cceK : change_composite_env CKS W_create_any.
Proof. make_cs_preserve CKS W_create_any. Defined.

(* the table opened at one entry *)
Definition hca5_PH_rest (tab: val) (T: tstate) (a: val) : mpred :=
  !! itable_wf T &&
  (@data_at Noise.CS Tsh t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a)).

(* p's handshake entry as a field of p at the world *)
Lemma hca5_PH_open_hs tab T p E : @field_compatible Noise.CS t_peer [] p ->
  sfind (t_D T) (hs_addr p) = Some (Tsh, E) ->
  itable Tsh tab T =
  @field_at W_create_any Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (succ_in (t_L T) (hs_addr p), (Val.of_bool (vin (hs_addr p) (t_L T)),
     (Vint (e_type E), Vint (e_index E))))) p * hca5_PH_rest tab T (hs_addr p).
Proof.
  intros FC0 HS. assert (FC: @field_compatible W_create_any t_peer [] p).
  { apply (@field_compatible_change_composite Noise.CS W_create_any _); [prove_cs_preserve_type | exact FC0]. }
  unfold itable, hca5_PH_rest. rewrite (prot_rep3_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at, entry_val.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  erewrite <- (@data_at_change_composite Noise.CS W_create_any _ Tsh t_entry_s); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold hs_addr. simpl nested_field_offset.
  unfold OFS_PEER_HANDSHAKE. apply pred_ext; normalize; try (apply andp_right; [apply prop_right; auto|]); cancel.
Qed.

(* a kent's keypair entry (offset 0) as its field kp.entry at the world *)
Lemma hca5_PH_e_conv sh a (v1 v2 v3 v4 v5: val) : @field_compatible W t_kent [] a ->
  @data_at Noise.CS sh t_entry_s (v1, (v2, (v3, (v4, v5)))) a =
  @field_at W sh t_kent (DOT HC._kp DOT HC._entry) (v1, (v2, (v3, (v4, v5)))) a.
Proof.
  intros Hfc.
  rewrite (field_at_data_at sh t_kent (DOT HC._kp DOT HC._entry)).
  assert (Ha: field_address t_kent (DOT HC._kp DOT HC._entry) a = a).
  { rewrite field_compatible_field_address by auto with field_compatible. simpl. normalize. }
  rewrite Ha. simpl nested_field_type.
  rewrite (@data_at_change_composite Noise.CS W _ sh t_entry_s
    (v1, (v2, (v3, (v4, v5)))) (v1, (v2, (v3, (v4, v5)))) (JMeq_refl _))
    by prove_cs_preserve_type.
  reflexivity.
Qed.

Lemma hca5_PH_open_k tab T a sh E : @field_compatible W t_kent [] a ->
  sfind (t_D T) a = Some (sh, E) ->
  itable Tsh tab T =
  @field_at W sh t_kent (DOT HC._kp DOT HC._entry)
    (e_peer E, (succ_in (t_L T) a, (Val.of_bool (vin a (t_L T)), (Vint (e_type E), Vint (e_index E))))) a *
  hca5_PH_rest tab T a.
Proof.
  intros FC HS.
  unfold itable, hca5_PH_rest. rewrite (prot_rep3_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at, entry_val.
  rewrite hca5_PH_e_conv by auto.
  apply pred_ext; normalize; try (apply andp_right; [apply prop_right; auto|]); cancel.
Qed.

(* the list link of a kent at the world *)
Lemma hca5_PH_next_conv sh a nx :
  @field_at CKS sh t_kent [StructField HC._next] nx a = @field_at W sh t_kent [StructField HC._next] nx a.
Proof.
  assert (Hp: cs_preserve_type CKS W (coeq CKS W) t_kent = true) by prove_cs_preserve_type.
  apply (equal_f (@field_at_change_composite CKS W _ sh t_kent [StructField HC._next] nx nx (JMeq_refl _) Hp)).
Qed.
(* a kent without its list link (at the world) *)
Definition hca5_PH_cr (e: kent4) : mpred :=
  @malloc_token W Ews t_kent (ke_addr e) * kp_body_rep (ke_addr e) (ke_K e) *
  kent_snap_rep (ke_addr e) (ke_snap e) * kent_pads (ke_addr e).

Lemma hca5_PH_cell e nx : kent_cell W e nx =
  !! (@field_compatible CKS t_kent [] (ke_addr e)) &&
  (@field_at W Ews t_kent [StructField HC._next] nx (ke_addr e) * hca5_PH_cr e).
Proof.
  unfold kent_cell, hca5_PH_cr. rewrite hca5_PH_next_conv. f_equal. apply pred_ext; cancel.
Qed.

Lemma hca5_PH_fcW a : @field_compatible CKS t_kent [] a -> @field_compatible W t_kent [] a.
Proof.
  intros FC. apply (@field_compatible_change_composite CKS W _); [prove_cs_preserve_type | exact FC].
Qed.

Definition hca5_PH_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the kents as a list segment *)
Fixpoint hca5_PH_seg (l: val) (KE: list kent4) (tl: val) : mpred :=
  match KE with
  | [] => !! (l = tl) && emp
  | e :: KE' => !! (l = ke_addr e) && EX nx: val, kent_cell W e nx * hca5_PH_seg nx KE' tl
  end.

Lemma hca5_PH_seg_kents l KE1 tl KE2 :
  hca5_PH_seg l KE1 tl * kents_rep W tl KE2 |-- kents_rep W l (KE1 ++ KE2).
Proof.
  revert l. induction KE1 as [| e KE1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hca5_PH_seg_snoc l KE1 e nx :
  hca5_PH_seg l KE1 (ke_addr e) * kent_cell W e nx |-- hca5_PH_seg l (KE1 ++ [e]) nx.
Proof.
  revert l. induction KE1 as [| e0 KE1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx0. Exists nx0. entailer!. sep_apply (IH nx0). cancel.
Qed.

Lemma hca5_PH_kents_head l KE : kents_rep W l KE |-- !! (l = hca5_PH_khead KE).
Proof. destruct KE as [| e KE]; simpl; [entailer! | Intros nx; entailer!]. Qed.

Lemma hca5_PH_kents_pn l KE : kents_rep W l KE |-- !! (is_pointer_or_null l).
Proof.
  destruct KE as [| e KE]; simpl.
  - entailer!.
  - Intros nx. unfold kent_cell. Intros. entailer!. match goal with Hf: field_compatible _ [] _ |- _ => destruct Hf as [Hp _] end. apply isptr_is_pointer_or_null; auto.
Qed.

Lemma hca5_PH_kents_app T KD1 KD2 : hca5_kents T (KD1 ++ KD2) = hca5_kents T KD1 ++ hca5_kents T KD2.
Proof. unfold hca5_kents. rewrite !map_app. reflexivity. Qed.

Lemma hca5_PH_khead_eq T KD : hca5_PH_khead (hca5_kents T KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

Lemma hca5_PH_vo sh p P : vobjs W [VPeer sh p P] = peer_rep sh p P.
Proof. unfold vobjs. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hca5_PH_cell_fold e nx : @field_compatible CKS t_kent [] (ke_addr e) ->
  @field_at W Ews t_kent [StructField HC._next] nx (ke_addr e) * hca5_PH_cr e |-- kent_cell W e nx.
Proof. intros FC. rewrite hca5_PH_cell. entailer!. Qed.

Lemma hca5_PH_seg_kents0 l KE1 : hca5_PH_seg l KE1 nullval |-- kents_rep W l KE1.
Proof.
  pose proof (hca5_PH_seg_kents l KE1 nullval []) as Hd. rewrite app_nil_r in Hd.
  eapply derives_trans; [| apply Hd]. simpl. entailer!.
Qed.

Lemma hca5_PH_RAn (Q: environ -> mpred) (Rr: ret_assert) : RA_normal (overridePost Q Rr) = Q.
Proof. destruct Rr; reflexivity. Qed.

Lemma hca5_PH_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SG x25519 gv L FR w)
    hca5_PH
    (overridePost (hca5_SG x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_SG at 1. unfold hca5_Delta, hca5_R, hca5_PH. simplify_func_tycontext. abbreviate_semax.
  Intros R P T KD H' T' S' S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars, hca5_rest; cbn [app].
  Intros.
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_p L)) as FCp by (unfold peer_rep; entailer!).
  assert_PROP (itable_wf T') as WF by (unfold itable; entailer!).
  destruct (hca5_PH_facts (l_p L) KD T T' Tsh (p_set_hs P H') H1 WF H4)
    as ((E & HS & HEp & HEt) & HK & Hlen & Hpre & Hsame).
  rewrite (hca5_PH_open_hs (l_ita L) T' (l_p L) E FCp HS). Intros.
  forward.
  { entailer!. destruct (vin _ _); simpl; auto. }
  set (h := vin (hs_addr (l_p L)) (t_L T')) in *.
  forward_if (temp HC._t'29 (Vint (Int.repr (if h then 1 else 0)))).
  { forward. destruct h; [entailer! | discriminate]. }
  { forward. destruct h; [discriminate | entailer!]. }
  forward.
  rewrite Int.signed_repr by (destruct h; rep_lia).
  unfold h in *; clear h.
  sep_apply (derives_refl' _ _ (eq_sym (hca5_PH_open_hs (l_ita L) T' (l_p L) E FCp HS))).
  remember (if vin (hs_addr (l_p L)) (t_L T') then 1 else 0) as nh eqn:Hnh.
  freeze [1;2;3;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32] FR1.
  rewrite <- (hca5_PH_vo Tsh (l_p L) (p_set_hs P H')).
  match goal with |- semax _ ?Pr _ _ => forward_loop Pr continue: Pr break: Pr end.
  { apply ENTAIL_refl. }
  { forward_call (kents_head KD, hca5_kents T KD, Tsh, l_ita L, T', [VPeer Tsh (l_p L) (p_set_hs P H')]).
    { repeat constructor. simpl. auto. }
    rewrite Hsame.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  rewrite (hca5_PH_vo Tsh (l_p L) (p_set_hs P H')).
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) _)) _ _ =>
  forward_loop
    (EX KD1: list kdraw, EX KD2: list kdraw,
     PROP (KD = KD1 ++ KD2)
     (LOCALx (temp HC._ke (kents_head KD2) :: temp HC._n (Vlong (Int64.repr (Zlength KD1 + nh))) :: Q)
     (SEPx [FRZL FR1; itable Tsh (l_ita L) T'; peer_rep Tsh (l_p L) (p_set_hs P H');
            hca5_PH_seg (kents_head KD) (hca5_kents T KD1) (kents_head KD2);
            kents_rep W (kents_head KD2) (hca5_kents T KD2)])))
  continue:
    (EX KD1: list kdraw, EX d: kdraw, EX KD2: list kdraw,
     PROP (KD = KD1 ++ d :: KD2)
     (LOCALx (temp HC._ke (kd_addr d) :: temp HC._n (Vlong (Int64.repr (Zlength KD1 + 1 + nh))) :: Q)
     (SEPx [FRZL FR1; itable Tsh (l_ita L) T'; peer_rep Tsh (l_p L) (p_set_hs P H');
            hca5_PH_seg (kents_head KD) (hca5_kents T KD1) (kd_addr d);
            kents_rep W (kd_addr d) (hca5_kents T (d :: KD2))])))
  break:
    (PROP ()
     (LOCALx (temp HC._n (Vlong (Int64.repr (Zlength KD + nh))) :: Q)
     (SEPx [FRZL FR1; itable Tsh (l_ita L) T'; peer_rep Tsh (l_p L) (p_set_hs P H');
            kents_rep W (kents_head KD) (hca5_kents T KD)])))
  end.
  - Exists (@nil kdraw) KD. simpl hca5_PH_seg. entailer!.
  - Intros KD1 KD2.
    destruct KD2 as [| d KD2].
    + simpl kents_head. cbn [hca5_kents map kents_rep]. Intros. rewrite app_nil_r in *. subst KD.
      forward_if.
      { exfalso. auto. }
      forward.
      sep_apply (hca5_PH_seg_kents0 (kents_head KD1) (hca5_kents T KD1)).
      entailer!.
    + assert (Hin: In d KD) by (subst KD; apply in_or_app; right; left; auto).
      destruct (HK d Hin) as [HSk HVk].
      cbn [kents_head hca5_kents map kents_rep]. Intros nx.
      rewrite hca5_PH_cell. Intros.
      change (ke_addr (kent_snapped T (kd_kent d))) with (kd_addr d) in *.
      match goal with Hf: @field_compatible CKS _ _ _ |- _ => pose proof (hca5_PH_fcW _ Hf) as FCk end.
      pose proof (hca5_PH_open_k (l_ita L) T' (kd_addr d) Ews _ FCk HSk) as Hop.
      cbn [e_peer e_type e_index] in Hop. rewrite HVk in Hop.
      rewrite Hop. Intros.
      forward_if.
      { assert (Hvp: @field_at W Ews t_kent (DOT HC._kp DOT HC._entry)
          (l_p L, (succ_in (t_L T') (kd_addr d), (Val.of_bool true, (Vint IDX_KEYPAIR, Vint (kd_idx d)))))
          (kd_addr d) |-- valid_pointer (kd_addr d)).
        { apply field_at_valid_ptr0; [apply readable_nonidentity, writable_readable, writable_Ews | reflexivity | reflexivity]. }
        sep_apply Hvp.
        apply denote_tc_test_eq_split; [| apply valid_pointer_null]. entailer!. }
      2: { exfalso. destruct FCk as [Hp _]. assert (Hn: kd_addr d = nullval) by assumption. rewrite Hn in Hp. exact Hp. }
      Intros.
      match goal with |- semax _ ?Pr _ _ => forward_loop Pr continue: Pr break: Pr end.
      * apply ENTAIL_refl.
      * forward.
        forward_if.
        { exfalso. apply Int.one_not_zero. assumption. }
        forward. entailer!.
      * forward. apply ENTAIL_refl.
      * forward.
        sep_apply (derives_refl' _ _ (eq_sym Hop)).
        sep_apply (hca5_PH_cell_fold (kent_snapped T (kd_kent d)) nx H8).
        Exists KD1 d KD2. cbn [hca5_kents map kents_rep]. Exists nx.
        entailer!. do 2 f_equal. lia.
  - Intros KD1 d KD2. cbn [hca5_kents map kents_rep]. Intros nx.
    rewrite hca5_PH_cell. Intros.
    change (ke_addr (kent_snapped T (kd_kent d))) with (kd_addr d) in *.
    assert_PROP (is_pointer_or_null nx) by (sep_apply (hca5_PH_kents_pn nx (hca5_kents T KD2)); entailer!).
    forward.
    sep_apply (hca5_PH_kents_head nx (hca5_kents T KD2)). Intros.
    rewrite hca5_PH_khead_eq in *.
    match goal with Hf: @field_compatible CKS _ _ _ |- _ =>
      sep_apply (hca5_PH_cell_fold (kent_snapped T (kd_kent d)) nx Hf) end.
    sep_apply (hca5_PH_seg_snoc (kents_head KD) (hca5_kents T KD1) (kent_snapped T (kd_kent d)) nx).
    Exists (KD1 ++ [d]) KD2.
    rewrite hca5_PH_kents_app. cbn [hca5_kents map].
    entailer!. split.
    + rewrite <- app_assoc. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. do 2 f_equal; lia.
  - match goal with |- semax _ ?Pr _ _ => forward_loop Pr continue: Pr break: Pr end.
    + apply ENTAIL_refl.
    + forward_call (Tsh, l_ita L, T').
      rewrite Hlen.
      forward_if.
      { exfalso. rewrite Int64.eq_true in *. apply Int.one_not_zero. assumption. }
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + unfold POSTCONDITION, abbreviate. rewrite hca5_PH_RAn.
      unfold hca5_SG. thaw FR1.
      Exists R P T KD H' T' S' S0.
      unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars, hca5_rest; cbn [app].
      entailer!.
Qed.
