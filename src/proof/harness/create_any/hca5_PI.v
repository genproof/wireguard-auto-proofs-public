(* law create_any: Segment I = statements 32..34 (CHECK(pr_same(&ps, &p) && p.refcount.refcount == refs0 && dev_same(&ds, &wa) && shim_same(&ss)); kents_free(kes); return 0), from hca5_SG; main returns (post FF: the return goes to hca5_R).
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
Require Import WgNoise.proof.harness.create_any.hca5_conv.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hca5_pi_CCE : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

Lemma hca5_pi_refs sh p r :
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p =
  @field_at W_create_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p.
Proof.
  assert (Hc: cs_preserve_type Noise.CS W_create_any (@coeq _ _ hca5_pi_CCE) t_peer = true)
    by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_create_any hca5_pi_CCE sh t_peer
                 [StructField prot_repr3.I._refcount] (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep with its reference count at the world's compspecs *)
Definition hca5_pi_prest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hca5_pi_split sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at W_create_any sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
    hca5_pi_prest sh p P))%logic.
Proof.
  rewrite <- hca5_pi_refs. unfold peer_rep, hca5_pi_prest.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hca5_pi_veqb v : veqb v v = true.
Proof. unfold veqb. rewrite if_true; auto. Qed.

Lemma hca5_pi_bytes_eqb b : bytes_eqb b b = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec b b); congruence. Qed.

Lemma hca5_pi_pr_eqb P H : pr_eqb P (p_set_hs P H) = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb, p_set_hs; cbn.
  rewrite !hca5_pi_veqb, !hca5_pi_bytes_eqb, !Bool.eqb_reflx, !Int64.eq_true. reflexivity.
Qed.

Lemma hca5_pi_dev_eqb D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hca5_pi_veqb, !hca5_pi_bytes_eqb, !Bool.eqb_reflx, !Int64.eq_true. reflexivity.
Qed.

Lemma hca5_pi_shim_eqb S0 S w : hca5_cnt S = hca5_cnt S0 -> shim_eqb S0 w S w = true.
Proof.
  unfold hca5_cnt, shim_eqb, warn_eqb. intros Hc. inversion Hc as [[Ha Hf Hr Hl]].
  rewrite Ha, Hf, Hr, Hl, !Int64.eq_true. cbn [forallb]. rewrite !Int64.eq_true. reflexivity.
Qed.

Lemma hca5_pi_saddrs p KD a sh E :
  saddrs (map (hca5_kpool p) KD ++ [(a, sh, E)]) = map kd_addr KD ++ [a].
Proof. unfold saddrs. rewrite map_app, map_map. reflexivity. Qed.

Lemma hca5_pi_supd p KD a sh E E' :
  ~ In a (map kd_addr KD) ->
  supd (map (hca5_kpool p) KD ++ [(a, sh, E)]) a E' = map (hca5_kpool p) KD ++ [(a, sh, E')].
Proof.
  induction KD as [| d KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intro; apply Hn; left; auto). f_equal. apply IH. tauto.
Qed.

Lemma hca5_pi_sfind p KD a sh E :
  ~ In a (map kd_addr KD) ->
  sfind (map (hca5_kpool p) KD ++ [(a, sh, E)]) a = Some (sh, E).
Proof.
  induction KD as [| d KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intro; apply Hn; left; auto). apply IH. tauto.
Qed.

(* the pool of the current table: the kents' entries, then p's handshake entry (its index maybe changed) *)
Lemma hca5_pi_D p KD T T' :
  hca5_pool p KD T ->
  (T' = T \/ (exists idx, T' = t_insert T (hs_addr p) idx)) ->
  exists E', t_D T' = map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E')].
Proof.
  intros [[E [HD _]] [Hnd _]] [-> | [idx ->]]; [exists E; exact HD |].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hn _].
  unfold t_insert, t_set_index, t_entry. rewrite HD, hca5_pi_sfind by exact Hn.
  cbn [t_D t_upd]. rewrite HD, hca5_pi_supd by exact Hn.
  eexists; reflexivity.
Qed.

(* the table dissolved: its header, the kents' entries, p's handshake entry *)
Lemma hca5_pi_itab p a KD T ita E' :
  t_D T = map (hca5_kpool p) KD ++ [(a, Tsh, E')] ->
  itable Tsh ita T |--
  @data_at_ Noise.CS Tsh t_itab ita *
  iter_sepcon (fun d => @data_at_ Noise.CS Ews t_entry_s (kd_addr d)) KD *
  EX n: val, EX h: bool, entry_at Tsh a E' n h.
Proof.
  intros HD. unfold itable. Intros. rewrite HD.
  rewrite iter_sepcon_app. simpl iter_sepcon. rewrite sepcon_emp.
  rewrite <- iter_sepcon_map.
  Exists (succ_in (t_L T) a) (vin a (t_L T)).
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_itab (hd nullval (t_L T)) ita).
  cancel. apply iter_sepcon_derives. intros d _.
  unfold hca5_kpool, pool_item_rep, entry_at. apply data_at_data_at_.
Qed.

Lemma hca5_pi_kents_ent T KD :
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) (hca5_kents T KD) =
  iter_sepcon (fun d => @data_at_ Noise.CS Ews t_entry_s (kd_addr d)) KD.
Proof. unfold hca5_kents. rewrite <- !iter_sepcon_map. reflexivity. Qed.

Lemma hca5_pi_vobjs2 (CS: compspecs) o1 o2 : vobj_rep CS o1 * vobj_rep CS o2 = vobjs CS [o1; o2].
Proof. unfold vobjs. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the device, whole *)
Lemma hca5_pi_dev sh wg D : device_rep sh wg D |-- @data_at_ Noise.CS sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep. Intros lk1 lk2.
  assert (FI: forall v, @data_at Noise.CS sh t_sid v (id_addr wg) |--
                        @field_at_ Noise.CS sh t_dev (DOT I._static_identity) wg).
  { intros v. unfold field_at_. rewrite field_at_data_at.
    rewrite field_address_offset by auto with field_compatible. apply data_at_data_at_. }
  assert (FC: forall v, @data_at Noise.CS sh t_cc v (cc_addr wg) |--
                        @field_at_ Noise.CS sh t_dev (DOT I._cookie_checker) wg).
  { intros v. unfold field_at_. rewrite field_at_data_at.
    rewrite field_address_offset by auto with field_compatible. apply data_at_data_at_. }
  sep_apply FI. sep_apply FC.
  unfold_data_at (@data_at_ Noise.CS sh t_dev wg).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_dev ?g ?v wg] =>
    change (@field_at Noise.CS sh t_dev g v wg) with (@field_at_ Noise.CS sh t_dev g wg) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_dev ?g ?v wg] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_dev g v wg) end.
  unfold I._static_identity, I._cookie_checker, noise.code._static_identity, noise.code._cookie_checker; cancel.
Qed.

Ltac hca5_pi_in :=
  first [ reflexivity | (left; hca5_pi_in) | (right; hca5_pi_in) | (apply in_or_app; right; simpl; hca5_pi_in) ].

Lemma hca5_PI_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SG x25519 gv L FR w)
    hca5_PI
    (overridePost FF (hca5_R gv)).
Proof.
  intros HH. unfold hca5_R. apply hca5_post_canon.
  unfold hca5_SG, hca5_Delta, hca5_PI. abbreviate_semax.
  Intros R P T KD H' T' S' S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars, hca5_rest; cbn [app].
  Intros. pose proof (hca5_pi_D _ _ _ _ H1 H4) as [E' HD'].
  assert (Hin: forall v, v = nullval \/ In v (map kd_addr KD) -> vp_ok (l_ita L :: saddrs (t_D T')) v).
  { intros v [-> | Hv]; [left; auto | right; right; rewrite HD', hca5_pi_saddrs; apply in_or_app; left; exact Hv]. }
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { entailer!. }
  2: { forward. entailer!. }
  { gather_SEP 0 3.
    change (device_rep Tsh (l_wa L) (hca5_D x25519 R L) * itable Tsh (l_ita L) T') with
      (vobj_rep W (VDev Tsh (l_wa L) (hca5_D x25519 R L)) * vobj_rep W (VItab Tsh (l_ita L) T')).
    rewrite hca5_pi_vobjs2.
    forward_call (Tsh, l_ps L, P, Tsh, l_p L, p_set_hs P H', [VDev Tsh (l_wa L) (hca5_D x25519 R L); VItab Tsh (l_ita L) T']).
    { split; [repeat constructor; apply readable_share_top |].
      destruct H0 as (Hd & _ & _ & Hpk & Hsl).
      assert (Hown: forall v, vp_ok (l_ita L :: saddrs (t_D T')) v ->
        vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_wa L) (hca5_D x25519 R L); VItab Tsh (l_ita L) T']) v).
      { unfold vp_ok. intros v [Hv | Hv]; [left; exact Hv | right]. simpl. rewrite app_nil_r.
        simpl in Hv. tauto. }
      inversion Hsl as [| ? ? Hc Hsl1]; subst. inversion Hsl1 as [| ? ? Hpr Hsl2]; subst.
      inversion Hsl2 as [| ? ? Hnx _]; subst.
      unfold pr_ptrs, p_set_hs; cbn [p_device p_cur p_prev p_next p_pknext]. rewrite Hd, Hpk.
      assert (Hwa: vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_wa L) (hca5_D x25519 R L); VItab Tsh (l_ita L) T']) (l_wa L))
        by (right; simpl; auto).
      assert (Hnl: vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_wa L) (hca5_D x25519 R L); VItab Tsh (l_ita L) T']) nullval)
        by (left; auto).
      pose proof (Hown _ (Hin _ Hc)). pose proof (Hown _ (Hin _ Hpr)). pose proof (Hown _ (Hin _ Hnx)).
      repeat (apply Forall_cons; [assumption |]); apply Forall_nil. }
    rewrite hca5_pi_pr_eqb.
    forward_if (temp HC._t'33 (Vint Int.one)).
    { rewrite (hca5_pi_split Tsh (l_p L) (p_set_hs P H')). Intros.
      forward. forward. rewrite Int.eq_true. entailer!.
      rewrite (hca5_pi_split Tsh (l_p L) (p_set_hs P H')). entailer!. }
    { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
    rewrite <- hca5_pi_vobjs2. cbn [vobj_rep].
    Intros.
    (* dev_same(&ds, &wa) *)
    forward_if (temp HC._t'34 (Vint Int.one)).
    { gather_SEP 3 1.
      change (itable Tsh (l_ita L) T' * peer_rep Tsh (l_p L) (p_set_hs P H')) with
        (vobj_rep W (VItab Tsh (l_ita L) T') * vobj_rep W (VPeer Tsh (l_p L) (p_set_hs P H'))).
      rewrite hca5_pi_vobjs2.
      forward_call (Tsh, l_ds L, hca5_D x25519 R L, l_p L, Tsh, l_wa L, hca5_D x25519 R L, Tsh, l_p L,
                    [VItab Tsh (l_ita L) T'; VPeer Tsh (l_p L) (p_set_hs P H')]).
      { split; [repeat constructor; apply readable_share_top |].
        unfold dev_ptrs, hca5_D, setup_dev; cbn [d_dev d_cc cc_dev d_ptab d_itab].
        repeat (apply Forall_cons; [unfold vp_ok; simpl; hca5_pi_in |]); apply Forall_nil. }
      rewrite hca5_pi_dev_eqb.
      forward. rewrite <- hca5_pi_vobjs2. cbn [vobj_rep].
      change (d_ptab (hca5_D x25519 R L)) with (l_pta L). entailer!. }
    { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
    (* shim_same(&ss) *)
    forward_if (temp HC._t'36 (Vint Int.one)).
    { forward_call (gv, Tsh, l_ss L, S0, w, S', w).
      rewrite (hca5_pi_shim_eqb S0 S' w H5).
      forward. entailer!. }
    { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
    forward_if.
    { match goal with Hx: _ |- _ => solve [inv Hx] end. }
    forward. entailer!. }
  (* kents_free(kes) *)
  sep_apply (hca5_pi_itab (l_p L) (hs_addr (l_p L)) KD T' (l_ita L) E' HD'). Intros n h.
  rewrite <- (hca5_pi_kents_ent T KD).
  forward_call (gv, kents_head KD, hca5_kents T KD).
  (* return 0 *)
  forward.
  sep_apply (prot_rep3_peer_whole Tsh (l_p L) (p_set_hs P H') E' n h).
  sep_apply (hca5_pi_dev Tsh (l_wa L) (hca5_D x25519 R L)).
  unfold ptable. sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab (l_p L) (l_pta L)).
  sep_apply (@data_at_data_at_ HCS Tsh t_mident (mident_val (hca5_I x25519 R)) (l_ia L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_prsnap (prsnap_val P) (l_ps L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hca5_D x25519 R L) (l_p L)) (l_ds L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S0 w) (l_ss L)).
  rewrite hca5_conv_dev, hca5_conv_itab, hca5_conv_ptab, hca5_conv_peer, hca5_conv_mident,
    !hca5_conv_hsnap, hca5_conv_mstate, !hca5_conv_bytes, hca5_conv_prsnap, hca5_conv_devsnap,
    hca5_conv_shimsnap.
  cancel.
Qed.
