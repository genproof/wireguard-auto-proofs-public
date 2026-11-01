(* law create_any: Segment G = statements 26..27 (if (ok) { CHECK(p.handshake.entry.index == wg_shim_random_u32 && table_has(&ita, &p.handshake.entry) && table_index_unique(&ita, p.handshake.entry.index)); x.next = p.handshake.entry.next; x.hashed = true; x.index = wg_shim_random_u32; } CHECK(hs_same(&x, &p.handshake))), from hca5_SF to hca5_SG.
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require WgNoise.harness.x_create_any.code.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

#[local] Instance hca5_PG_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.
#[local] Instance hca5_PG_cceH : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.

(* ---- pure facts on the table ---- *)

Lemma hca5_PG_sfind_supd (D: list (val * share * entry)) a sh E E' :
  sfind D a = Some (sh, E) -> sfind (supd D a E') a = Some (sh, E').
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - inv H. rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. auto.
Qed.

Lemma hca5_PG_sfind_supd_ne (D: list (val * share * entry)) a x E' :
  x <> a -> sfind (supd D a E') x = sfind D x.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; [reflexivity|].
  destruct (EqDec_val y a); simpl.
  - subst. rewrite !if_false by congruence. reflexivity.
  - destruct (EqDec_val y x); auto.
Qed.

Lemma hca5_PG_saddrs_supd (D: list (val * share * entry)) a E' : saddrs (supd D a E') = saddrs D.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; [reflexivity|].
  destruct (EqDec_val y a); simpl; [reflexivity|]. f_equal; auto.
Qed.

Lemma hca5_PG_vremove_in a x L : In x L -> x <> a -> In x (vremove a L).
Proof.
  induction L as [|y L IH]; simpl; intros H N; [contradiction|].
  destruct (EqDec_val y a); [subst; destruct H; [congruence|auto]|].
  destruct H; [left; auto | right; auto].
Qed.

Lemma hca5_PG_vremove_notin a L : ~ In a (vremove a L).
Proof.
  induction L as [|y L IH]; simpl; [auto|].
  destruct (EqDec_val y a); [auto|]. intros [H|H]; [congruence|auto].
Qed.

Lemma hca5_PG_vremove_incl a L : incl (vremove a L) L.
Proof.
  induction L as [|y L IH]; simpl; intros x Hx; [contradiction|].
  destruct (EqDec_val y a); [right; auto|]. destruct Hx; [left; auto|right; auto].
Qed.

Lemma hca5_PG_vremove_nodup a L : NoDup L -> NoDup (vremove a L).
Proof.
  induction L as [|y L IH]; simpl; intros H; [constructor|]. inv H.
  destruct (EqDec_val y a); [auto|]. constructor; auto.
  intros Hi; apply H2, (hca5_PG_vremove_incl a L); auto.
Qed.

(* the inserted entry *)
Definition hca5_PG_E' (E: entry) (idx: int) : entry := mkEntry (e_peer E) (e_type E) idx.

Lemma hca5_PG_tD T a E idx : t_entry T a = Some E ->
  t_D (t_insert T a idx) = supd (t_D T) a (hca5_PG_E' E idx) /\
  t_L (t_insert T a idx) = a :: vremove a (t_L T).
Proof. intros H. unfold t_insert, t_set_index. rewrite H. split; reflexivity. Qed.

Lemma hca5_PG_indices_ne T a E' L :
  ~ In a L -> t_indices (mkT (supd (t_D T) a E') (a :: L)) L = t_indices T L.
Proof.
  intros N. unfold t_indices. apply map_ext_in. intros x Hx.
  unfold t_entry. cbn [t_D]. rewrite hca5_PG_sfind_supd_ne by (intros ->; auto). reflexivity.
Qed.

Lemma hca5_PG_count T a E idx : t_entry T a = Some E -> t_fresh T a idx ->
  count_index (t_insert T a idx) idx = 1%Z.
Proof.
  intros HE HF. unfold t_fresh in HF.
  unfold t_entry in HE. destruct (sfind (t_D T) a) as [[sh E0]|] eqn:HS; inv HE.
  assert (HE: t_entry T a = Some E) by (unfold t_entry; rewrite HS; reflexivity).
  unfold count_index, t_insert, t_set_index. rewrite HE. unfold t_upd. cbn [t_D t_L].
  unfold t_indices at 1. cbn [map].
  unfold t_entry at 1. cbn [t_D]. rewrite (hca5_PG_sfind_supd _ _ _ _ _ HS). cbn [e_index hca5_PG_E'].
  fold (t_indices (mkT (supd (t_D T) a (mkEntry (e_peer E) (e_type E) idx)) (a :: vremove a (t_L T))) (vremove a (t_L T))).
  rewrite hca5_PG_indices_ne by apply hca5_PG_vremove_notin.
  cbn [filter]. rewrite Int.eq_true.
  replace (filter (fun i => Int.eq i idx) (t_indices T (vremove a (t_L T)))) with (@nil int).
  { reflexivity. }
  symmetry.
  induction (t_indices T (vremove a (t_L T))) as [|i l IH]; [reflexivity|].
  cbn [filter]. destruct (Int.eq i idx) eqn:Ei.
  - apply Int.same_if_eq in Ei. subst. exfalso. apply HF. left; auto.
  - apply IH. intros Hi; apply HF; right; auto.
Qed.

(* ---- the pool of hca3_pool ---- *)

Lemma hca5_PG_psfind (p: val) (KD: list kdraw) (E: entry) :
  ~ In (hs_addr p) (map kd_addr KD) ->
  sfind (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) (hs_addr p) = Some (Tsh, E).
Proof.
  induction KD as [|K KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_PG_psupd (p: val) (KD: list kdraw) (E E': entry) :
  ~ In (hs_addr p) (map kd_addr KD) ->
  supd (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) (hs_addr p) E' =
  map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E')].
Proof.
  induction KD as [|K KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    f_equal. apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_PG_pool_sfind p KD T :
  hca5_pool p KD T -> exists E, sfind (t_D T) (hs_addr p) = Some (Tsh, E) /\ e_peer E = p /\
    e_type E = IDX_HANDSHAKE.
Proof.
  intros [[E [HD [Hp Ht]]] [Hnd _]]. exists E. rewrite HD.
  inversion Hnd; subst. rewrite hca5_PG_psfind by assumption. auto.
Qed.

Lemma hca5_PG_succ T a : itable_wf T ->
  succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & Hinc & _). revert Hinc. generalize (t_L T) as L.
  induction L as [|x L IH]; simpl; intros Hinc; [auto|].
  destruct (EqDec_val x a).
  - destruct L as [|y L]; simpl; [auto|]. right. apply Hinc. right; left; auto.
  - apply IH. intros z Hz; apply Hinc; right; auto.
Qed.

Lemma hca5_PG_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hca5_PG_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[ep et ei] n hd [st lic sid eph rs re ss psk h ck ts ri]].
  unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite !Int.eq_true, !Int64.eq_true, !hca5_PG_bytes_eqb_refl, !Bool.eqb_reflx.
  destruct (EqDec_val ep ep); [|congruence]. destruct (EqDec_val n n); [|congruence].
  destruct (EqDec_val sid sid); [|congruence]. reflexivity.
Qed.

(* ---- separation: the table opened at p's handshake entry, the entry as a field of p at the world ---- *)

Definition hca5_PG_rest (tab: val) (T: tstate) (a: val) : mpred :=
  !! itable_wf T &&
  (@data_at Noise.CS Tsh t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a)).

Lemma hca5_PG_open tab T p E : @field_compatible Noise.CS t_peer [] p ->
  sfind (t_D T) (hs_addr p) = Some (Tsh, E) ->
  itable Tsh tab T =
  @field_at W_create_any Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (succ_in (t_L T) (hs_addr p), (Val.of_bool (vin (hs_addr p) (t_L T)),
     (Vint (e_type E), Vint (e_index E))))) p * hca5_PG_rest tab T (hs_addr p).
Proof.
  intros FC0 HS. assert (FC: @field_compatible W_create_any t_peer [] p).
  { apply (@field_compatible_change_composite Noise.CS W_create_any _); [prove_cs_preserve_type | exact FC0]. }
  unfold itable, hca5_PG_rest. rewrite (prot_rep3_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at, entry_val.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  erewrite <- (@data_at_change_composite Noise.CS W_create_any _ Tsh t_entry_s); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold hs_addr. simpl nested_field_offset.
  unfold OFS_PEER_HANDSHAKE. apply pred_ext; normalize; try (apply andp_right; [apply prop_right; auto|]); cancel.
Qed.

Lemma hca5_PG_open2 tab T p E idx : @field_compatible Noise.CS t_peer [] p ->
  sfind (t_D T) (hs_addr p) = Some (Tsh, hca5_PG_E' E idx) -> vin (hs_addr p) (t_L T) = true ->
  itable Tsh tab T =
  @field_at W_create_any Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (succ_in (t_L T) (hs_addr p), (Val.of_bool true, (Vint (e_type E), Vint idx)))) p *
  hca5_PG_rest tab T (hs_addr p).
Proof. intros FC HS HV. rewrite (hca5_PG_open tab T p _ FC HS), HV. reflexivity. Qed.

Lemma hca5_PG_iter_ptr L (D: list (val * share * entry)) x :
  In x (saddrs D) -> iter_sepcon (pool_item_rep L) D |-- !! isptr x.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros Hx; [contradiction|].
  destruct Hx as [<-|Hx].
  - unfold pool_item_rep at 1, entry_at. entailer!. apply field_compatible_isptr in H; auto.
  - sep_apply (IH Hx). entailer!.
Qed.

Lemma hca5_PG_succ_ok tab T p : isptr p -> itable_wf T ->
  hca5_PG_rest tab T (hs_addr p) |--
  !! (succ_in (t_L T) (hs_addr p) = nullval \/ isptr (succ_in (t_L T) (hs_addr p))).
Proof.
  intros Hp WF. destruct (hca5_PG_succ T (hs_addr p) WF) as [N|I].
  { apply prop_right; auto. }
  destruct (EqDec_val (succ_in (t_L T) (hs_addr p)) (hs_addr p)) as [Eq|Ne].
  { apply prop_right. right. rewrite Eq. unfold hs_addr. destruct p; try contradiction; simpl; auto. }
  unfold hca5_PG_rest. Intros.
  sep_apply (hca5_PG_iter_ptr (t_L T) _ _ (prot_rep3_saddrs_sdel _ _ _ I Ne)). entailer!.
Qed.

(* the snapshot struct at the world *)
Lemma hca5_PG_xW sh sn p :
  @data_at HCS sh t_hsnap (hsnap_val sn) p = @data_at W_create_any sh t_hsnap (hsnap_val sn) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_create_any hca5_PG_cceH sh t_hsnap (hsnap_val sn)
    (hsnap_val sn) (@JMeq_refl _ (hsnap_val sn)) ltac:(vm_compute; reflexivity))).
Qed.

(* the same at the world, with the value typed at the world *)
Definition hca5_PG_xvalW (s: hsnap) : @reptype W_create_any t_hsnap :=
  let E := sn_entry s in let H := sn_hs s in
  (e_peer E, (sn_next s, (Val.of_bool (sn_hashed s), (Vint (e_type E), (Vint (e_index E),
  (Vint (hs_state H), (Vlong (hs_lic H), (hs_sid H, (bytes (hs_eph H), (bytes (hs_rstatic H),
  (bytes (hs_reph H), (bytes (hs_ss H), (bytes (hs_psk H), (bytes (hs_hash H), (bytes (hs_ck H),
  (bytes (hs_ts H), Vint (hs_rindex H))))))))))))))))).

Lemma hca5_PG_xW2 sh sn p :
  @data_at HCS sh t_hsnap (hsnap_val sn) p = @data_at W_create_any sh t_hsnap (hca5_PG_xvalW sn) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_create_any hca5_PG_cceH sh t_hsnap (hsnap_val sn)
    (hca5_PG_xvalW sn) (@JMeq_refl _ (hsnap_val sn)) ltac:(vm_compute; reflexivity))).
Qed.

(* the shim's globals but wg_shim_random_u32 *)
Definition hca5_PG_srest (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)).

Lemma hca5_PG_uint sh (v: val) p : @data_at Noise.CS sh tuint v p = @data_at W_create_any sh tuint v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_create_any _ sh tuint v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hca5_PG_shim gv S w : shim_state4 gv S w =
  @data_at W_create_any Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32) * (hca5_PG_srest gv S * refwarn4 gv w).
Proof.
  unfold shim_state4, shim_core, hca5_PG_srest. rewrite <- hca5_PG_uint.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hca5_PG_vp sh p P : sepalg.nonidentity sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros N. unfold peer_rep. apply andp_left2. repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.

Lemma hca5_PG_vdev wa D : device_rep Tsh wa D = vobjs W_create_any [VDev Tsh wa D].
Proof. unfold vobjs; simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hca5_PG_pre T p E' P H wa D : itable_wf T -> e_peer E' = p -> hs_sid H = id_addr wa ->
  t_entry T (hs_addr p) = Some E' ->
  Forall (vp_ok (hs_own p T [VDev Tsh wa D])) (hs_ptrs (snap_of T (hs_addr p) E' H) (hs_snap_cur T p (p_set_hs P H))).
Proof.
  intros WF HP HS HE. unfold hs_snap_cur, t_entry_d. rewrite HE.
  unfold hs_ptrs, hs_ptrs_nn, snap_of. cbn [sn_next sn_entry sn_hs p_hs p_set_hs].
  unfold hs_own, vobjs_addrs. cbn [map concat vobj_addrs app].
  assert (Hs: vp_ok (p :: saddrs (t_D T) ++ [wa; id_addr wa; cc_addr wa]) (succ_in (t_L T) (hs_addr p))).
  { destruct (hca5_PG_succ T (hs_addr p) WF) as [N|I]; [left; auto|].
    right; right; apply in_or_app; left; auto. }
  assert (Hp: vp_ok (p :: saddrs (t_D T) ++ [wa; id_addr wa; cc_addr wa]) (e_peer E')) by (right; left; auto).
  assert (Hi: vp_ok (p :: saddrs (t_D T) ++ [wa; id_addr wa; cc_addr wa]) (hs_sid H)).
  { right; right; apply in_or_app; right; rewrite HS; simpl; auto. }
  repeat (apply Forall_cons; [assumption|]); apply Forall_nil.
Qed.

Lemma hca5_PG_cur T p E' P H : t_entry T (hs_addr p) = Some E' ->
  hs_snap_cur T p (p_set_hs P H) = snap_of T (hs_addr p) E' H.
Proof. intros HE. unfold hs_snap_cur, t_entry_d. rewrite HE. reflexivity. Qed.

Lemma hca5_PG_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SF x25519 gv L FR w)
    hca5_PG
    (overridePost (hca5_SG x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_SF, hca5_Delta, hca5_R, hca5_PG. simplify_func_tycontext. abbreviate_semax.
  Intros R P T KD E b H' idx T' S' S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_p L)) as FCp by (unfold peer_rep; entailer!).
  destruct (hca5_PG_pool_sfind _ _ _ H1) as (E0 & HS0 & HpE & HtE).
  assert (E0 = E) by (unfold t_entry in H2; rewrite HS0 in H2; congruence). subst E0.
  apply semax_if_seq. forward_if.
  - destruct b; [| match goal with Hx: Int.repr 0 <> Int.zero |- _ => exfalso; apply Hx; reflexivity end]. destruct H5 as (-> & Hfr & Hu).
    destruct (hca5_PG_tD T (hs_addr (l_p L)) E idx H2) as [HD' HL'].
    assert (HS': sfind (t_D (t_insert T (hs_addr (l_p L)) idx)) (hs_addr (l_p L)) = Some (Tsh, hca5_PG_E' E idx))
      by (rewrite HD'; eapply hca5_PG_sfind_supd; eauto).
    assert (HE': t_entry (t_insert T (hs_addr (l_p L)) idx) (hs_addr (l_p L)) = Some (hca5_PG_E' E idx))
      by (unfold t_entry; rewrite HS'; reflexivity).
    pose proof (hca5_PG_count T _ E idx H2 Hfr) as Hcnt.
    assert (Hvin: vin (hs_addr (l_p L)) (t_L (t_insert T (hs_addr (l_p L)) idx)) = true).
    { rewrite HL'. unfold vin. destruct (in_dec _ _ _) as [_|N]; [auto | exfalso; apply N; left; auto]. }
    assert (Hin: In (hs_addr (l_p L)) (saddrs (t_D (t_insert T (hs_addr (l_p L)) idx))))
      by (eapply prot_rep3_saddrs_in, prot_rep3_sfind_In; eauto).
    assert (HTT: exists i, t_insert T (hs_addr (l_p L)) idx = t_insert T (hs_addr (l_p L)) i) by eauto.
    set (T' := t_insert T (hs_addr (l_p L)) idx) in *.
    clearbody T'.
    assert_PROP (itable_wf T') as WF by (unfold itable; entailer!).
    rewrite hca5_PG_shim.
    rewrite (hca5_PG_open2 (l_ita L) T' (l_p L) E idx FCp HS' Hvin). Intros.
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    + apply ENTAIL_refl.
    + forward. forward.
      forward_if (temp HC._t'24 (Vint Int.one)).
      { sep_apply (derives_refl' _ _ (eq_sym (hca5_PG_open2 (l_ita L) T' (l_p L) E idx FCp HS' Hvin))).
        forward_call (Tsh, l_ita L, T', hs_addr (l_p L)).
        rewrite Hvin. forward.
        rewrite (hca5_PG_open2 (l_ita L) T' (l_p L) E idx FCp HS' Hvin). Intros.
        entailer!. }
      { match goal with Hn: idx <> s_u32 S' |- _ => exfalso; apply Hn; rewrite Hu; reflexivity end. }
      forward_if (temp HC._t'26 (Vint Int.one)).
      { forward.
        sep_apply (derives_refl' _ _ (eq_sym (hca5_PG_open2 (l_ita L) T' (l_p L) E idx FCp HS' Hvin))).
        forward_call (Tsh, l_ita L, T', idx).
        rewrite Hcnt, if_true by auto. forward.
        rewrite (hca5_PG_open2 (l_ita L) T' (l_p L) E idx FCp HS' Hvin). Intros.
        entailer!. }
      { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
      forward_if.
      { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + assert_PROP (succ_in (t_L T') (hs_addr (l_p L)) = nullval \/ isptr (succ_in (t_L T') (hs_addr (l_p L))))
        as Hsucc.
      { sep_apply (hca5_PG_succ_ok (l_ita L) T' (l_p L) ltac:(apply field_compatible_isptr in FCp; exact FCp) WF).
        entailer!. }
      forward.
      { entailer!. destruct Hsucc as [Hn | Hsp]; [rewrite Hn; simpl; auto; reflexivity|].
        destruct (succ_in _ _); try contradiction; simpl; auto. }
      rewrite hca5_PG_xW2.
      forward. forward. forward. forward.
      match goal with |- context [@data_at W_create_any Tsh t_hsnap ?v (l_x L)] =>
        replace v with (hca5_PG_xvalW (snap_of T' (hs_addr (l_p L)) (hca5_PG_E' E idx) H')) end.
      2: { unfold hca5_PG_xvalW, snap_of. cbn [sn_entry sn_next sn_hashed sn_hs hca5_PG_E' e_peer e_type e_index fst snd].
           rewrite Hvin, Hu. reflexivity. }
      rewrite <- hca5_PG_xW2.
      sep_apply (derives_refl' _ _ (eq_sym (hca5_PG_open2 (l_ita L) T' (l_p L) E idx FCp HS' Hvin))).
      sep_apply (derives_refl' _ _ (eq_sym (hca5_PG_shim gv S' w))).
      rewrite (hca5_PG_vdev (l_wa L)).
      change (peer_rep Tsh (l_p L) (p_set_hs P H')) with (hs_mem true Tsh (l_p L) (p_set_hs P H')).
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      * apply ENTAIL_refl.
      * forward_call (Tsh, l_x L, snap_of T' (hs_addr (l_p L)) (hca5_PG_E' E idx) H', Tsh, l_p L, p_set_hs P H',
                      true, Tsh, l_ita L, T', [VDev Tsh (l_wa L) (hca5_D x25519 R L)]).
        { split; [repeat constructor; simpl; auto|]. apply hca5_PG_pre; auto. }
        rewrite (hca5_PG_cur T' (l_p L) _ P H' HE').
        rewrite (hca5_PG_snap_refl (snap_of T' (hs_addr (l_p L)) (hca5_PG_E' E idx) H')).
        rewrite <- hca5_PG_xW.
        forward_if.
        { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
        forward. entailer!.
      * forward. apply ENTAIL_refl.
      * unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hca5_SG.
        rewrite <- (hca5_PG_vdev (l_wa L)). unfold hs_mem.
        Exists R P T KD H' T' S' S0.
        unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
        sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of T' (hs_addr (l_p L)) (hca5_PG_E' E idx) H')) (l_x L)).
        entailer!.
  - destruct b; [match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end|]. hnf in H5. subst T'.
    assert_PROP (itable_wf T) as WF by (unfold itable; entailer!).
    assert (Hin: In (hs_addr (l_p L)) (saddrs (t_D T)))
      by (eapply prot_rep3_saddrs_in, prot_rep3_sfind_In; eauto).
    rewrite (hca5_PG_vdev (l_wa L)).
    change (peer_rep Tsh (l_p L) (p_set_hs P H')) with (hs_mem true Tsh (l_p L) (p_set_hs P H')).
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) ?S)) _ _ =>
      forward_loop (PROPx [] (LOCALx Q S)) continue: (PROPx [] (LOCALx Q S)) break: (PROPx [] (LOCALx Q S)) end.
    + entailer!.
    + forward_call (Tsh, l_x L, snap_of T (hs_addr (l_p L)) E H', Tsh, l_p L, p_set_hs P H',
                    true, Tsh, l_ita L, T, [VDev Tsh (l_wa L) (hca5_D x25519 R L)]).
      { split; [repeat constructor; simpl; auto|]. apply hca5_PG_pre; auto. }
      rewrite (hca5_PG_cur T (l_p L) _ P H' H2).
      rewrite (hca5_PG_snap_refl (snap_of T (hs_addr (l_p L)) E H')).
      rewrite <- hca5_PG_xW.
      forward_if.
      { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hca5_SG.
      rewrite <- (hca5_PG_vdev (l_wa L)). unfold hs_mem.
      Exists R P T KD H' T S' S0.
      unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
      sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E H')) (l_x L)).
      entailer!.
Qed.
