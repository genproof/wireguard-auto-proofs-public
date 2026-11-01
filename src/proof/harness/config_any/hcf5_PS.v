(* law config_any: main's phase PS, statements 18..24: kents_snap(kes), head0 = it.head, dev_take, hs_take, pr_take, refs0 = p.refcount.refcount, shim_take.
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

#[local] Instance hcf5_ps_CCE : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.

Lemma hcf5_ps_refs_nest sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at Noise.CS sh t_peer [StructField I._refcount; StructField I._refcount] (Vint v) p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hcf5_ps_refs_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at W_config_any sh (Tstruct HF._wg_peer noattr) [StructField HF._refcount; StructField HF._refcount] (Vint v) p.
Proof.
  rewrite hcf5_ps_refs_nest.
  change (Tstruct HF._wg_peer noattr) with t_peer. change HF._refcount with I._refcount.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

(* peer_rep without the reference count *)
Definition hcf5_ps_prestR (sh: share) (p: val) (P: peer) : mpred :=
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hcf5_ps_open sh p P :
  peer_rep sh p P =
  (hcf5_ps_prestR sh p P *
   @field_at W_config_any sh (Tstruct HF._wg_peer noattr) [StructField HF._refcount; StructField HF._refcount] (Vint (p_refs P)) p)%logic.
Proof.
  rewrite <- hcf5_ps_refs_conv.
  unfold peer_rep, hcf5_ps_prestR. apply pred_ext; Intros; entailer!.
Qed.

Lemma hcf5_ps_close sh p P :
  (hcf5_ps_prestR sh p P *
   @field_at W_config_any sh (Tstruct HF._wg_peer noattr) [StructField HF._refcount; StructField HF._refcount] (Vint (p_refs P)) p)%logic
  |-- peer_rep sh p P.
Proof. rewrite hcf5_ps_open. apply derives_refl. Qed.

Lemma hcf5_ps_itab_conv sh (v: val) p : @data_at Noise.CS sh t_itab v p = @data_at W_config_any sh t_itab v p.
Proof.
  apply equal_f. apply (@data_at_change_composite Noise.CS W_config_any _ sh t_itab); [apply JMeq_refl | reflexivity].
Qed.

Lemma hcf5_ps_kents_ptr l KE : kents_rep W_config_any l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; simpl.
  - entailer!.
  - Intros nx. unfold kent_cell. Intros. sep_apply (IH nx). Intros. apply prop_right.
    constructor; auto. exact (@field_compatible_isptr CKS _ _ _ H0).
Qed.

Lemma hcf5_ps_succ_in l a : succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [| x l IH]; simpl; [auto |].
  destruct (EqDec_val x a).
  - destruct l as [| y l]; simpl; auto.
  - destruct IH; auto.
Qed.

Lemma hcf5_ps_khead T KE : hcf5_khead (map (kent_snapped T) KE) = hcf5_khead KE.
Proof. destruct KE; reflexivity. Qed.

Lemma hcf5_ps_addrs T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. reflexivity. Qed.

Lemma hcf5_ps_slots T KE P : hcf5_slots_ok KE P -> hcf5_slots_ok (map (kent_snapped T) KE) P.
Proof. unfold hcf5_slots_ok. rewrite hcf5_ps_addrs. auto. Qed.

Lemma hcf5_ps_Tok L T KE : hcf5_T_ok L KE false T -> hcf5_T_ok L (map (kent_snapped T) KE) false T.
Proof.
  unfold hcf5_T_ok. rewrite hcf5_ps_addrs. intros (A & B & C & D & E).
  refine (conj A (conj _ (conj C (conj D E)))). apply Forall_map. exact B.
Qed.

Lemma hcf5_ps_ksnap L T KE : itable_wf T -> hcf5_T_ok L KE false T ->
  hcf5_ksnap_ok L T (map (kent_snapped T) KE).
Proof.
  intros (_ & Hincl & _) (_ & B & _). unfold hcf5_ksnap_ok. apply Forall_map.
  eapply Forall_impl; [| exact B]. intros e [_ He]. simpl. split; [discriminate |].
  unfold kent_ptrs; simpl. rewrite He.
  assert (Hs: vp_ok (l_p L :: saddrs (t_D T)) (succ_in (t_L T) (ke_addr e))).
  { destruct (hcf5_ps_succ_in (t_L T) (ke_addr e)) as [-> | Hi]; [left; reflexivity |].
    right. right. apply Hincl. exact Hi. }
  repeat (apply Forall_cons; [first [exact Hs | right; left; reflexivity] |]). apply Forall_nil.
Qed.

Section PS.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_PS_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SK gv L FR) hcf5_PS
    (overridePost (hcf5_SX0 gv L FR) (hcf5_R gv)).
Proof.
  intros HH. unfold hcf5_SK, hcf5_SX0, hcf5_Delta, hcf5_R, hcf5_PS. simplify_func_tycontext. abbreviate_semax.
  Intros R S w D P T KE.
  unfold hcf5_globs, hcf5_pre, hcf5_lvars. cbn [app].
  pose proof H2 as (Dd & Dcc & Dpt & Dit).
  pose proof H3 as (Pdev & Ppk & Psid & Prs).
  pose proof H5 as (Tsa & Tke & Tts & Tpe & _).
  assert_PROP (isptr (l_w L) /\ isptr (l_it L) /\ isptr (l_pt L) /\ isptr (l_p L)) as Hptrs by entailer!.
  destruct Hptrs as (Pw & Pit & Ppt & Pp).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) KE) as Hkp
    by (sep_apply (hcf5_ps_kents_ptr (hcf5_khead KE) KE); entailer!).
  (* kents_snap(kes) *)
  forward_call (hcf5_khead KE, KE, Tsh, l_it L, T).
  { rewrite Forall_forall. intros e He. rewrite Tsa. split.
    - apply in_or_app. right. apply in_or_app. left. apply in_map. exact He.
    - rewrite Forall_forall in Tke. rewrite (proj2 (Tke e He)). intro E; rewrite E in Pp; contradiction. }
  Intros. unfold itable at 1. Intros.
  match goal with Hx: itable_wf _ |- _ => rename Hx into Hwf end.
  assert (Hhd: is_pointer_or_null (hd nullval (t_L T))).
  { destruct Hwf as (_ & Hincl & _). destruct (t_L T) as [| a l] eqn:E; simpl; [simpl; auto |].
    assert (Ha: In a (saddrs (t_D T))) by (apply Hincl; left; reflexivity).
    rewrite Tsa in Ha. simpl in Ha. apply in_app_or in Ha. destruct Ha as [Ha | [<- | []]].
    - apply in_map_iff in Ha. destruct Ha as (e & <- & He). rewrite Forall_forall in Hkp.
      specialize (Hkp e He). destruct (ke_addr e); try contradiction; exact I.
    - unfold hs_addr. destruct (l_p L); try contradiction; exact I. }
  rewrite hcf5_ps_itab_conv. forward. rewrite <- hcf5_ps_itab_conv.
  gather_SEP 1 2. replace_SEP 0 (itable Tsh (l_it L) T).
  { unfold itable. entailer!. }
  (* dev_take(&ds, &w) *)
  replace_SEP 3 (ptable Tsh (d_ptab D) (l_p L)) by (rewrite Dpt; entailer!).
  forward_call (Tsh, l_ds L, Tsh, l_w L, D, Tsh, l_p L).
  { rewrite Dd, Dcc, Dpt, Dit.
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction]. }
  replace_SEP 2 (ptable Tsh (l_pt L) (l_p L)) by (rewrite Dpt; entailer!).
  (* hs_take(&hs0, &p.handshake): p whole *)
  assert (Hin: In (hs_addr (l_p L)) (saddrs (t_D T))) by
    (rewrite Tsa; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
  forward_call (Tsh, l_hs0 L, Tsh, l_p L, P, true, Tsh, l_it L, T).
  { split.
    - rewrite Tpe. intro E; rewrite E in Pp; contradiction.
    - rewrite Psid. unfold id_addr. destruct (l_w L); try contradiction. discriminate. }
  change (hs_mem true Tsh (l_p L) P) with (peer_rep Tsh (l_p L) P).
  (* pr_take(&ps0, &p) *)
  forward_call (Tsh, l_ps0 L, Tsh, l_p L, P).
  { rewrite Pdev, Ppk.
    assert (Hnu: forall v, v = nullval \/ In v (map ke_addr KE) -> v <> Vundef).
    { intros v [-> | Hv]; [discriminate |]. apply list_in_map_inv in Hv. destruct Hv as (e & -> & He).
      rewrite Forall_forall in Hkp. specialize (Hkp e He). intro E; rewrite E in Hkp; contradiction. }
    unfold hcf5_slots_ok in H4.
    inversion H4 as [| ? ? S1 Hs1]; inversion Hs1 as [| ? ? S2 Hs2]; inversion Hs2 as [| ? ? S3 _].
    repeat (apply Forall_cons; [first [apply Hnu; assumption | intro E; rewrite E in Pw; contradiction | discriminate] |]).
    constructor. }
  (* refs0 = p.refcount.refcount *)
  rewrite (hcf5_ps_open Tsh (l_p L) P). Intros.
  forward.
  sep_apply (hcf5_ps_close Tsh (l_p L) P).
  (* shim_take(&ss) *)
  forward_call (gv, Tsh, l_ss L, S, w).
  assert (Hinv: hcf5_inv R L S w D P T (map (kent_snapped T) KE) false).
  { refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj _ (conj _ _))))))).
    - apply hcf5_ps_slots; exact H4.
    - apply hcf5_ps_Tok; exact H5.
    - apply hcf5_ps_ksnap; assumption. }
  assert (Hsame: hcf5_same L D P T (map (kent_snapped T) KE) S w D (hs_snap_cur T (l_p L) P) P (p_refs P) S w
                   (hd nullval (t_L T))).
  { refine (conj (hcf5_dev_eqb_refl _ _) (conj (hcf5_snap_eqb_refl _) (conj (hcf5_pr_eqb_refl _)
              (conj eq_refl (conj (hcf5_shim_eqb_refl _ _) (conj (hcf5_kents_same_snapped _ _) eq_refl)))))). }
  Exists R S w D P T (map (kent_snapped T) KE).
  Exists D (hs_snap_cur T (l_p L) P) P (p_refs P) S w (hd nullval (t_L T)).
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars. cbn [app].
  rewrite hcf5_ps_khead.
  entailer!.
Qed.

End PS.
