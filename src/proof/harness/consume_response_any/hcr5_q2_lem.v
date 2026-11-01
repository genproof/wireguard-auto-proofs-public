(* law consume_response_any, phase Q2: helpers - the preconditions of
   hnodes_snap4 / kents_snap4 / dev_take4 / consume_response (prot_specs4) from the state's invariants, the boot
   clock's store, the index table's head.  Port of hci5_P6.v's helpers and v1's hcr3_q2_A / hcr3_q2_C. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope Z_scope.

#[local] Instance hcr5_q2_cceN : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.

(* ---- the shim's boot clock ---- *)
Lemma hcr5_q2_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_consume_response_any sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hcr5_q2_rest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.

Lemma hcr5_q2_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_consume_response_any Ews tulong (Vlong (s_boot S)) (gv HR5._wg_shim_boottime_ns) *
     hcr5_q2_rest gv S))%logic.
Proof.
  unfold shim_core, hcr5_q2_rest. rewrite <- hcr5_q2_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hcr5_q2_shim_fold gv S n w : shim_ok S ->
  (@data_at W_consume_response_any Ews tulong (Vlong n) (gv HR5._wg_shim_boottime_ns) * hcr5_q2_rest gv S *
   refwarn4 gv w |-- shim_state4 gv (shim_set_boot S n) w)%logic.
Proof.
  intros HS. unfold shim_state4. rewrite hcr5_q2_core_open. unfold hcr5_q2_rest; cbn.
  entailer!.
Qed.

(* ---- the index table's head field at the world ---- *)
Lemma hcr5_q2_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_consume_response_any sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q2_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_consume_response_any sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hcr5_q2_itab_W. reflexivity. Qed.

Lemma hcr5_q2_itable_fold sht tab T : itable_wf T ->
  (@data_at W_consume_response_any sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hcr5_q2_itable_open. entailer!. Qed.

(* ---- pointers ---- *)
Lemma hcr5_q2_pn l NS : hnodes_rep4 W_consume_response_any l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hcr5_q2_kptrs l KE : kents_rep W_consume_response_any l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; cbn [kents_rep].
  - entailer!.
  - Intros nx. sep_apply (IH nx). unfold kent_cell. entailer!.
    constructor; [| assumption].
    match goal with X: field_compatible t_kent [] (ke_addr e) |- _ => destruct X; assumption end.
Qed.

(* ---- pure ---- *)
Lemma hcr5_q2_F2_in {A B: Type} (Rr: A -> B -> Prop) l1 l2 x :
  Forall2 Rr l1 l2 -> In x l1 -> exists y, In y l2 /\ Rr x y.
Proof.
  intros HF; induction HF as [| a b l1' l2' Hab HF IH]; simpl; [tauto |].
  intros [-> | Hin]; [exists b; auto |]. destruct (IH Hin) as (y & Hy & Hr). exists y; auto.
Qed.

Lemma hcr5_q2_f2r {A B: Type} (P: A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> Forall (fun y => exists x, In x l1 /\ P x y) l2.
Proof.
  induction 1; constructor.
  - exists x. split; [left; reflexivity | assumption].
  - eapply Forall_impl; [| exact IHForall2]. intros b (a & Ha & Hp). exists a. split; [right |]; assumption.
Qed.

Lemma hcr5_q2_sfind_nodup {A: Type} (D: list (val * share * A)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; simpl; [tauto |]. intros Hnd Hin.
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin]; [congruence |].
    exfalso. apply Hni. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto.
  - destruct Hin as [Heq | Hin]; [congruence | auto].
Qed.

Lemma hcr5_q2_entry_d T a sh E :
  NoDup (saddrs (t_D T)) -> In (a, sh, E) (t_D T) -> t_entry_d T a = E.
Proof.
  intros Hnd Hin. unfold t_entry_d, t_entry. rewrite (hcr5_q2_sfind_nodup _ _ _ _ Hnd Hin). reflexivity.
Qed.

Lemma hcr5_q2_in_saddrs {A: Type} (D: list (val * share * A)) a sh E : In (a, sh, E) D -> In a (saddrs D).
Proof. intros Hin. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto. Qed.

Lemma hcr5_q2_pknext head PS :
  pk_chain head PS -> Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun x => match x with (_, _, P) => p_pknext P <> Vundef end) PS.
Proof.
  revert head; induction PS as [| [[a sh] P] PS IH]; intros head Hc Hp; [constructor |].
  cbn in Hc. destruct Hc as [-> Hc]. inversion Hp as [| ? ? Ha Hp']; subst.
  constructor; [| eapply IH; eauto].
  destruct PS as [| [[b shb] Q] PS']; cbn in Hc.
  - rewrite Hc. discriminate.
  - destruct Hc as [-> _]. inversion Hp'; subst. cbn in *. destruct b; try contradiction; discriminate.
Qed.

Lemma hcr5_q2_head head PS : pk_chain head PS -> Forall (fun x => isptr (peer_addr4 x)) PS -> head <> Vundef.
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; intros Hc Hp.
  - subst; discriminate.
  - destruct Hc as [-> _]. inversion Hp; subst. cbn in *. destruct a; try contradiction; discriminate.
Qed.

Lemma hcr5_q2_pptrs L KA PS : Forall (hcr5_pok L KA) PS -> Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  intros H. eapply Forall_impl; [| exact H]. intros [[a sh] P] (_ & Ha & _). exact Ha.
Qed.

Lemma hcr5_q2_snap_pre L KE NS PS head nb T :
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  Forall (fun e => isptr (ke_addr e)) KE -> isptr (l_wa L) ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
            hs_sid (p_hs P) <> Vundef /\
            Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS.
Proof.
  intros (Hpok & _ & Hch & _ & _ & _) (_ & Hhs) (_ & _ & Hnd & _) Hkp Hwa.
  pose proof (hcr5_q2_pptrs _ _ _ Hpok) as Hptr.
  pose proof (hcr5_q2_pknext _ _ Hch Hptr) as Hpk.
  apply Forall_forall. intros [[p sh] P] Hin.
  rewrite Forall_forall in Hpok, Hptr, Hpk, Hkp.
  pose proof (Hptr _ Hin) as Hp. cbn in Hp.
  destruct (Hpok _ Hin) as (_ & _ & Hdev & Hsid & _ & _ & Hs).
  pose proof (Hpk _ Hin) as Hpn. cbn in Hpn.
  destruct (hcr5_q2_F2_in _ _ _ _ Hhs Hin) as ([[a she] E] & Hy & Hr).
  cbn in Hr. destruct Hr as (-> & -> & Hpe & _).
  apply skipn_In in Hy.
  assert (Hk: forall k, k = nullval \/ In k (hcr5_ka KE) -> k <> Vundef).
  { intros k [-> | Hk]; [discriminate|]. unfold hcr5_ka in Hk. apply in_map_iff in Hk. destruct Hk as (e & <- & He').
    specialize (Hkp _ He'). destruct (ke_addr e); try contradiction; discriminate. }
  rewrite Forall_forall in Hs.
  split; [| split; [| split]].
  - eapply hcr5_q2_in_saddrs; exact Hy.
  - rewrite (hcr5_q2_entry_d _ _ _ _ Hnd Hy), Hpe. destruct p; try contradiction; discriminate.
  - rewrite Hsid. unfold id_addr. destruct (l_wa L); try contradiction; discriminate.
  - repeat constructor.
    + rewrite Hdev. destruct (l_wa L); try contradiction; discriminate.
    + apply Hk, Hs; cbn; auto.
    + apply Hk, Hs; cbn; auto.
    + apply Hk, Hs; cbn; auto.
    + exact Hpn.
Qed.

Lemma hcr5_q2_ksnap_pre L KE NS PS head nb T :
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE.
Proof.
  intros (Hpok & _) (Hke & _) (_ & _ & Hnd & _).
  pose proof (hcr5_q2_pptrs _ _ _ Hpok) as Hptr. rewrite Forall_forall in Hptr.
  apply Forall_forall. intros e He.
  assert (HinK: In (ke_addr e) (hcr5_ka KE)) by (apply in_map, He).
  destruct (hcr5_q2_F2_in _ _ _ _ Hke HinK) as ([[a she] E] & Hy & Hr).
  cbn in Hr. destruct Hr as (-> & -> & Hpe & _).
  apply firstn_In in Hy. split.
  - eapply hcr5_q2_in_saddrs; exact Hy.
  - rewrite (hcr5_q2_entry_d _ _ _ _ Hnd Hy).
    apply in_map_iff in Hpe. destruct Hpe as (x & Hx & Hx'). rewrite <- Hx.
    specialize (Hptr _ Hx'). destruct x as [[q sh] Q]. cbn in *. destruct q; try contradiction; discriminate.
Qed.

Lemma hcr5_q2_hd_pn L KE NS PS head nb T :
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  Forall (fun e => isptr (ke_addr e)) KE ->
  is_pointer_or_null (hd nullval (t_L T)).
Proof.
  intros (Hpok & _) (Hke & Hhs) (_ & Hinc & _) Hk.
  pose proof (hcr5_q2_pptrs _ _ _ Hpok) as Hp.
  destruct (t_L T) as [| v l] eqn:E; cbn; [reflexivity|].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv. apply in_map_iff in Hv. destruct Hv as ([[a sh] D] & Ha & Hin). cbn in Ha. subst a.
  rewrite <- (firstn_skipn (length (hcr5_ka KE)) (t_D T)) in Hin. apply in_app_or in Hin.
  rewrite Forall_forall in Hp, Hk. destruct Hin as [Hin | Hin].
  - apply hcr5_q2_f2r in Hke. rewrite Forall_forall in Hke. destruct (Hke _ Hin) as (k & Hk' & -> & _).
    unfold hcr5_ka in Hk'. apply in_map_iff in Hk'. destruct Hk' as (e & <- & He). specialize (Hk _ He).
    destruct (ke_addr e); try contradiction; exact I.
  - apply hcr5_q2_f2r in Hhs. rewrite Forall_forall in Hhs. destruct (Hhs _ Hin) as ([[p shp] P] & HP & -> & _).
    specialize (Hp _ HP). cbn in Hp. unfold hs_addr. destruct p; try contradiction; exact I.
Qed.

Lemma hcr5_q2_sfind (PS: list (val * share * peer)) a sh P :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [| [[b sh'] P'] PS IH]; intros Hnd Hin; [destruct Hin |].
  cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst. cbn [sfind].
  destruct Hin as [Heq | Hin].
  - inversion Heq; subst. rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false; [auto |]. intro Hba; subst b. apply Hnin.
    change a with (peer_addr4 (a, sh, P)). apply in_map. exact Hin.
Qed.

Lemma hcr5_q2_refs L KA (x: val * share * peer) :
  hcr5_pok L KA x -> p_refs (snd x) <> Int.zero.
Proof.
  destruct x as [[a sh] P]. intros (_ & _ & _ & _ & _ & Hr & _). cbn [snd].
  intro Hc. rewrite Hc, Int.unsigned_zero in Hr. lia.
Qed.

(* the call's preconditions on the pool and the references *)
Lemma hcr5_q2_ppok L KA NS PS head nb T :
  hcr5_list_ok L KA NS PS head nb -> hcr5_pool KA PS T -> pool_peers_ok T PS.
Proof.
  intros (Hpok & _ & _ & _ & Hnd & _) (Hke & Hhs).
  unfold pool_peers_ok. rewrite <- (firstn_skipn (length KA) (t_D T)). apply Forall_app. split.
  - apply hcr5_q2_f2r in Hke. eapply Forall_impl; [| exact Hke].
    intros [[a sh] E] (K & HK & Ha & Hsh & Hp & Ht).
    split; [| right; exact Ht].
    apply in_map_iff in Hp. destruct Hp as ([[p shp] P] & Hp & HP). cbn in Hp. rewrite <- Hp.
    exists shp, P. split; [apply hcr5_q2_sfind; assumption |].
    apply (hcr5_q2_refs L KA (p, shp, P)). rewrite Forall_forall in Hpok. apply Hpok. exact HP.
  - apply hcr5_q2_f2r in Hhs. eapply Forall_impl; [| exact Hhs].
    intros [[a sh] E] ([[p shp] P] & HP & Ha & Hsh & Hp & Ht).
    split; [| left; split; [exact Ht | rewrite Hp; exact Ha]].
    exists shp, P. rewrite Hp. split; [apply hcr5_q2_sfind; assumption |].
    apply (hcr5_q2_refs L KA (p, shp, P)). rewrite Forall_forall in Hpok. apply Hpok. exact HP.
Qed.

Lemma hcr5_q2_refs_ok L KA PS : Forall (hcr5_pok L KA) PS -> peers_refs_ok PS.
Proof.
  intros H. unfold peers_refs_ok. eapply Forall_impl; [| exact H].
  intros [[a sh] P] (_ & _ & _ & _ & _ & Hr & _). exact Hr.
Qed.
