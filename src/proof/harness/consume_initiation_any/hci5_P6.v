(* law consume_initiation_any: main's phase P6, statements 20..28: now = draw_boottime(); the flood boundary (now = A's last consumption + 20 ms +- 2 ns if below 2^62); wg_shim_boottime_ns = now; hnodes_snap(peers); kents_snap(kes); dev_take(&ds, &wb); head0 = itb.head; shim_take(&ss); ret = wg_noise_handshake_consume_initiation(msg, &wb).
   (states: hci5_defs.v).
   harness/consume_initiation_any/hci3_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

#[local] Instance hci5_p6_cceN : change_composite_env Noise.CS W_consume_initiation_any.
Proof. make_cs_preserve Noise.CS W_consume_initiation_any. Defined.
#[local] Instance hci5_p6_cceK : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.

Section hci5_p6_helpers.
Local Open Scope logic.
(* ---- accessors: P |-- Q * (Q -* P) ---- *)
Definition hci5_p6_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hci5_p6_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hci5_p6_acc_refl Q : hci5_p6_acc Q Q.
Proof.
  unfold hci5_p6_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hci5_p6_acc_eq Q A : Q = A -> hci5_p6_acc Q A.
Proof. intros ->. apply hci5_p6_acc_refl. Qed.

Lemma hci5_p6_acc_l Q A F : hci5_p6_acc Q A -> hci5_p6_acc Q (A * F).
Proof.
  unfold hci5_p6_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hci5_p6_acc_r Q A F : hci5_p6_acc Q A -> hci5_p6_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hci5_p6_acc_l, H. Qed.

Lemma hci5_p6_acc_prop Q (c: Prop) A : (c -> hci5_p6_acc Q A) -> hci5_p6_acc Q (!! c && A).
Proof.
  unfold hci5_p6_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hci5_p6_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hci5_p6_acc Q (A x)) -> hci5_p6_acc Q (EX x, A x).
Proof.
  unfold hci5_p6_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hci5_p6_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hci5_p6_acc Q A) -> hci5_p6_acc Q A.
Proof.
  unfold hci5_p6_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hci5_p6_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hci5_p6_acc Q (f x) -> hci5_p6_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hci5_p6_acc_l, H | apply hci5_p6_acc_r, IH, Hin].
Qed.

(* the node's field p, at the world *)
Lemma hci5_p6_node_split p sn r rs nx x :
  @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x |--
  @field_at W Ews t_hnode4 [StructField HC._p] p x *
  (@field_at W Ews t_hnode4 [StructField HC._p] p x -* @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ p x); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

Lemma hci5_p6_node_acc l NS N : In N NS ->
  hci5_p6_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) (hnodes_rep4 W l NS).
Proof.
  revert l; induction NS as [|N0 NS IH]; intros l Hin; [destruct Hin|]. cbn [hnodes_rep4].
  apply hci5_p6_acc_prop; intros Hl. apply hci5_p6_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hci5_p6_acc_l, hci5_p6_acc_l, hci5_p6_acc_r. apply hci5_p6_node_split.
  - apply hci5_p6_acc_r, IH, Hin.
Qed.

Lemma hci5_p6_acc_trans Q B P : hci5_p6_acc Q B -> hci5_p6_acc B P -> hci5_p6_acc Q P.
Proof.
  unfold hci5_p6_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Section hci5_p6_N.
#[local] Existing Instance Noise.CS.
Lemma hci5_p6_acc_lic sh h H :
  hci5_p6_acc (field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h) (hs_rep sh h H).
Proof.
  unfold hs_rep. apply hci5_p6_acc_prop; intros _.
  do 13 apply hci5_p6_acc_l. apply hci5_p6_acc_r, hci5_p6_acc_refl.
Qed.
Lemma hci5_p6_acc_hs sh a Q : hci5_p6_acc (hs_rep sh (hs_addr a) (p_hs Q)) (peer_rep sh a Q).
Proof.
  unfold peer_rep. apply hci5_p6_acc_prop; intros _.
  do 7 apply hci5_p6_acc_l. apply hci5_p6_acc_r, hci5_p6_acc_refl.
Qed.
End hci5_p6_N.

Lemma hci5_p6_pk_lic sh a Q : hci5_p6_acc
  (@field_at W sh t_peer [StructField HC._last_initiation_consumption; StructField HC._handshake]
     (Vlong (hs_lic (p_hs Q))) a) (peer_rep sh a Q).
Proof.
  rewrite <- (@field_at_change_composite Noise.CS W _ sh t_peer [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong (hs_lic (p_hs Q))) (Vlong (hs_lic (p_hs Q))) (JMeq_refl _))
    by (vm_compute; reflexivity).
  apply hci5_p6_acc_pure with (c := @field_compatible Noise.CS t_peer [] a); [unfold peer_rep; entailer! | intros FC].
  pose proof (@field_at_app Noise.CS sh t_peer [StructField HC._last_initiation_consumption] [StructField HC._handshake]
     (Vlong (hs_lic (p_hs Q))) (Vlong (hs_lic (p_hs Q))) a (JMeq_refl _)) as E.
  change ([StructField HC._last_initiation_consumption] ++ [StructField HC._handshake]) with
    [StructField HC._last_initiation_consumption; StructField HC._handshake] in E.
  rewrite E; clear E.
  rewrite field_address_offset by auto with field_compatible.
  change (offset_val _ a) with (hs_addr a).
  change (nested_field_type t_peer [StructField HC._handshake]) with t_hs.
  change HC._last_initiation_consumption with I._last_initiation_consumption.
  exact (hci5_p6_acc_trans _ _ _ (hci5_p6_acc_lic sh (hs_addr a) (p_hs Q)) (hci5_p6_acc_hs sh a Q)).
Qed.

Lemma hci5_p6_peers_lic PS a sh P : In (a, sh, P) PS -> hci5_p6_acc
  (@field_at W sh t_peer [StructField HC._last_initiation_consumption; StructField HC._handshake]
     (Vlong (hs_lic (p_hs P))) a) (peers_rep PS).
Proof.
  intros Hin. unfold peers_rep. apply (hci5_p6_acc_iter _ _ (a, sh, P)); [exact Hin|].
  apply hci5_p6_pk_lic.
Qed.

End hci5_p6_helpers.

Lemma hci5_p6_ptrs PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  induction PS as [| [[a sh] P] PS IH]; unfold peers_rep in *; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_item_rep at 1, peer_rep. entailer!.
    constructor; [cbn; destruct H0; assumption | assumption].
Qed.

(* ---- the shim's boot clock (as hci5_P1's hci5_p1_core_open) ---- *)
Lemma hci5_p6_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_consume_initiation_any sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_initiation_any _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hci5_p6_rest (gv: globals) (S: shim) : mpred :=
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

Lemma hci5_p6_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_consume_initiation_any Ews tulong (Vlong (s_boot S)) (gv HC._wg_shim_boottime_ns) *
     hci5_p6_rest gv S))%logic.
Proof.
  unfold shim_core, hci5_p6_rest. rewrite <- hci5_p6_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hci5_p6_shim_fold gv S n w : shim_ok S ->
  (@data_at W_consume_initiation_any Ews tulong (Vlong n) (gv HC._wg_shim_boottime_ns) * hci5_p6_rest gv S *
   refwarn4 gv w |-- shim_state4 gv (shim_set_boot S n) w)%logic.
Proof.
  intros HS. unfold shim_state4. rewrite hci5_p6_core_open. unfold hci5_p6_rest; cbn.
  entailer!.
Qed.

(* ---- the index table's head field at the world ---- *)
Lemma hci5_p6_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_consume_initiation_any sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_initiation_any _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hci5_p6_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_consume_initiation_any sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hci5_p6_itab_W. reflexivity. Qed.

Lemma hci5_p6_itable_fold sht tab T : itable_wf T ->
  (@data_at W_consume_initiation_any sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hci5_p6_itable_open. entailer!. Qed.

(* ---- pointers ---- *)
Lemma hci5_p6_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hci5_p6_kptrs l KE : kents_rep W l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; cbn [kents_rep].
  - entailer!.
  - Intros nx. sep_apply (IH nx). unfold kent_cell. entailer!.
    constructor; [| assumption].
    match goal with X: field_compatible t_kent [] (ke_addr e) |- _ => destruct X; assumption end.
Qed.

Section hci5_p6_pure.
Variable x25519: list byte -> list byte -> list byte.

Lemma hci5_p6_snap_pre R L PS KE T :
  Forall (hci5_pok x25519 R L) PS -> hci5_T_ok PS KE T -> hci5_slots_ok KE PS ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> Forall (fun e => isptr (ke_addr e)) KE -> isptr (l_wb L) ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
            hs_sid (p_hs P) <> Vundef /\
            Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS.
Proof.
  intros Hpok (HT1 & HT2 & HT3 & HT4) Hsl Hptr Hkp Hwb. unfold hci5_slots_ok in Hsl.
  rewrite Forall_forall in Hpok, HT3, Hsl, Hptr, Hkp |- *. intros [[p sh] P] Hin.
  pose proof (Hptr _ Hin) as Hp. cbn in Hp.
  destruct (Hpok _ Hin) as (_ & Hdev & Hsid & _ & _ & _ & _ & Hpk).
  pose proof (HT3 _ Hin) as He. cbn in He.
  pose proof (Hsl _ Hin) as Hs. cbn in Hs.
  assert (Hk: forall k, k = nullval \/ In k (map ke_addr KE) -> k <> Vundef).
  { intros k [-> | Hk]; [discriminate|]. apply in_map_iff in Hk. destruct Hk as (e & <- & He').
    specialize (Hkp _ He'). destruct (ke_addr e); try contradiction; discriminate. }
  rewrite Forall_forall in Hs.
  split; [| split; [| split]].
  - rewrite HT1. apply in_or_app. right. apply in_map_iff. exists (p, sh, P). split; [reflexivity | exact Hin].
  - rewrite He. destruct p; try contradiction; discriminate.
  - rewrite Hsid. unfold id_addr. destruct (l_wb L); try contradiction; discriminate.
  - repeat constructor.
    + rewrite Hdev. destruct (l_wb L); try contradiction; discriminate.
    + apply Hk, Hs; cbn; auto.
    + apply Hk, Hs; cbn; auto.
    + apply Hk, Hs; cbn; auto.
    + destruct (p_pknext P); try contradiction; discriminate.
Qed.

Lemma hci5_p6_ksnap_pre PS KE T :
  hci5_T_ok PS KE T -> Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE.
Proof.
  intros (HT1 & HT2 & HT3 & HT4) Hptr. rewrite Forall_forall in HT4, Hptr |- *. intros e He. split.
  - rewrite HT1. apply in_or_app. left. apply in_map, He.
  - specialize (HT4 _ He). apply in_map_iff in HT4. destruct HT4 as (x & Hx & Hx'). rewrite <- Hx.
    specialize (Hptr _ Hx'). destruct (peer_addr4 x); try contradiction; discriminate.
Qed.

Lemma hci5_p6_head head PS : pk_chain head PS -> Forall (fun x => isptr (peer_addr4 x)) PS -> head <> Vundef.
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; intros Hc Hp.
  - subst; discriminate.
  - destruct Hc as [-> _]. inversion Hp; subst. cbn in *. destruct a; try contradiction; discriminate.
Qed.

Lemma hci5_p6_cons_pre R L PS : Forall (hci5_pok x25519 R L) PS ->
  Forall (fun x => match x with (_, _, P) =>
            Int64.signed (hs_lic (p_hs P)) <= Int64.max_signed - 20000000 end) PS /\ peers_refs_ok PS.
Proof.
  intros Hp. split; unfold peers_refs_ok; eapply Forall_impl; try exact Hp; intros [[a sh] P] HP;
    destruct HP as (_ & _ & _ & _ & _ & Hr & Hl & _); [| exact Hr].
  rewrite Int64.signed_eq_unsigned; [rep_lia |].
  unfold Int64.max_signed, Int64.half_modulus, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in *.
  cbn in *. lia.
Qed.
Lemma hci5_p6_hd_pn PS KE T : itable_wf T -> hci5_T_ok PS KE T ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> Forall (fun e => isptr (ke_addr e)) KE ->
  is_pointer_or_null (hd nullval (t_L T)).
Proof.
  intros (_ & Hinc & _) (HT1 & _) Hp Hk. destruct (t_L T) as [| v l] eqn:E; cbn; [reflexivity|].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  rewrite HT1 in Hv. apply in_app_or in Hv. rewrite Forall_forall in Hp, Hk. destruct Hv as [Hv | Hv].
  - apply in_map_iff in Hv. destruct Hv as (e & <- & He). specialize (Hk _ He).
    destruct (ke_addr e); try contradiction; exact I.
  - apply in_map_iff in Hv. destruct Hv as (x & <- & Hx). specialize (Hp _ Hx). unfold hs_addr.
    destruct (peer_addr4 x); try contradiction; exact I.
Qed.
End hci5_p6_pure.

Section P6.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_P6_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S5 x25519 gv L FR) hci5_P6
    (overridePost (hci5_S6 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_S5, hci5_Delta, hci5_R, hci5_P6. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
  forward_call tt. Intros now.
  pose proof H0 as Hinv. destruct Hinv as (Hpok & Hwf & Hch & Hnp & Hna & HT & Hsl).
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS) as Hptr by (sep_apply (hci5_p6_ptrs PS); entailer!).
  match goal with |- semax _ (PROPx ?Pp (LOCALx (temp _ (Vlong now) :: ?Qq) (SEPx ?Rr))) _ _ =>
    apply semax_seq with (Q := EX n: int64, PROPx ((0 <= Int64.unsigned n < 2 ^ 62) :: Pp)
                                 (LOCALx (temp HC._now (Vlong n) :: Qq) (SEPx Rr))) end.
  { destruct Hna as [Hna | Hna].
    - subst na.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HC._t'18 (Vint Int.zero) :: Q) (SEPx R))) end.
      + discriminate.
      + forward. entailer!.
      + forward_if.
        * contradiction.
        * forward. Exists now. entailer!.
    - apply in_map_iff in Hna. destruct Hna as (N & <- & HN).
      assert (Hp: In (hn_p N) (map peer_addr4 PS)) by (rewrite <- Hnp; apply in_map, HN).
      apply in_map_iff in Hp. destruct Hp as ([[a sh] P] & Ha & HinP). cbn in Ha. subst a.
      assert (Hsh: sh = Ews) by (rewrite Forall_forall in Hpok; destruct (Hpok _ HinP) as (? & _); auto). subst sh.
      assert (Hpp: isptr (hn_p N)) by (rewrite Forall_forall in Hptr; exact (Hptr _ HinP)).
      pose proof (hci5_p6_node_acc (hci5_head NS) NS N HN) as A1. unfold hci5_p6_acc in A1. sep_apply A1. clear A1.
      pose proof (hci5_p6_peers_lic PS (hn_p N) Ews P HinP) as A1. unfold hci5_p6_acc in A1. sep_apply A1. clear A1. Intros.
      match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
        forward_if (EX b: bool, PROPx Pp (LOCALx (temp HC._t'18 (Val.of_bool b) :: Qq) (SEPx Rr))) end.
      { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
        apply derives_trans with (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) * TT)%logic; [cancel|].
        apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; vm_compute; reflexivity. }
      + forward_call tt. Intros k. forward.
        { entailer!. match goal with X: _ /\ Int.repr 4 = Int.mone |- _ => destruct X as [_ X];
            apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end. }
        Exists (Int.eq (Int.mods (Int.repr k) (Int.repr 4)) (Int.repr 0)). entailer!.
        destruct (Int.eq _ _); reflexivity.
      + forward. Exists false. entailer!.
      + Intros b. forward_if.
        * forward_call tt. Intros k. forward. forward. forward.
          { entailer!. match goal with X: _ /\ Int.repr 5 = Int.mone |- _ => destruct X as [_ X];
              apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end. }
          forward_if.
          -- forward.
             sep_apply (hci5_p6_mp (@field_at W Ews t_peer [StructField HC._last_initiation_consumption; StructField HC._handshake]
                 (Vlong (hs_lic (p_hs P))) (hn_p N)) (peers_rep PS)).
             sep_apply (hci5_p6_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
             match goal with |- context [temp HC._now (Vlong ?e)] => Exists e end. entailer!.
             match goal with X: Int64.unsigned _ < Int64.unsigned (Int64.shl _ _) |- _ =>
               split; [apply Int64.unsigned_range | eapply Z.lt_le_trans; [exact X | vm_compute; discriminate]] end.
          -- forward.
             sep_apply (hci5_p6_mp (@field_at W Ews t_peer [StructField HC._last_initiation_consumption; StructField HC._handshake]
                 (Vlong (hs_lic (p_hs P))) (hn_p N)) (peers_rep PS)).
             sep_apply (hci5_p6_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
             Exists now. entailer!.
        * forward.
          sep_apply (hci5_p6_mp (@field_at W Ews t_peer [StructField HC._last_initiation_consumption; StructField HC._handshake]
              (Vlong (hs_lic (p_hs P))) (hn_p N)) (peers_rep PS)).
          sep_apply (hci5_p6_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
          Exists now. entailer!. }
  Intros n. unfold MORE_COMMANDS, abbreviate. abbreviate_semax. rename H3 into Hn.
  unfold shim_state4. rewrite (hci5_p6_core_open gv S). Intros. rename H3 into HSok.
  forward.
  sep_apply (hci5_p6_shim_fold gv S n w HSok).
  assert_PROP (is_pointer_or_null (hci5_head NS)) as Hpn by (sep_apply (hci5_p6_pn (hci5_head NS) NS); entailer!).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) KE) as Hkp by (sep_apply (hci5_p6_kptrs (hci5_khead KE) KE); entailer!).
  assert_PROP (isptr (l_wb L) /\ isptr (l_ptb L) /\ isptr (l_itb L)) as Hlv by entailer!.
  destruct Hlv as (Hwb & Hpt & Hit).
  forward.
  forward_call (hci5_head NS, NS, PS, Tsh, l_itb L, T).
  { apply (hci5_p6_snap_pre x25519 R L PS KE T Hpok HT Hsl Hptr Hkp Hwb). }
  forward_call (hci5_khead KE, KE, Tsh, l_itb L, T).
  { apply (hci5_p6_ksnap_pre PS KE T HT Hptr). }
  change (ptable Tsh (l_ptb L) head) with (ptable Tsh (d_ptab (hci5_DB x25519 R L)) head).
  forward_call (Tsh, l_ds L, Tsh, l_wb L, hci5_DB x25519 R L, Tsh, head).
  { pose proof (hci5_p6_head head PS Hch Hptr).
    unfold hci5_DB, setup_dev; cbn.
    repeat constructor; try discriminate; auto; intro X; rewrite X in *; contradiction. }
  rewrite hci5_p6_itable_open. Intros.
  pose proof (hci5_p6_hd_pn PS KE T H3 HT Hptr Hkp) as Hhd.
  forward.
  sep_apply (hci5_p6_itable_fold Tsh (l_itb L) T H3).
  forward_call (gv, Tsh, l_ss L, shim_set_boot S n, w).
  destruct (hci5_p6_cons_pre x25519 R L PS Hpok) as [Hlic Hrefs].
  forward_call (gv, shim_set_boot S n, w, Int64.zero, Ews, m, M, Tsh, l_wb L, hci5_DB x25519 R L, Tsh, head, PS).
  forward.
  unfold hci5_S6. Exists R (shim_set_boot S n) w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs; cbn [app s_boot shim_set_boot].
  change (d_ptab (hci5_DB x25519 R L)) with (l_ptb L).
  entailer!.
Qed.

End P6.
