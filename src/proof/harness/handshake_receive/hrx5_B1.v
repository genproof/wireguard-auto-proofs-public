(* law handshake_receive: main's phase B1 = the loop body's statements 0..11: the per-packet temps, the clock and its three edges, wg_shim_boottime_ns.
   From hrx5_SC to hrx5_S1 (hrx5_defs.v; the cut: hrx5_cut.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

#[local] Instance hrx5_B1_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_B1_cceK : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

Section hrx5_B1_helpers.
Local Open Scope logic.
(* ---- accessors: P |-- Q * (Q -* P) (port of hci5_P6's) ---- *)
Definition hrx5_B1_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B1_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B1_acc_refl Q : hrx5_B1_acc Q Q.
Proof.
  unfold hrx5_B1_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B1_acc_l Q A F : hrx5_B1_acc Q A -> hrx5_B1_acc Q (A * F).
Proof.
  unfold hrx5_B1_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B1_acc_r Q A F : hrx5_B1_acc Q A -> hrx5_B1_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B1_acc_l, H. Qed.

Lemma hrx5_B1_acc_prop Q (c: Prop) A : (c -> hrx5_B1_acc Q A) -> hrx5_B1_acc Q (!! c && A).
Proof.
  unfold hrx5_B1_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B1_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B1_acc Q (A x)) -> hrx5_B1_acc Q (EX x, A x).
Proof.
  unfold hrx5_B1_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hrx5_B1_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B1_acc Q A) -> hrx5_B1_acc Q A.
Proof.
  unfold hrx5_B1_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B1_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hrx5_B1_acc Q (f x) -> hrx5_B1_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hrx5_B1_acc_l, H | apply hrx5_B1_acc_r, IH, Hin].
Qed.

Lemma hrx5_B1_acc_trans Q B P : hrx5_B1_acc Q B -> hrx5_B1_acc B P -> hrx5_B1_acc Q P.
Proof.
  unfold hrx5_B1_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

(* the node's field p, at the world *)
Lemma hrx5_B1_node_split p sn r rs nx x :
  @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x |--
  @field_at W Ews t_hnode4 [StructField HM._p] p x *
  (@field_at W Ews t_hnode4 [StructField HM._p] p x -* @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HM._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HM._p) _ p x); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

Lemma hrx5_B1_node_acc l NS N : In N NS ->
  hrx5_B1_acc (@field_at W Ews t_hnode4 [StructField HM._p] (hn_p N) (hn_addr N)) (hnodes_rep4 W l NS).
Proof.
  revert l; induction NS as [|N0 NS IH]; intros l Hin; [destruct Hin|]. cbn [hnodes_rep4].
  apply hrx5_B1_acc_prop; intros Hl. apply hrx5_B1_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hrx5_B1_acc_l, hrx5_B1_acc_l, hrx5_B1_acc_r. apply hrx5_B1_node_split.
  - apply hrx5_B1_acc_r, IH, Hin.
Qed.

Section hrx5_B1_N.
#[local] Existing Instance Noise.CS.
Lemma hrx5_B1_acc_lic sh h H :
  hrx5_B1_acc (field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h) (hs_rep sh h H).
Proof.
  unfold hs_rep. apply hrx5_B1_acc_prop; intros _.
  do 13 apply hrx5_B1_acc_l. apply hrx5_B1_acc_r, hrx5_B1_acc_refl.
Qed.
Lemma hrx5_B1_acc_hs sh a Q : hrx5_B1_acc (hs_rep sh (hs_addr a) (p_hs Q)) (peer_rep sh a Q).
Proof.
  unfold peer_rep. apply hrx5_B1_acc_prop; intros _.
  do 7 apply hrx5_B1_acc_l. apply hrx5_B1_acc_r, hrx5_B1_acc_refl.
Qed.
End hrx5_B1_N.

Lemma hrx5_B1_pk_lic sh a Q : hrx5_B1_acc
  (@field_at W sh t_peer [StructField HM._last_initiation_consumption; StructField HM._handshake]
     (Vlong (hs_lic (p_hs Q))) a) (peer_rep sh a Q).
Proof.
  rewrite <- (@field_at_change_composite Noise.CS W _ sh t_peer [StructField HM._last_initiation_consumption; StructField HM._handshake] (Vlong (hs_lic (p_hs Q))) (Vlong (hs_lic (p_hs Q))) (JMeq_refl _))
    by (vm_compute; reflexivity).
  apply hrx5_B1_acc_pure with (c := @field_compatible Noise.CS t_peer [] a); [unfold peer_rep; entailer! | intros FC].
  pose proof (@field_at_app Noise.CS sh t_peer [StructField HM._last_initiation_consumption] [StructField HM._handshake]
     (Vlong (hs_lic (p_hs Q))) (Vlong (hs_lic (p_hs Q))) a (JMeq_refl _)) as E.
  change ([StructField HM._last_initiation_consumption] ++ [StructField HM._handshake]) with
    [StructField HM._last_initiation_consumption; StructField HM._handshake] in E.
  rewrite E; clear E.
  rewrite field_address_offset by auto with field_compatible.
  change (offset_val _ a) with (hs_addr a).
  change (nested_field_type t_peer [StructField HM._handshake]) with t_hs.
  change HM._last_initiation_consumption with I._last_initiation_consumption.
  exact (hrx5_B1_acc_trans _ _ _ (hrx5_B1_acc_lic sh (hs_addr a) (p_hs Q)) (hrx5_B1_acc_hs sh a Q)).
Qed.

Lemma hrx5_B1_peers_lic PS a sh P : In (a, sh, P) PS -> hrx5_B1_acc
  (@field_at W sh t_peer [StructField HM._last_initiation_consumption; StructField HM._handshake]
     (Vlong (hs_lic (p_hs P))) a) (peers_rep PS).
Proof.
  intros Hin. unfold peers_rep. apply (hrx5_B1_acc_iter _ _ (a, sh, P)); [exact Hin|].
  apply hrx5_B1_pk_lic.
Qed.

(* ---- D's cookie secret birthdate (port of hcy5_p5_a_lemmas's) ---- *)
Lemma hrx5_B1_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Section hrx5_B1_D.
#[local] Existing Instance Noise.CS.

Lemma hrx5_B1_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hrx5_B1_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W hrx5_B1_cceN); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hrx5_B1_fc_cc; exact FC).
  rewrite (@field_at_data_at W). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hrx5_B1_tulong_cs.
Qed.

Lemma hrx5_B1_cc_split sh v a :
  data_at sh t_cc v a |--
  field_at sh t_cc (DOT I._secret_birthdate) (proj_reptype t_cc (DOT I._secret_birthdate) v) a *
  (field_at sh t_cc (DOT I._secret_birthdate) (proj_reptype t_cc (DOT I._secret_birthdate) v) a -* data_at sh t_cc v a).
Proof.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (gfield_ramif sh t_cc [] (StructField I._secret_birthdate) v (proj_reptype t_cc (DOT I._secret_birthdate) v) a); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (proj_reptype t_cc (DOT I._secret_birthdate) v)).
  apply derives_refl.
Qed.

Lemma hrx5_B1_acc_cc sh a CC :
  hrx5_B1_acc (field_at sh t_cc (DOT I._secret_birthdate) (Vlong (cc_birth CC)) a) (checker_rep sh a CC).
Proof.
  unfold checker_rep. apply hrx5_B1_acc_prop; intros _. apply hrx5_B1_acc_ex; intros lk.
  apply (hrx5_B1_cc_split sh (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC),
                                  (Vlong (cc_birth CC), (lk, cc_dev CC))))) a).
Qed.
End hrx5_B1_D.

Lemma hrx5_B1_acc_birth sh wg D :
  hrx5_B1_acc (@field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth (d_cc D))) wg)
    (device_rep sh wg D).
Proof.
  unfold device_rep. apply hrx5_B1_acc_prop; intros FC. rewrite (hrx5_B1_cc_birth sh wg _ FC).
  apply hrx5_B1_acc_l, hrx5_B1_acc_l, hrx5_B1_acc_r, hrx5_B1_acc_cc.
Qed.

End hrx5_B1_helpers.

(* ---- arithmetic of the clock ---- *)
Lemma hrx5_B1_mods b : 0 <= b <= Byte.max_unsigned ->
  0 <= Int.unsigned (Int.mods (Int.repr b) (Int.repr 64)) < 64.
Proof.
  intros Hb. unfold Int.mods. rewrite (Int.signed_repr b) by rep_lia.
  change (Int.signed (Int.repr 64)) with 64.
  assert (0 <= Z.rem b 64 < 64) by (apply Z.rem_bound_pos; lia).
  rewrite Int.unsigned_repr by rep_lia. lia.
Qed.

Lemma hrx5_B1_shl62 : Int64.shl (Int64.repr 1) (Int64.repr 62) = Int64.repr (2 ^ 62).
Proof. reflexivity. Qed.

Lemma hrx5_B1_add_lt n x : 0 <= Int64.unsigned n < 2 ^ 62 ->
  Int64.unsigned x < Int64.unsigned (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 62)) n) ->
  0 <= Int64.unsigned (Int64.add n x) < 2 ^ 62.
Proof.
  intros Hn Hx. rewrite hrx5_B1_shl62 in Hx. unfold Int64.sub in Hx.
  rewrite (Int64.unsigned_repr (2 ^ 62)) in Hx by rep_lia.
  rewrite Int64.unsigned_repr in Hx by rep_lia.
  pose proof (Int64.unsigned_range x).
  unfold Int64.add. rewrite Int64.unsigned_repr by rep_lia. lia.
Qed.

Lemma hrx5_B1_ltu62 e : Int64.ltu e (Int64.shl (Int64.repr 1) (Int64.repr 62)) = true ->
  0 <= Int64.unsigned e < 2 ^ 62.
Proof.
  intros He. rewrite hrx5_B1_shl62 in He. unfold Int64.ltu in He.
  rewrite Int64.unsigned_repr in He by rep_lia.
  destruct (zlt _ _); [| discriminate]. pose proof (Int64.unsigned_range e). lia.
Qed.

Lemma hrx5_B1_b2v x y : Val.of_bool (Int64.ltu x y) = bool2val (Int64.cmpu Clt x y).
Proof. unfold Int64.cmpu, bool2val. destruct (Int64.ltu x y); reflexivity. Qed.

(* the shim's boot clock (as hci5_P6's) *)
Lemma hrx5_B1_tulong_W sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W sh tulong v p.
Proof. apply hrx5_B1_tulong_cs. Qed.

Definition hrx5_B1_rest (gv: globals) (S: shim) : mpred :=
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

Lemma hrx5_B1_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W Ews tulong (Vlong (s_boot S)) (gv HM._wg_shim_boottime_ns) *
     hrx5_B1_rest gv S))%logic.
Proof.
  unfold shim_core, hrx5_B1_rest. rewrite <- hrx5_B1_tulong_W. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hrx5_B1_shim_fold gv S n w : shim_ok S ->
  (@data_at W Ews tulong (Vlong n) (gv HM._wg_shim_boottime_ns) * hrx5_B1_rest gv S *
   refwarn4 gv w |-- shim_state4 gv (shim_set_boot S n) w)%logic.
Proof.
  intros HS. unfold shim_state4. rewrite hrx5_B1_core_open. unfold hrx5_B1_rest; cbn.
  entailer!.
Qed.

Lemma hrx5_B1_lt62 e : Int64.unsigned e < Int64.unsigned (Int64.shl (Int64.repr 1) (Int64.repr 62)) ->
  0 <= Int64.unsigned e < 2 ^ 62.
Proof.
  intros He. rewrite hrx5_B1_shl62, Int64.unsigned_repr in He by rep_lia.
  pose proof (Int64.unsigned_range e). lia.
Qed.

(* the normal post after the last forward of a block (its ret_assert destructed) *)
Ltac hrx5_B1_post := try
  match goal with |- _ |-- RA_normal ?X =>
    let Y := eval cbv beta iota in X in
    match Y with Build_ret_assert ?Q _ _ _ => change (RA_normal X) with Q end end.

(* the statements 7 (the clock), 8, 9, 10 (the edges) and 11 (the boot clock) of B1 *)
Definition hrx5_B1_a := ltac:(let x := eval cbv beta iota delta [hrx5_bl firstn skipn hrx5_bstmts] in (firstn 7 (hrx5_bl 0 12)) in exact x).
Definition hrx5_B1_s11 := ltac:(let x := eval cbv beta iota delta [hrx5_bl firstn skipn hrx5_bstmts nth] in (nth 11 (hrx5_bl 0 12) Sskip) in exact x).
Definition hrx5_B1_s7 := ltac:(let x := eval cbv beta iota delta [hrx5_bl firstn skipn hrx5_bstmts nth] in (nth 7 (hrx5_bl 0 12) Sskip) in exact x).
Definition hrx5_B1_s8 := ltac:(let x := eval cbv beta iota delta [hrx5_bl firstn skipn hrx5_bstmts nth] in (nth 8 (hrx5_bl 0 12) Sskip) in exact x).
Definition hrx5_B1_s9 := ltac:(let x := eval cbv beta iota delta [hrx5_bl firstn skipn hrx5_bstmts nth] in (nth 9 (hrx5_bl 0 12) Sskip) in exact x).
Definition hrx5_B1_s10 := ltac:(let x := eval cbv beta iota delta [hrx5_bl firstn skipn hrx5_bstmts nth] in (nth 10 (hrx5_bl 0 12) Sskip) in exact x).

Section B1Q.
Variable x25519: list byte -> list byte -> list byte.

(* inside B1: the temps reset, now = n (the boot clock not yet stored) *)
Definition hrx5_B1_Q (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (n: int64) : environ -> mpred :=
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; 0 <= Int64.unsigned n < 2 ^ 62]
  (LOCALx (hrx5_ltemps nk KE st i (shim_set_boot S n) lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc nullval; temp HM._buf nullval;
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         hrx5_rglobs gv lul ++ [hrx5_skb0 L] ++ hrx5_scr L))).
End B1Q.

Section B1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B1_c7 {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul n Rt :
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n) hrx5_B1_s7
    (overridePost (EX n': int64, hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n') Rt).
Proof.
  destruct Rt. unfold hrx5_B1_Q, hrx5_B1_s7, hrx5_Delta. abbreviate_semax.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot]. Intros.
  forward_call tt. Intros d.
  forward_call tt. Intros b.
  pose proof (hrx5_B1_mods b H4) as Hm.
  forward.
  { entailer!. split; [change (Int.unsigned Int64.iwordsize') with 64; lia |].
    intros [_ X]. apply (f_equal Int.signed) in X. rewrite Int.signed_mone, Int.signed_repr in X by rep_lia. lia. }
  forward_if.
  - forward. hrx5_B1_post. Exists (Int64.add n (Int64.shru d (Int64.repr (Int.unsigned (Int.mods (Int.repr b) (Int.repr 64)))))).
    unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot].
    entailer!. apply hrx5_B1_add_lt; assumption.
  - forward. hrx5_B1_post. Exists n.
    unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot].
    entailer!.
Qed.

Lemma hrx5_B1_c8 {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul n Rt :
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n) hrx5_B1_s8
    (overridePost (EX n': int64, hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n') Rt).
Proof.
  destruct Rt. unfold hrx5_B1_Q, hrx5_B1_s8, hrx5_Delta. abbreviate_semax.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot]. Intros.
  pose proof H0 as Hinv. destruct Hinv as (Hpok & Hwf & Hnd & Hch & Hnp & Hnk & Hpool).
  destruct Hnk as [Hnk | Hnk].
  - subst nk.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'12 (Vint Int.zero) :: Q) (SEPx R))) end.
    + discriminate.
    + forward. entailer!.
    + forward_if.
      * contradiction.
      * forward. hrx5_B1_post. Exists n.
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot].
        entailer!.
  - apply in_map_iff in Hnk. destruct Hnk as (N & <- & HN).
    assert (Hp: In (hn_p N) (map peer_addr4 PS)) by (rewrite <- Hnp; apply in_map, HN).
    apply in_map_iff in Hp. destruct Hp as ([[a sh] P] & Ha & HinP). cbn in Ha. subst a.
    assert (HP := proj1 (Forall_forall _ _) Hpok _ HinP). cbn in HP.
    destruct HP as (Hsh & _ & _ & _ & _ & _ & Hlic & _). subst sh.
    pose proof (hrx5_B1_node_acc (hrx5_head NS) NS N HN) as A1. unfold hrx5_B1_acc in A1. sep_apply A1. clear A1.
    pose proof (hrx5_B1_peers_lic PS (hn_p N) Ews P HinP) as A1. unfold hrx5_B1_acc in A1. sep_apply A1. clear A1. Intros.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (EX b: bool, PROPx Pp (LOCALx (temp HRM._t'12 (Val.of_bool b) :: Qq) (SEPx Rr))) end.
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      apply derives_trans with (@field_at W Ews t_hnode4 (DOT HM._p) (hn_p N) (hn_addr N) * TT)%logic; [cancel|].
      apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; vm_compute; reflexivity. }
    + forward_call tt. Intros k. forward.
      { entailer!. match goal with X: _ /\ Int.repr 8 = Int.mone |- _ => destruct X as [_ X];
          apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end. }
      Exists (Int.eq (Int.mods (Int.repr k) (Int.repr 8)) (Int.repr 0)). entailer!.
      destruct (Int.eq _ _); reflexivity.
    + forward. Exists false. entailer!.
    + Intros b. forward_if.
      * forward_call tt. Intros k. forward. forward. forward.
        { entailer!. match goal with X: _ /\ Int.repr 5 = Int.mone |- _ => destruct X as [_ X];
            apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end. }
        match goal with |- context [temp HRM._edge (Vlong ?x)] => set (e := x) end.
        match goal with |- semax _ (PROPx ?Pp (LOCALx (temp _ (Vlong e) :: ?Qq) (SEPx ?Rr))) _ _ =>
          forward_if (EX bb: bool, PROPx ((bb = true -> 0 <= Int64.unsigned e < 2^62) :: Pp)
            (LOCALx (temp HRM._t'11 (Val.of_bool bb) :: temp HRM._edge (Vlong e) :: Qq) (SEPx Rr))) end.
        -- forward. Exists (Int64.ltu e (Int64.shl (Int64.repr 1) (Int64.repr 62))). entailer!.
           split; [apply hrx5_B1_ltu62 | apply hrx5_B1_b2v].
        -- forward. Exists false. entailer!.
        -- Intros bb. forward_if.
           ++ forward. hrx5_B1_post.
              sep_apply (hrx5_B1_mp (@field_at W Ews t_peer [StructField HM._last_initiation_consumption; StructField HM._handshake]
                 (Vlong (hs_lic (p_hs P))) (hn_p N)) (peers_rep PS)).
              sep_apply (hrx5_B1_mp (@field_at W Ews t_hnode4 (DOT HM._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hrx5_head NS) NS)).
              Exists e.
              unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot].
              entailer!. destruct bb; [auto | discriminate].
           ++ forward. hrx5_B1_post.
              sep_apply (hrx5_B1_mp (@field_at W Ews t_peer [StructField HM._last_initiation_consumption; StructField HM._handshake]
                 (Vlong (hs_lic (p_hs P))) (hn_p N)) (peers_rep PS)).
              sep_apply (hrx5_B1_mp (@field_at W Ews t_hnode4 (DOT HM._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hrx5_head NS) NS)).
              Exists n.
              unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot].
              entailer!.
      * forward. hrx5_B1_post.
        sep_apply (hrx5_B1_mp (@field_at W Ews t_peer [StructField HM._last_initiation_consumption; StructField HM._handshake]
           (Vlong (hs_lic (p_hs P))) (hn_p N)) (peers_rep PS)).
        sep_apply (hrx5_B1_mp (@field_at W Ews t_hnode4 (DOT HM._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hrx5_head NS) NS)).
        Exists n.
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app s_boot shim_set_boot].
        entailer!.
Qed.

Ltac hrx5_B1_tc := entailer!; try match goal with X: _ /\ Int.repr ?m = Int.mone |- _ => destruct X as [_ X];
  apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end.

Ltac hrx5_B1_unf := unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr;
  cbn [app s_boot shim_set_boot].

Lemma hrx5_B1_c9 {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul n Rt :
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n) hrx5_B1_s9
    (overridePost (EX n': int64, hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n') Rt).
Proof.
  destruct Rt. unfold hrx5_B1_Q, hrx5_B1_s9, hrx5_Delta. abbreviate_semax.
  hrx5_B1_unf. Intros.
  forward_call tt. Intros k0.
  forward_if.
  { hrx5_B1_tc. }
  - forward_call tt. Intros k.
    pose proof (hrx5_B1_acc_birth Tsh (l_wd L) (hrx5_DL x25519 R L sec birth)) as A1.
    unfold hrx5_B1_acc in A1. sep_apply A1. clear A1.
    change (cc_birth (d_cc (hrx5_DL x25519 R L sec birth))) with birth.
    Intros.
    forward. forward.
    { hrx5_B1_tc. }
    match goal with |- context [temp HRM._edge__1 (Vlong ?x)] => set (e := x) end.
    match goal with |- semax _ (PROPx ?Pp (LOCALx (temp _ (Vlong e) :: ?Qq) (SEPx ?Rr))) _ _ =>
      forward_if (EX bb: bool, PROPx ((bb = true -> 0 <= Int64.unsigned e < 2^62) :: Pp)
        (LOCALx (temp HRM._t'15 (Val.of_bool bb) :: temp HRM._edge__1 (Vlong e) :: Qq) (SEPx Rr))) end.
    + forward. Exists (Int64.ltu e (Int64.shl (Int64.repr 1) (Int64.repr 62))). entailer!.
      split; [apply hrx5_B1_ltu62 | apply hrx5_B1_b2v].
    + forward. Exists false. entailer!.
    + Intros bb. forward_if.
      * forward. hrx5_B1_post.
        sep_apply (hrx5_B1_mp (@field_at W Tsh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong birth) (l_wd L))
          (device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth))).
        Exists e. hrx5_B1_unf. entailer!. destruct bb; [auto | discriminate].
      * forward. hrx5_B1_post.
        sep_apply (hrx5_B1_mp (@field_at W Tsh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong birth) (l_wd L))
          (device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth))).
        Exists n. hrx5_B1_unf. entailer!.
  - forward. hrx5_B1_post. Exists n. hrx5_B1_unf. entailer!.
Qed.

Lemma hrx5_B1_c10 {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul n Rt :
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n) hrx5_B1_s10
    (overridePost (EX n': int64, hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n') Rt).
Proof.
  destruct Rt. unfold hrx5_B1_Q, hrx5_B1_s10, hrx5_Delta. abbreviate_semax.
  hrx5_B1_unf. Intros.
  match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
    forward_if (EX b: bool, PROPx Pp (LOCALx (temp HRM._t'19 (Val.of_bool b) :: Qq) (SEPx Rr))) end.
  - forward_call tt. Intros k. forward.
    { hrx5_B1_tc. }
    Exists (Int.eq (Int.mods (Int.repr k) (Int.repr 8)) (Int.repr 0)). entailer!.
    destruct (Int.eq _ _); reflexivity.
  - forward. Exists false. entailer!.
  - Intros b. forward_if.
    + forward_call tt. Intros k. forward.
      { hrx5_B1_tc. }
      match goal with |- context [temp HRM._edge__2 (Vlong ?x)] => set (e := x) end.
      match goal with |- semax _ (PROPx ?Pp (LOCALx (temp _ (Vlong e) :: ?Qq) (SEPx ?Rr))) _ _ =>
        forward_if (EX bb: bool, PROPx ((bb = true -> 0 <= Int64.unsigned e < 2^62) :: Pp)
          (LOCALx (temp HRM._t'18 (Val.of_bool bb) :: temp HRM._edge__2 (Vlong e) :: Qq) (SEPx Rr))) end.
      * forward. Exists (Int64.ltu e (Int64.shl (Int64.repr 1) (Int64.repr 62))). entailer!.
        split; [apply hrx5_B1_ltu62 | apply hrx5_B1_b2v].
      * forward. Exists false. entailer!.
      * Intros bb. forward_if.
        -- forward. hrx5_B1_post. Exists e. hrx5_B1_unf. entailer!. destruct bb; [auto | discriminate].
        -- forward. hrx5_B1_post. Exists n. hrx5_B1_unf. entailer!.
    + forward. hrx5_B1_post. Exists n. hrx5_B1_unf. entailer!.
Qed.

Lemma hrx5_B1_c11 {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul n Rt :
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul n) hrx5_B1_s11
    (overridePost (hrx5_S1 x25519 gv L FR) Rt).
Proof.
  destruct Rt. unfold hrx5_B1_Q, hrx5_B1_s11, hrx5_Delta. abbreviate_semax.
  hrx5_B1_unf. Intros.
  unfold shim_state4. rewrite (hrx5_B1_core_open gv S). Intros. rename H4 into HSok.
  forward. hrx5_B1_post.
  sep_apply (hrx5_B1_shim_fold gv S n w HSok).
  unfold hrx5_S1.
  Exists R sec birth (shim_set_boot S n) w NS PS T. Exists head nk KE st i kc lul.
  hrx5_B1_unf. entailer!.
  unfold hrx5_base_ok in *; cbn [s_boot shim_set_boot]; tauto.
Qed.

Lemma hrx5_B1_c0 {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul Rt :
  hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= st <= Int64.max_unsigned ->
  0 <= i <= st -> i < st ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (PROPx [] (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_lvars gv L)
      (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
             hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
             hrx5_rglobs gv lul ++ [hrx5_skb0 L] ++ hrx5_scr L))))
    (hrx5_seql hrx5_B1_a)
    (overridePost (hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul (s_boot S)) Rt).
Proof.
  intros Hb Hi Hst Hi1 Hi2.
  destruct Rt. unfold hrx5_B1_a, hrx5_seql, hrx5_Delta. abbreviate_semax.
  hrx5_B1_unf.
  forward. forward. forward. forward. forward. forward. forward. hrx5_B1_post.
  unfold hrx5_B1_Q. hrx5_B1_unf. entailer!.
  destruct Hb as (_ & _ & _ & Hs). exact Hs.
Qed.

Lemma hrx5_B1_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SC x25519 gv L FR) hrx5_B1
    (overridePost (hrx5_S1 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH. unfold hrx5_SC, hrx5_SLc. Intros R sec birth S w NS PS T. Intros head nk KE st i kc lul.
  change hrx5_B1 with (hrx5_seql (hrx5_B1_a ++ [hrx5_B1_s7; hrx5_B1_s8; hrx5_B1_s9; hrx5_B1_s10; hrx5_B1_s11])).
  eapply hrx5_seql_app with (Q := hrx5_B1_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul (s_boot S));
    [discriminate | discriminate | apply hrx5_B1_c0; auto |].
  cbn [hrx5_seql].
  eapply semax_seq; [apply hrx5_B1_c7 |]. Intros n1.
  eapply semax_seq; [apply hrx5_B1_c8 |]. Intros n2.
  eapply semax_seq; [apply hrx5_B1_c9 |]. Intros n3.
  eapply semax_seq; [apply hrx5_B1_c10 |]. Intros n4.
  apply hrx5_B1_c11.
Qed.

End B1.
