(* v2, law handshake_receive, B8 R B part K: pure facts and accessors for KP / K1 / K2 (the keypair, its pool entry, the peer's slots, the device's index table). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---- pure ---- *)

Lemma hrx5_B8RBK_itab x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d :
  d_itab (rw_D (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
    o dp d)) = l_itd L.
Proof.
  unfold hrx5_B8R_W1, rx_model, rx_packet, hrx5_W0. cbv zeta. cbn [rw_D].
  destruct (hrx5_fwd _); [|reflexivity].
  destruct (Int.eq _ (Int.repr 3)); [reflexivity|].
  destruct (rx_consumes _ _).
  - destruct (Int.eq _ Int.one).
    + destruct (cin_res _ _ _ _ _ _) as [[? ?]|]; reflexivity.
    + destruct (cre_res _ _ _ _ _ _) as [[? ?]|]; reflexivity.
  - destruct (rx_needs_cookie _ _); reflexivity.
Qed.

Lemma hrx5_B8RBK_sfind_In {A: Type} (D: list (val * share * A)) x sh v : sfind D x = Some (sh, v) -> In (x, sh, v) D.
Proof.
  induction D as [|[[y shy] u] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val y x) as [->|Hne]; [inv H; left; reflexivity | right; apply IH, H].
Qed.

Lemma hrx5_B8RBK_sfind_Znth (l: list (val * share * peer)) : forall j a sh v,
  NoDup (map peer_addr4 l) -> 0 <= j < Zlength l -> Znth j l = (a, sh, v) -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[y shy] u] l IH]; intros j a sh v ND Hj Hz; [rewrite Zlength_nil in Hj; lia|].
  simpl in ND. inv ND. simpl.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite Znth_0_cons in Hz. inv Hz. destruct (EqDec_val a a); [reflexivity | congruence].
  - rewrite Znth_pos_cons in Hz by lia. rewrite Zlength_cons in Hj.
    assert (Hin: In (a, sh, v) l) by (rewrite <- Hz; apply Znth_In; lia).
    destruct (EqDec_val y a) as [->|Hne].
    + exfalso. apply H1. change a with (peer_addr4 (a, sh, v)). apply in_map, Hin.
    + apply (IH (j - 1)); auto; lia.
Qed.

Lemma hrx5_B8RBK_snapped_len T NS PS : Zlength NS = Zlength PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength NS.
Proof.
  intros H. unfold hnodes_snapped4. rewrite Zlength_map.
  revert PS H. induction NS as [|N NS IH]; intros [|x PS] H; simpl combine; rewrite ?Zlength_cons, ?Zlength_nil in *;
    auto; pose proof (Zlength_nonneg NS).
  all: first [lia | rewrite IH; lia].
Qed.

Lemma hrx5_B8RBK_cur d P M ck h : hrx5_B8R_sess d P = true -> p_cur (hrx5_B8RB_Pz d P M ck h) = rd_k d.
Proof. intros Hs. unfold hrx5_B8RB_Pz. cbv zeta. rewrite Hs. reflexivity. Qed.

(* ---- the peer's slots, at W ---- *)
Lemma hrx5_B8RBK_kps_eq sh a (v: @reptype Noise.CS t_kps) : @field_compatible Noise.CS t_peer [] a ->
  @data_at Noise.CS sh t_kps v (kps_addr a) = @field_at W sh t_peer [StructField I._keypairs] v a.
Proof.
  intros FC. rewrite <- (hrx5_B8RBK_fW sh t_peer [StructField I._keypairs] v v a (JMeq_refl _)) by (vm_compute; reflexivity).
  rewrite (@field_at_data_at Noise.CS sh t_peer [StructField I._keypairs]), field_address_offset by auto with field_compatible.
  reflexivity.
Qed.

Lemma hrx5_B8RBK_pk_kps sh a Q : peer_rep sh a Q |--
  EX lk: val, @field_at W sh t_peer [StructField I._keypairs] (p_cur Q, (p_prev Q, (p_next Q, lk))) a *
   (@field_at W sh t_peer [StructField I._keypairs] (p_cur Q, (p_prev Q, (p_next Q, lk))) a -* peer_rep sh a Q).
Proof.
  unfold peer_rep at 1. Intros. unfold kps_rep at 1. Intros lk. Exists lk.
  rewrite (hrx5_B8RBK_kps_eq sh a _ H).
  match goal with |- ?a1 * ?a2 * ?F * ?a4 * ?a5 * ?a6 * ?a7 * ?a8 * ?a9 * ?a10 * ?a11 |-- _ =>
    apply derives_trans with (F * (a1 * a2 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11)); [cancel|] end.
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. unfold peer_rep, kps_rep. Exists lk.
  rewrite (hrx5_B8RBK_kps_eq sh a _ H). entailer!.
Qed.

(* ---- a pool entry found by sfind ---- *)
Lemma hrx5_B8RBK_pool tab T x E : sfind (t_D T) x = Some (Ews, E) ->
  hrx5_B8RBK_acc (entry_at Ews x E (succ_in (t_L T) x) (vin x (t_L T))) (itable Tsh tab T).
Proof.
  intros Hf. unfold itable. apply hrx5_B8RBK_acc_prop; intros _. apply hrx5_B8RBK_acc_r.
  apply (hrx5_B8RBK_acc_iter _ _ (x, Ews, E)); [apply hrx5_B8RBK_sfind_In, Hf |].
  apply hrx5_B8RBK_acc_refl.
Qed.

Lemma hrx5_B8RBK_hentry tab T x E : sfind (t_D T) x = Some (Ews, E) -> @field_compatible Noise.CS t_hs [] x ->
  itable Tsh tab T |--
  @field_at W Ews t_hs [StructField I._entry] (entry_val E (succ_in (t_L T) x) (vin x (t_L T))) x *
  (@field_at W Ews t_hs [StructField I._entry] (entry_val E (succ_in (t_L T) x) (vin x (t_L T))) x -*
   itable Tsh tab T).
Proof.
  intros Hf FC. pose proof (hrx5_B8RBK_pool tab T x E Hf) as HA.
  unfold hrx5_B8RBK_acc, entry_at in HA. rewrite hrx5_B8RBK_entry_eq in HA by exact FC. exact HA.
Qed.

Lemma hrx5_B8RBK_kentry_eq sh k (v: @reptype Noise.CS t_entry_s) : @field_compatible Noise.CS t_kp [] k ->
  @data_at Noise.CS sh t_entry_s v k = @field_at W sh t_kp [StructField I._entry] v k.
Proof.
  intros FC. rewrite <- (hrx5_B8RBK_fW sh t_kp [StructField I._entry] v v k (JMeq_refl _)) by (vm_compute; reflexivity).
  rewrite (@field_at_data_at Noise.CS sh t_kp [StructField I._entry]), field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

Lemma hrx5_B8RBK_kentry tab T k E : sfind (t_D T) k = Some (Ews, E) -> @field_compatible Noise.CS t_kp [] k ->
  itable Tsh tab T |--
  @field_at W Ews t_kp [StructField I._entry] (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k *
  (@field_at W Ews t_kp [StructField I._entry] (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k -*
   itable Tsh tab T).
Proof.
  intros Hf FC. pose proof (hrx5_B8RBK_pool tab T k E Hf) as HA.
  unfold hrx5_B8RBK_acc, entry_at in HA. rewrite hrx5_B8RBK_kentry_eq in HA by exact FC. exact HA.
Qed.

(* ---- the keypair's fields, at W ---- *)
Lemma hrx5_B8RBK_kp_fc k K : keypair_rep W k K |-- !! (@field_compatible Noise.CS t_kp [] k).
Proof. unfold keypair_rep. Intros. entailer!. Qed.

Lemma hrx5_B8RBK_kp_init k K : keypair_rep W k K |--
  @field_at W Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
  (@field_at W Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k -* keypair_rep W k K).
Proof.
  rewrite <- (hrx5_B8RBK_fW Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K))
    (Val.of_bool (kp_init K)) k (JMeq_refl _)) by (vm_compute; reflexivity).
  change (hrx5_B8RBK_acc (@field_at Noise.CS Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k)
    (keypair_rep W k K)).
  unfold keypair_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 4 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.

Lemma hrx5_B8RBK_kp_rindex k K : keypair_rep W k K |--
  @field_at W Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
  (@field_at W Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k -* keypair_rep W k K).
Proof.
  rewrite <- (hrx5_B8RBK_fW Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) (Vint (kp_rindex K)) k
    (JMeq_refl _)) by (vm_compute; reflexivity).
  change (hrx5_B8RBK_acc (@field_at Noise.CS Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k)
    (keypair_rep W k K)).
  unfold keypair_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 5 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.

(* ---- the response message at W ---- *)
Lemma hrx5_B8RBK_resp_W sh m M :
  resp_rep sh m M = !! rm_ok M && @data_at W sh t_resp (resp_val M) m.
Proof.
  unfold resp_rep.
  rewrite (@hrx5_B8RBK_cs_eq Noise.CS W _ sh t_resp (resp_val M) (resp_val M) m)
    by (apply JMeq_refl || prove_cs_preserve_type).
  reflexivity.
Qed.
