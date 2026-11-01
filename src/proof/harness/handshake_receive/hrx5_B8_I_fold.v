(* law handshake_receive, phase B8 branch I, segment fold: QI |-- hrx5_S8 (the new world).

   Shared (proved): hrx5_B8_I_sep.v (accessors, port of hci5_p8_A3_sep.v), hrx5_B8_I_pure.v (the model analysis). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_pure.
Require Import WgNoise.proof.blake2s.model.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.
Local Open Scope Z_scope.

Lemma hrx5_B8IF_len_blake2s key m : Zlength (blake2s key 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma hrx5_B8IF_len_hmac k d : Zlength (hmac k d) = 32.
Proof. unfold hmac, HASH. apply hrx5_B8IF_len_blake2s. Qed.

Lemma hrx5_B8IF_len2 aead_enc aead_dec SS CK H ENCT t ck h : aead_props aead_enc aead_dec ->
  Zlength ENCT = 28 -> m_consume_init2_model aead_dec SS CK H ENCT = Some (t, ck, h) ->
  Zlength t = 12 /\ Zlength ck = 32 /\ Zlength h = 32.
Proof.
  intros HA HL H0.
  unfold m_consume_init2_model, consume_init_stage2 in H0.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) eqn:E; inv H0.
  apply (aead_dec_length _ _ HA) in E. cbn [im_enct] in E.
  unfold kdf1, mix_hash, HASH. rewrite hrx5_B8IF_len_hmac, hrx5_B8IF_len_blake2s. lia.
Qed.

Lemma hrx5_B8IF_tgt_len x25519 aead_enc aead_dec IB PS M now a P t ck2 h2 : aead_props aead_enc aead_dec ->
  im_ok M -> hrx5ci_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) ->
  Zlength t = 12 /\ Zlength ck2 = 32 /\ Zlength h2 = 32.
Proof.
  intros HA HM. unfold hrx5ci_tgt. destruct (mi_ok IB); [| discriminate].
  destruct (m_consume_init1_model _ _ _ _ _) as [[[[s0 k] ck1] h1]|]; [| discriminate].
  destruct (pk_find PS s0) as [[a0 P0]|]; [| discriminate].
  destruct (m_consume_init2_model _ _ _ _ _) as [[[t0 c0] h0]|] eqn:E2; [| discriminate].
  destruct (_ && _)%bool; [| discriminate]. intros H; inversion H; subst.
  exact (hrx5_B8IF_len2 aead_enc aead_dec _ _ _ _ _ _ _ HA (proj1 (proj2 (proj2 HM))) E2).
Qed.

Lemma hrx5_B8IF_pok x25519 R L a P M now t ck2 h2 :
  hrx5_pok x25519 R L (a, Ews, P) -> im_ok M -> 0 <= Int64.unsigned now < 2 ^ 62 ->
  Zlength t = 12 -> Zlength ck2 = 32 -> Zlength h2 = 32 ->
  hrx5_pok x25519 R L (a, Ews, hrx5_B8I_put P M now t ck2 h2).
Proof.
  intros (_ & Hd & Hsid & Hok & Hss & Hrefs & Hlic & Hpk & Hc & Hp & Hn) HM Hnow Lt Lck Lh.
  unfold hrx5_B8I_put, hrx5ci_new, p_set_refs, p_set_hs. cbn [hs_sid hs_ss hs_rstatic hs_lic p_device p_refs
    p_pknext p_cur p_prev p_next p_hs hrx5_pok].
  split; [reflexivity|]. split; [exact Hd|]. split; [exact Hsid|].
  split; [| split; [exact Hss|]; split; [exact Hrefs|]; split;
           [unfold last_consumption; destruct (Int64.lt _ _); assumption|]; auto].
  destruct Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  unfold hs_ok; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
  destruct HM as (HM1 & _). auto 10.
Qed.

Lemma hrx5_B8IF_sfind_in (l: list (val * share * peer)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x shx] y] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|Hne]; [inv H; left; reflexivity | right; auto].
Qed.

Lemma hrx5_B8IF_sfind (l: list (val * share * peer)) a sh v :
  NoDup (map peer_addr4 l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x shx] y] l IH]; simpl; intros Hnd Hin; [contradiction|].
  inv Hnd. destruct (EqDec_val x a) as [->|Hne].
  - destruct Hin as [Heq|Hin]; [inv Heq; reflexivity|].
    exfalso. apply H1. apply (in_map peer_addr4) in Hin. exact Hin.
  - destruct Hin as [Heq|Hin]; [inv Heq; congruence | auto].
Qed.

Lemma hrx5_B8IF_snapped_p T NS PS :
  length NS = length PS -> map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8IF_snapped_a T NS PS :
  length NS = length PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8IF_kaddr T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. apply map_ext. intros e. reflexivity. Qed.

Lemma hrx5_B8IF_khead T KE : hrx5_khead (map (kent_snapped T) KE) = hrx5_khead KE.
Proof. destruct KE; reflexivity. Qed.

Lemma hrx5_B8IF_inv_nodes x25519 R L NS PS KE T head nk NS' KE' :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  map hn_p NS' = map hn_p NS -> map hn_addr NS' = map hn_addr NS -> map ke_addr KE' = map ke_addr KE ->
  hrx5_inv x25519 R L NS' PS KE' T head nk.
Proof.
  intros (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool) Hp Ha Hk.
  unfold hrx5_inv. split; [exact HF|]. split; [exact Hwf|]. split; [exact HND|]. split; [exact Hch|].
  split; [unfold hnodes_peers4 in *; rewrite Hp; exact Hnp|].
  split; [rewrite Ha; exact Hnk|]. rewrite Hk. exact Hpool.
Qed.

Lemma hrx5_B8IF_inv x25519 aead_enc aead_dec R L NS PS KE T head nk IB M now a P t ck2 h2 :
  aead_props aead_enc aead_dec -> im_ok M -> 0 <= Int64.unsigned now < 2 ^ 62 ->
  hrx5_inv x25519 R L NS PS KE T head nk ->
  hrx5ci_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) ->
  hrx5_inv x25519 R L (hnodes_snapped4 T NS PS) (supd PS a (hrx5_B8I_put P M now t ck2 h2))
    (map (kent_snapped T) KE) T head nk.
Proof.
  intros HA HM Hnow HI Ht.
  destruct (hrx5_B8IF_tgt_len x25519 aead_enc aead_dec _ _ _ _ _ _ _ _ _ HA HM Ht) as (Lt & Lck & Lh).
  destruct (hrx5_B8I_tgt_in x25519 aead_dec _ _ _ _ _ _ _ _ _ Ht) as [sh Hin].
  assert (Hok: hrx5_pok x25519 R L (a, sh, P)).
  { destruct HI as (HF & _). exact (proj1 (Forall_forall _ _) HF _ Hin). }
  assert (Hsh: sh = Ews) by (destruct Hok; auto). subst sh.
  assert (Hf: sfind PS a = Some (Ews, P)).
  { apply hrx5_B8IF_sfind; [destruct HI as (_ & _ & HND & _); exact HND | exact Hin]. }
  assert (Hlen: length NS = length PS).
  { destruct HI as (_ & _ & _ & _ & Hnp & _). unfold hnodes_peers4 in Hnp.
    rewrite <- (map_length hn_p NS), Hnp, map_length. reflexivity. }
  assert (HI2: hrx5_inv x25519 R L NS (supd PS a (hrx5_B8I_put P M now t ck2 h2)) KE T head nk).
  { eapply (proj1 (hrx5_B8i_lem x25519)); [exact HI | exact Hf | | reflexivity].
    apply hrx5_B8IF_pok; assumption. }
  eapply hrx5_B8IF_inv_nodes; [exact HI2 | | | apply hrx5_B8IF_kaddr].
  - apply hrx5_B8IF_snapped_p; exact Hlen.
  - apply hrx5_B8IF_snapped_a; exact Hlen.
Qed.

Lemma hrx5_B8IF_rxlog gv X : rxlog_rep gv X |-- @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx).
Proof. unfold rxlog_rep. apply data_at_data_at_. Qed.

Lemma hrx5_B8IF_qlen gv q : qlen_rep gv q |-- @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len).
Proof. unfold qlen_rep. apply data_at_data_at_. Qed.

Lemma hrx5_B8I_fold_ok : hrx5_B8I_fold_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q
    proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1 S1 lul1 HY.
  unfold hrx5_B8I_QI, hrx5_B8I_props.
  Intros.
  match goal with Hb: hrx5_base_ok R sec birth S, HI: hrx5_inv x25519 R L NS PS KE T head nk,
    HM: im_ok M, Ht: hrx5ci_tgt _ _ _ _ _ _ = Some _ |- _ =>
    pose proof (hrx5_B8IF_inv x25519 aead_enc aead_dec R L NS PS KE T head nk _ M (s_boot S) a P t ck2 h2
      (proj1 (proj2 HY)) HM (proj2 (proj2 (proj2 Hb))) HI Ht) as HI2 end.
  match goal with HB: s_boot S1 = s_boot S |- _ => rename HB into HB1 end.
  unfold hrx5_S8.
  Exists R sec1 birth1 S1 w (hnodes_snapped4 T NS PS) (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) T.
  Exists head nk (map (kent_snapped T) KE) st i kc lul1 q.
  Exists proto ip4 ip6 port (OInit M) dp img.
  unfold hrx5_ltemps. rewrite hrx5_B8IF_khead, HB1.
  change (obj_bytes (OInit M)) with (init_bytes M).
  unfold hrx5_B8I_temps, hrx5_lvars, hrx5_B8I_world, hrx5_B8I_scr, hrx5_wcore, hrx5_globs,
    hrx5_rglobs, hrx5_scr, hrx5_cglobs, obj_rep. cbn [app].
  entailer!.
  unfold hrx5_rest. cbn [app fold_right_sepcon].
  sep_apply (hrx5_B8IF_rxlog gv (hrx5_B8I_log a (l_skb L) (sk_len (hrx5_skb dp (OInit M) proto ip4 ip6 port)))).
  sep_apply (hrx5_B8IF_qlen gv q).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hrx5_DL x25519 R L sec1 birth1) head) (l_ds L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_skbsnap (skbsnap_val (hrx5_skb dp (OInit M) proto ip4 ip6 port)) (l_sks L)).
  sep_apply (@data_at_data_at_ HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L)).
  cancel.
Qed.
