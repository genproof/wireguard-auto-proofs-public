(* law handshake_receive, phase B8 branch C: the fold QC |-- hrx5_S8 (the new world: a's peer with the new cookie, nodes / kents snapped).
*)
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

Lemma hrx5_B8CF_sfind_in (l: list (val * share * peer)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x shx] y] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|Hne]; [inv H; left; reflexivity | right; auto].
Qed.

Lemma hrx5_B8CF_snapped_p T NS PS :
  length NS = length PS -> map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8CF_snapped_a T NS PS :
  length NS = length PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8CF_kaddr T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. apply map_ext. intros e. reflexivity. Qed.

Lemma hrx5_B8CF_khead T KE : hrx5_khead (map (kent_snapped T) KE) = hrx5_khead KE.
Proof. destruct KE; reflexivity. Qed.

Lemma hrx5_B8CF_inv_nodes x25519 R L NS PS KE T head nk NS' KE' :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  map hn_p NS' = map hn_p NS -> map hn_addr NS' = map hn_addr NS -> map ke_addr KE' = map ke_addr KE ->
  hrx5_inv x25519 R L NS' PS KE' T head nk.
Proof.
  intros (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool) Hp Ha Hk.
  unfold hrx5_inv. split; [exact HF|]. split; [exact Hwf|]. split; [exact HND|]. split; [exact Hch|].
  split; [unfold hnodes_peers4 in *; rewrite Hp; exact Hnp|].
  split; [rewrite Ha; exact Hnk|]. rewrite Hk. exact Hpool.
Qed.

Lemma hrx5_B8CF_inv x25519 R L NS PS KE T head nk a P pt now :
  hrx5_inv x25519 R L NS PS KE T head nk -> sfind PS a = Some (Ews, P) ->
  hrx5_inv x25519 R L (hnodes_snapped4 T NS PS) (supd PS a (hrx5ck_new P pt now)) (map (kent_snapped T) KE)
    T head nk.
Proof.
  intros HI Hf.
  assert (Hlen: length NS = length PS).
  { destruct HI as (_ & _ & _ & _ & Hnp & _). unfold hnodes_peers4 in Hnp.
    rewrite <- (map_length hn_p NS), Hnp, map_length. reflexivity. }
  assert (HI2: hrx5_inv x25519 R L NS (supd PS a (hrx5ck_new P pt now)) KE T head nk).
  { eapply (proj1 (hrx5_B8i_lem x25519)); [exact HI | exact Hf | | reflexivity].
    destruct HI as (HF & _). rewrite Forall_forall in HF.
    pose proof (HF _ (hrx5_B8CF_sfind_in _ _ _ _ Hf)) as Hok. exact Hok. }
  eapply hrx5_B8CF_inv_nodes; [exact HI2 | | | apply hrx5_B8CF_kaddr].
  - apply hrx5_B8CF_snapped_p; exact Hlen.
  - apply hrx5_B8CF_snapped_a; exact Hlen.
Qed.

Lemma hrx5_B8CF_rxlog gv : rxlog_rep gv rx0 |-- @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx).
Proof. unfold rxlog_rep. apply data_at_data_at_. Qed.

Lemma hrx5_B8CF_qlen gv q : qlen_rep gv q |-- @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len).
Proof. unfold qlen_rep. apply data_at_data_at_. Qed.

Lemma hrx5_B8CF_pt (pt: list byte) p : Zlength pt = 16 -> hbytes Tsh pt p |-- hout Tsh 16 p.
Proof. intros H. unfold hbytes, hout. rewrite H. apply data_at_data_at_. Qed.

Lemma hrx5_B8C_fold_ok : hrx5_B8C_fold_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port M dp img a P pt HY.
  unfold hrx5_B8C_QC, hrx5_B8C_props.
  Intros.
  unfold hrx5_S8.
  Exists R sec birth S w (hnodes_snapped4 T NS PS) (supd PS a (hrx5ck_new P pt (s_boot S))) T.
  Exists head nk (map (kent_snapped T) KE) st i kc lul q.
  Exists proto ip4 ip6 port (OCookie M) dp img.
  unfold hrx5_ltemps. rewrite hrx5_B8CF_khead.
  pose proof (hrx5_B8CF_inv x25519 R L NS PS KE T head nk a P pt (s_boot S) H0 H8) as HI.
  change (obj_bytes (OCookie M)) with (cookie_msg_bytes M).
  assert (HO: obj_ok (OCookie M)) by (exact H3).
  unfold hrx5_B8C_temps, hrx5_lvars, hrx5_B8C_sep, hrx5_B8C_world, hrx5_B8C_scr, hrx5_wcore, hrx5_globs,
    hrx5_rglobs, hrx5_scr, hrx5_cglobs, obj_rep. cbn [app].
  entailer!.
  unfold hrx5_rest. cbn [app fold_right_sepcon].
  sep_apply (hrx5_B8CF_rxlog gv). sep_apply (hrx5_B8CF_qlen gv q). sep_apply (hrx5_B8CF_pt pt (l_pt L) H9).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hrx5_DL x25519 R L sec birth) head) (l_ds L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_skbsnap (skbsnap_val (hrx5_skb dp (OCookie M) proto ip4 ip6 port)) (l_sks L)).
  cancel.
Qed.
