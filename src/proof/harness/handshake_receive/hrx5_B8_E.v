(* law handshake_receive: phase B8, branch E
   of statement 41. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_P.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_A.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_B.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the nodes' addresses are not NULL *)
Lemma hrx5_b8e_nodes_nn NS : forall l, hnodes_rep4 W l NS |-- !! (~ In nullval (map hn_addr NS)).
Proof.
  induction NS as [| N NS IH]; intros l; cbn [map In].
  - entailer!.
  - cbn [hnodes_rep4]. Intros nx. sep_apply (IH nx). entailer!.
    match goal with H: _ \/ _ |- _ => destruct H as [Hn | Hn]; [| contradiction] end.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    rewrite Hn in Hp. exact Hp.
Qed.

Lemma hrx5_b8e_snapped_addr T NS PS : length NS = length PS ->
  map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  revert PS; induction NS as [|N NS IH]; intros [|[[p sh] P] PS] Hl; try discriminate; [reflexivity |].
  simpl in Hl. injection Hl as Hl. specialize (IH PS Hl). unfold hnodes_snapped4 in *.
  cbn [combine map] in *. rewrite IH. reflexivity.
Qed.

Lemma hrx5_b8e_peers_len NS PS : hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros H. unfold hnodes_peers4 in H.
  rewrite <- (length_map hn_p NS), H, length_map. reflexivity.
Qed.

Lemma hrx5_B8_E_ok : hrx5_B8_E_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d HY HX.
  apply semax_pre with (P' := !! (~ In nullval (map hn_addr NS)) && hrx5_B8_Q x25519 aead_dec xaead_enc xaead_dec
    gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d).
  { apply andp_right; [| apply andp_left2; apply derives_refl].
    unfold hrx5_B8_Q. cbv zeta.
    unfold hrx5_rest, hrx5_ptrs, hrx5_lvars, hrx5_cglobs, hrx5_scr5; cbn [app].
    match goal with |- context [hnodes_rep4 W ?l ?N] => sep_apply (hrx5_b8e_nodes_nn N l) end.
    Intros. apply prop_right. destruct H0 as (_&_&_&_&Hnp&_).
    rewrite hrx5_b8e_snapped_addr in H7 by (apply hrx5_b8e_peers_len; exact Hnp). exact H7. }
  apply semax_extract_prop. intros Hnn.
  unfold hrx5_B8_Q. cbv zeta.
  apply semax_extract_PROP; intros Hb.
  apply semax_extract_PROP; intros Hinv.
  apply semax_extract_PROP; intros Hst.
  apply semax_extract_PROP; intros Hi.
  apply semax_extract_PROP; intros Ho.
  apply semax_extract_PROP; intros Hmc.
  apply semax_extract_PROP; intros Hacc.
  apply semax_extract_PROP; intros Hd.
  pose proof (hrx5_B8E_P_ok x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE kc lul
    q proto ip4 ip6 port o dp tg ai ar d HY Hb Hinv Ho Hacc Hd Hnn HX) as HPu.
  destruct HPu as (sec1 & birth1 & S1 & lul1 & Hw & Hb1 & Hs1 & Hsh & Hp & Hk).
  rewrite Hw.
  rewrite hrx5_B8E_eq.
  eapply semax_seq; [| apply (hrx5_B8E_B_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w
    NS PS T head nk KE st i kc q proto ip4 ip6 port o dp img tg ai ar sec1 birth1 S1 lul1
    (hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) HY)].
  rewrite overridePost_overridePost.
  eapply semax_pre; [| apply (hrx5_B8E_A_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w
    NS PS T head nk KE st i kc q proto ip4 ip6 port o dp img tg ai ar sec1 birth1 S1 lul1
    (hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) HY)].
  apply andp_left2. unfold hrx5_B8E_Q1. cbv zeta. cbn [hrx5_B8E_W rw_lul rw_D].
  apply andp_right; [apply prop_right; repeat (apply conj; [assumption |]); exact I |].
  apply andp_left2. apply derives_refl.
Qed.

