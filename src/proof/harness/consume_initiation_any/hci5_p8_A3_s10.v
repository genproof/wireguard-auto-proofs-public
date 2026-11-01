(* law consume_initiation_any, phase P8, segment A3, statement s10 (port of v1's hci3_p8_A3_s10.v):
     CHECK(h->last_initiation_consumption == m_last_consumption(s->last_initiation_consumption, now))
   Shared: hci5_p8_A3_defs.v (statements, cut), hci5_p8_A3_pure.v
   (hci5_p8_A3_facts), hci5_p8_A3_sep.v (accessors). *)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Notation W := W_consume_initiation_any.

(* the field last_initiation_consumption of a handshake snapshot, at W *)
Lemma hci5_p8_A3_s10_flic sn y :
  hci5_p8_A3_acc (@field_at W Ews t_hsnap [StructField HH._last_initiation_consumption] (Vlong (hs_lic (sn_hs sn))) y)
    (@data_at W Ews t_hsnap (hsnap_val sn) y).
Proof.
  rewrite <- hci5_p8_A3_HW.
  rewrite <- (@field_at_change_composite HCS W hci5_p8_A3_cceHW Ews t_hsnap
    [StructField HH._last_initiation_consumption] (Vlong (hs_lic (sn_hs sn))) (Vlong (hs_lic (sn_hs sn))) (JMeq_refl _))
    by (vm_compute; reflexivity).
  unfold hci5_p8_A3_acc.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts HCS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif HCS Ews t_hsnap [] (StructField HH._last_initiation_consumption)
    (hsnap_val sn) (Vlong (hs_lic (sn_hs sn))) y); [apply JMeq_refl | auto with field_compatible]|].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (Vlong (hs_lic (sn_hs sn)))).
  apply wand_derives; [apply derives_refl|]. unfold data_at. apply derives_refl'. f_equal.
Qed.

(* that field of node N's snapshot (s = offset_val 8 node), from the node list *)
Lemma hci5_p8_A3_s10_nlic N NS l sn : In N NS -> hn_snap N = hsnap_val sn ->
  hci5_p8_A3_acc (@field_at W Ews t_hsnap [StructField HH._last_initiation_consumption] (Vlong (hs_lic (sn_hs sn)))
    (offset_val 8 (hn_addr N))) (hnodes_rep4 W l NS).
Proof.
  intros Hin Hsn. apply (hci5_p8_A3_nodes_acc _ N); auto. intros nx.
  apply hci5_p8_A3_acc_pure with (c := @field_compatible CKS t_hnode4 [] (hn_addr N));
    [eapply derives_trans; [apply (@data_at_local_facts CKS)|]; apply prop_derives; tauto|].
  intros FC. eapply hci5_p8_A3_acc_trans; [|apply hci5_p8_A3_nfld_snap].
  rewrite (hci5_p8_A3_snap_at _ _ FC), Hsn. apply hci5_p8_A3_s10_flic.
Qed.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_s10_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR)
    hci5_p8_A3_s10 (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. destruct HH as (Hx & Ha & Hxa & Hrep).
  unfold hci5_p8_QA1, hci5_Delta, hci5_R, hci5_p8_A3_s10. simplify_func_tycontext.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct (hci5_p8_A3_facts x25519 aead_enc aead_dec R L NS PS KE T head na M (s_boot S) a P t ck2 h2 Ha H0 Hwf H1 H3)
    as (NS1 & N & NS2 & PS1 & PS2 & HNS & Hna & Hnp & Hsn & Hnr & Hnrest & HPS & Hdel & Hsf & Hin & Hpok & HinT & Hep
        & Hpkn & Hslot & Lt & Lck & Lh).
  pose (Fl := @field_at W Ews t_hsnap [StructField HH._last_initiation_consumption] (Vlong (hs_lic (p_hs P)))
    (offset_val 8 (hci5_nfind NS a))).
  assert (Hnode: hnodes_rep4 W (hci5_head NS) (hnodes_snapped4 T NS PS) |--
    Fl * (Fl -* hnodes_rep4 W (hci5_head NS) (hnodes_snapped4 T NS PS))).
  { unfold Fl. rewrite <- Hna. change (hs_lic (p_hs P)) with (hs_lic (sn_hs (hs_snap_cur T a P))).
    apply hci5_p8_A3_s10_nlic; [rewrite HNS; apply in_elt | exact Hsn]. }
  sep_apply Hnode. Intros.
  rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf). Intros.
  sep_apply (hci5_p8_A3_pk_lic Ews a (hci5_p8_put P M (s_boot S) t ck2 h2)). Intros.
  rewrite (hci5_p8_A3_put_lic P M (s_boot S) t ck2 h2).
  unfold Fl.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - forward.
    forward_call (hs_lic (p_hs P), s_boot S).
    forward.
    forward_if True.
    + exfalso. rewrite Int64.eq_true in H6. exact (Int.one_not_zero H6).
    + forward. entailer!.
    + forward. entailer!.
  - fold Fl.
    sep_apply (hci5_p8_A3_mp Fl (hnodes_rep4 W (hci5_head NS) (hnodes_snapped4 T NS PS))).
    rewrite <- (hci5_p8_A3_put_lic P M (s_boot S) t ck2 h2).
    sep_apply (hci5_p8_A3_mp
      (@field_at W Ews t_hs [StructField prot_repr3.I._last_initiation_consumption]
         (Vlong (hs_lic (p_hs (hci5_p8_put P M (s_boot S) t ck2 h2)))) (hs_addr a))
      (peer_rep Ews a (hci5_p8_put P M (s_boot S) t ck2 h2))).
    Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
    rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf).
    entailer!.
Qed.

End Seg.
