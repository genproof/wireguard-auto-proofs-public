(* law handshake_receive, phase B8 branch I, segment I2: CHECK(h->entry.peer/next/hashed/type/index == s->.., static_identity, 4 x bytes_eq with s)  (QI -> QI).

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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I2_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I2_core.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I2_open.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* The CHECK is proved over a small state (hrx5_B8_I_I2_core.v: its sixteen fields and a frame); QI is opened into
   that state with the frame = a wand back to QI's own SEP list (hrx5_B8_I_I2_open.v).  Port of consume_initiation_any's
   hci5_p8_A3_s11.v. *)
Lemma hrx5_B8I_I2_S_eq hv sv pe nxt hb ty ix sid eph rs ss psk F :
  hrx5_B8I_I2_S hv sv pe nxt hb ty ix sid eph rs ss psk F =
  hrx5_B8I_I2_C hv sv pe nxt hb ty ix sid eph rs ss psk ++ [F].
Proof. reflexivity. Qed.

Lemma hrx5_B8I_I2_fchN p : @field_compatible Noise.CS t_peer [] p -> @field_compatible Noise.CS t_hs [] (hs_addr p).
Proof.
  intros FC. assert (FC1: @field_compatible Noise.CS t_peer (DOT prot_repr3.I._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

Lemma hrx5_B8I_I2_ok : hrx5_B8I_I2_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q
    proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1 S1 lul1 HY.
  generalize (hrx5_RB x25519 gv L FR) as Rr. intros Rr.
  unfold hrx5_B8I_QI at 1. unfold hrx5_B8I_props. cbv zeta.
  Intros.
  match goal with H: hrx5_inv _ _ _ _ _ _ _ _ _ |- _ => rename H into Hinv end.
  match goal with H: hrx5ci_tgt _ _ _ _ _ _ = Some _ |- _ => rename H into Htgt end.
  set (QL := hrx5_B8I_I2_QL x25519 gv L FR R S w NS PS T head KE kc q proto ip4 ip6 port M dp img a P t ck2 h2 key
               spub sec1 birth1 S1 lul1).
  change (hrx5_B8I_world x25519 gv L R sec1 birth1 T head (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) S1 w
     kc lul1 (hrx5_B8I_log a (l_skb L) (sk_len (hrx5_skb dp (OInit M) proto ip4 ip6 port))) ++
   hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
   hrx5_cglobs gv FR ++
   [qlen_rep gv q; skb_rep Tsh (l_skb L) (hrx5_skb dp (OInit M) proto ip4 ip6 port); @malloc_token W Ews t_init dp;
    init_rep Ews dp M; img_rep img (init_bytes M)] ++
   hrx5_B8I_scr x25519 L R sec1 birth1 head S w (hrx5_skb dp (OInit M) proto ip4 ip6 port) ck2 h2 key spub t)
    with QL.
  assert_PROP (itable_wf T) as HwfT.
  { apply andp_left2. apply (hrx5_B8I_I2_sep_prop _ _ (itable Tsh (l_itd L) T));
      [subst QL; hrx5_B8I_I2_in | apply hrx5_B8I_I2_itable_wf]. }
  destruct (hrx5_B8I_I2_facts x25519 aead_dec R L NS PS KE T head nk M (s_boot S) a P t ck2 h2 Hinv HwfT Htgt)
    as (N & HinN & Hna & Hsn & Hsf & Hok & Hsid & HinT & Hsh & Hep).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfp.
  { apply andp_left2. apply (hrx5_B8I_I2_sep_prop _ _ (peers_rep (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2))));
      [subst QL; hrx5_B8I_I2_in | apply (hrx5_B8I_I2_fc_prop PS a P _ Hsf)]. }
  assert (Hfc: @field_compatible Noise.CS t_hs [] (hs_addr a)) by (apply hrx5_B8I_I2_fchN; exact Hfp).
  assert_PROP (@field_compatible W t_hsnap [] (offset_val 8 (hrx5_nfind NS a))) as Hfs.
  { apply andp_left2. rewrite <- Hna.
    apply (hrx5_B8I_I2_sep_prop _ _ (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)));
      [subst QL; hrx5_B8I_I2_in | apply (hrx5_B8I_I2_fcs_prop _ _ N HinN)]. }
  assert_PROP (isptr (l_wd L)) as Pwd.
  { apply andp_left2. apply (hrx5_B8I_I2_sep_prop _ _ (device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec1 birth1)));
      [subst QL; hrx5_B8I_I2_in | apply hrx5_B8I_I2_dev_ptr]. }
  assert_PROP (is_pointer_or_null (succ_in (t_L T) (hs_addr a))) as Hpn.
  { destruct (hrx5_B8I_I2_succ_in (t_L T) (hs_addr a)) as [E | E];
      [rewrite E; apply prop_right; simpl; auto |].
    apply andp_left2. eapply derives_trans.
    - apply (hrx5_B8I_I2_sep_prop _ _ (itable Tsh (l_itd L) T));
        [subst QL; hrx5_B8I_I2_in | apply (hrx5_B8I_I2_itable_ptr _ _ _ _ E)].
    - apply prop_derives. intros Hp. destruct (succ_in (t_L T) (hs_addr a)); try contradiction; exact I. }
  assert (Hpa: is_pointer_or_null (e_peer (t_entry_d T (hs_addr a))))
    by (rewrite Hep; destruct Hfp as [Hp _]; destruct a; try contradiction; exact I).
  assert (Hps: is_pointer_or_null (hs_sid (p_hs P)))
    by (rewrite Hsid; unfold id_addr; destruct (l_wd L); try contradiction; exact I).
  set (Cl := hrx5_B8I_I2_C (hs_addr a) (offset_val 8 (hrx5_nfind NS a)) (e_peer (t_entry_d T (hs_addr a)))
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a)))
      (e_index (t_entry_d T (hs_addr a)))
      (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))).
  set (Q := hrx5_B8I_I2_st gv L NS nk KE st i S lul1 dp img M T a (hs_addr a)
            (offset_val 8 (hrx5_nfind NS a)) (e_peer (t_entry_d T (hs_addr a))) (succ_in (t_L T) (hs_addr a))
            (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a))) (e_index (t_entry_d T (hs_addr a)))
            (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
            (fold_right_sepcon Cl -* fold_right_sepcon QL) []).
  apply semax_pre_post with (P' := Q) (R' := overridePost Q Rr).
  - subst Q. unfold hrx5_B8I_I2_st. rewrite hrx5_B8I_I2_S_eq. apply SEP_entail.
    subst Cl QL.
    exact (hrx5_B8I_I2_open x25519 gv L FR R S w NS PS T head KE kc q proto ip4 ip6 port M dp img a P t ck2 h2 key
             spub sec1 birth1 S1 lul1 N _ HinT Hsh Hsf Hfc HinN Hna Hsn Hok (derives_refl _)).
  - destruct Rr as [r1 r2 r3 r4]. simpl_ret_assert.
    subst Q. unfold hrx5_B8I_I2_st. rewrite hrx5_B8I_I2_S_eq.
    eapply derives_trans; [apply SEP_entail with (R' := QL); apply hrx5_B8I_I2_mp |].
    subst QL. unfold hrx5_B8I_QI, hrx5_B8I_props. cbv zeta.
    apply hrx5_B8I_I2_prop_intro. simpl. auto 20.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - subst Q. apply hrx5_B8I_I2_core.
    unfold hrx5_B8I_I2_hyps.
    pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    split; [exact Hpa |]. split; [exact Hpn |]. split; [exact Hps |].
    split; [apply hrx5_B8I_I2_fch; exact Hfp |]. split; [exact Hfs |].
    split; [exact L1 |]. split; [exact L2 |]. split; [exact L4 |]. split; [exact L5 |].
    rewrite hrx5_B8I_I2_S_eq. subst Cl QL.
    exact (hrx5_B8I_I2_hv x25519 gv L FR R S w NS PS T head KE kc q proto ip4 ip6 port M dp img a P t ck2 h2 key
             spub sec1 birth1 S1 lul1 _ Hsf Hsid Hep).
Qed.
