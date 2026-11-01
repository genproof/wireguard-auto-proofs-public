(* law consume_initiation_any, phase P8, segment A3, statement s11 (port of v1's hci3_p8_A3_s11.v):
     CHECK(h->entry.{peer,next,hashed,type,index} == s->.., h->static_identity == s->.., 4 x bytes_eq(h->.., s->.., 32))
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s11_core.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s11_open.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* The CHECK is proved over a small state (hci5_p8_A3_s11_core.v: its sixteen fields and a frame); QA1 is
   opened into that state with the frame = a wand back to QA1's own SEP list (hci5_p8_A3_s11_open.v). *)
Lemma hci5_p8_A3_s11_S_eq hv sv pe nxt hb ty ix sid eph rs ss psk F :
  hci5_p8_A3_s11_S hv sv pe nxt hb ty ix sid eph rs ss psk F =
  hci5_p8_A3_s11_C hv sv pe nxt hb ty ix sid eph rs ss psk ++ [F].
Proof. reflexivity. Qed.

Lemma hci5_p8_A3_s11_fchN p : @field_compatible Noise.CS t_peer [] p -> @field_compatible Noise.CS t_hs [] (hs_addr p).
Proof.
  intros FC. assert (FC1: @field_compatible Noise.CS t_peer (DOT prot_repr3.I._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_s11_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR)
    hci5_p8_A3_s11 (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros Hy. destruct Hy as (Hx & Ha & Hxa & Hrep).
  generalize (hci5_R gv) as Rr. intros Rr.
  unfold hci5_p8_QA1. Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  assert_PROP (itable_wf T) as HwfT.
  { apply andp_left2. apply (hci5_p8_A3_s11_sep_prop _ _ (itable Tsh (l_itb L) T));
      [hci5_p8_A3_s11_in | apply hci5_p8_A3_s11_itable_wf]. }
  destruct (hci5_p8_A3_facts x25519 aead_enc aead_dec R L NS PS KE T head na M (s_boot S) a P t ck2 h2
              Ha H0 HwfT H1 H3)
    as (NS1 & N & NS2 & PS1 & PS2 & HNS & Hna & Hnp & Hsn & Hnr & Hnrest & HPS & Hdel & Hsf & Hin & Hpok & HinT
        & Hep & Hpkn & Hslot & Lt & Lck & Lh).
  destruct Hpok as (_ & _ & Hsid & Hok & _).
  pose proof H0 as (_ & _ & _ & _ & _ & (_ & Hsh & _) & _).
  assert (HinN: In N (hnodes_snapped4 T NS PS)) by (rewrite HNS; apply in_or_app; right; left; reflexivity).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfp.
  { apply andp_left2.
    apply (hci5_p8_A3_s11_sep_prop _ _ (peers_rep (supd PS a (hci5_p8_put P M (s_boot S) t ck2 h2))));
      [hci5_p8_A3_s11_in | apply (hci5_p8_A3_s11_fc_prop PS a P _ Hsf)]. }
  assert (Hfc: @field_compatible Noise.CS t_hs [] (hs_addr a)) by (apply hci5_p8_A3_s11_fchN; exact Hfp).
  assert_PROP (@field_compatible W t_hsnap [] (offset_val 8 (hci5_nfind NS a))) as Hfs.
  { apply andp_left2. rewrite <- Hna.
    apply (hci5_p8_A3_s11_sep_prop _ _ (hnodes_rep4 W (hci5_head NS) (hnodes_snapped4 T NS PS)));
      [hci5_p8_A3_s11_in | apply (hci5_p8_A3_s11_fcs_prop _ _ N HinN)]. }
  assert_PROP (isptr (l_wb L)) as Pwb.
  { apply andp_left2. apply (hci5_p8_A3_s11_sep_prop _ _ (device_rep Tsh (l_wb L) (hci5_DB x25519 R L)));
      [hci5_p8_A3_s11_in | apply hci5_p8_A3_s11_dev_ptr]. }
  assert_PROP (is_pointer_or_null (succ_in (t_L T) (hs_addr a))) as Hpn.
  { destruct (hci5_p8_A3_s11_succ_in (t_L T) (hs_addr a)) as [E | E];
      [rewrite E; apply prop_right; simpl; auto |].
    apply andp_left2. eapply derives_trans.
    - apply (hci5_p8_A3_s11_sep_prop _ _ (itable Tsh (l_itb L) T));
        [hci5_p8_A3_s11_in | apply (hci5_p8_A3_s11_itable_ptr _ _ _ _ E)].
    - apply prop_derives. intros Hp. destruct (succ_in (t_L T) (hs_addr a)); try contradiction; exact I. }
  assert (Hpa: is_pointer_or_null (e_peer (t_entry_d T (hs_addr a))))
    by (rewrite Hep; destruct Hfp as [Hp _]; destruct a; try contradiction; exact I).
  assert (Hps: is_pointer_or_null (hs_sid (p_hs P)))
    by (rewrite Hsid; unfold id_addr; destruct (l_wb L); try contradiction; exact I).
  set (Cl := hci5_p8_A3_s11_C (hs_addr a) (offset_val 8 (hci5_nfind NS a)) (e_peer (t_entry_d T (hs_addr a)))
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a)))
      (e_index (t_entry_d T (hs_addr a)))
      (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))).
  set (QL := hci5_p8_A3_s11_QL x25519 gv L FR R S w NS PS T head KE m M a P t ck2 h2 key spub).
  set (Q := hci5_p8_A3_s11_st gv L (hci5_khead KE) m (Vlong (s_boot S)) a (hci5_nfind NS a) (hs_addr a)
            (offset_val 8 (hci5_nfind NS a)) (e_peer (t_entry_d T (hs_addr a))) (succ_in (t_L T) (hs_addr a))
            (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a))) (e_index (t_entry_d T (hs_addr a)))
            (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
            (fold_right_sepcon Cl -* fold_right_sepcon QL) []).
  apply semax_pre_post with (P' := Q) (R' := overridePost Q Rr).
  - subst Q. unfold hci5_p8_A3_s11_st. rewrite hci5_p8_A3_s11_S_eq. apply SEP_entail.
    subst Cl QL.
    exact (hci5_p8_A3_s11_open x25519 gv L FR R S w NS PS T head KE m M a P t ck2 h2 key spub N _
             HinT Hsh Hsf Hfc HinN Hna Hsn Hok (derives_refl _)).
  - destruct Rr as [r1 r2 r3 r4]. simpl_ret_assert.
    subst Q. unfold hci5_p8_A3_s11_st. rewrite hci5_p8_A3_s11_S_eq.
    eapply derives_trans; [apply SEP_entail with (R' := QL); apply hci5_p8_A3_s11_mp |].
    Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    subst QL. unfold hci5_p8_A3_s11_QL.
    apply hci5_p8_A3_s11_prop_intro. simpl. auto 10.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - subst Q. apply hci5_p8_A3_s11_core.
    unfold hci5_p8_A3_s11_hyps.
    pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    split; [exact Hpa |]. split; [exact Hpn |]. split; [exact Hps |].
    split; [apply hci5_p8_A3_s11_fch; exact Hfp |]. split; [exact Hfs |].
    split; [exact L1 |]. split; [exact L2 |]. split; [exact L4 |]. split; [exact L5 |].
    rewrite hci5_p8_A3_s11_S_eq. subst Cl QL.
    exact (hci5_p8_A3_s11_hv x25519 gv L FR R S w NS PS T head KE m M a P t ck2 h2 key spub _ Hsf Hsid Hep).
Qed.

End Seg.
