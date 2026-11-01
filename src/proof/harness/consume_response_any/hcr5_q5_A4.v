(* law consume_response_any, phase Q5, segment A4: the big CHECK (entry fields, static_identity, snapshot bytes, last consumption).
   States and statements: hcr5_q5_defs.v; pure facts: hcr5_q5_pure.v (its statement is a hypothesis here,
   proved separately); (section Q5);
   src/proof/harness/consume_response_any/hcr3_q5_A4*.v. *)
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
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A4_core.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A4_open.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_q5_A4_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hcr5_q5_pure_stmt x25519 aead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_QA1 x25519 aead_dec gv L FR) hcr5_q5_A4 (overridePost (hcr5_q5_QA1 x25519 aead_dec gv L FR) (hcr5_R gv)).
Proof.
  intros Hy Hpure.
  generalize (hcr5_R gv) as Rr. intros Rr.
  unfold hcr5_q5_QA1. Intros R S NS PS head nb T KE m M. Intros a P ck h.
  assert_PROP (itable_wf T) as HwfT.
  { apply andp_left2. apply (hcr5_q5_A4_sep_prop _ _ (itable Tsh (l_ita L) T)); [hcr5_q5_A4_in | apply hcr5_q5_A4_itable_wf]. }
  destruct Hpure as (_ & _ & _ & Hp4 & _).
  destruct (Hp4 R L NS PS head nb KE T M a P ck h H0 H1 HwfT H4)
    as (NS1 & N & NS2 & PS1 & PS2 & E & _ & Hsf & _ & HNS & HNa & _ & HNs & _ & _ & HE & HEp & _ & Hpok & _).
  clear Hp4.
  destruct Hpok as (_ & _ & _ & Hsid & Hok & _).
  assert (HtE: t_entry_d T (hs_addr a) = E) by (unfold t_entry_d; rewrite HE; reflexivity).
  assert (HNs': hn_snap N = hsnap_val (snap_of T (hs_addr a) E (p_hs P)))
    by (rewrite HNs; unfold hs_snap_cur; rewrite HtE; reflexivity).
  clear HNs HtE.
  assert (HIn: In N (hnodes_snapped4 T NS PS)) by (rewrite HNS; apply in_or_app; right; left; reflexivity).
  clear HNS.
  unfold t_entry in HE. destruct (sfind (t_D T) (hs_addr a)) as [[she E']|] eqn:HS; [|discriminate].
  injection HE as HE. subst E'.
  assert_PROP (Forall isptr (saddrs (t_D T))) as PP.
  { apply andp_left2. apply (hcr5_q5_A4_sep_prop _ _ (itable Tsh (l_ita L) T)); [hcr5_q5_A4_in | apply hcr5_q5_A4_itable_ptrs]. }
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfc.
  { apply andp_left2. apply (hcr5_q5_A4_sep_prop _ _ (peers_rep (supd PS a (hcr5_q5_put P M ck h))));
      [hcr5_q5_A4_in | apply (hcr5_q5_A4_fc_prop PS a P (hcr5_q5_put P M ck h) Hsf)]. }
  assert_PROP (@field_compatible W_consume_response_any t_hsnap [] (offset_val 8 (hcr5_nfind NS a))) as Hfs.
  { apply andp_left2. rewrite <- HNa.
    apply (hcr5_q5_A4_sep_prop _ _ (hnodes_rep4 W_consume_response_any (hcr5_head NS) (hnodes_snapped4 T NS PS)));
      [hcr5_q5_A4_in | apply (hcr5_q5_A4_fcs_prop (hcr5_head NS) _ N HIn)]. }
  assert_PROP (isptr (l_wa L)) as Pwa.
  { apply andp_left2. apply (hcr5_q5_A4_sep_prop _ _ (device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L)));
      [hcr5_q5_A4_in | apply hcr5_q5_A4_dev_ptr]. }
  assert (Hpn: is_pointer_or_null (succ_in (t_L T) (hs_addr a)))
    by (eapply hcr5_q5_A4_ptr_or_null; [exact PP | apply hcr5_q5_A4_succ_in; exact HwfT]).
  assert (Hpa: is_pointer_or_null (e_peer E))
    by (rewrite HEp; destruct Hfc as [Hp _]; destruct a; try contradiction; exact I).
  assert (Hps: is_pointer_or_null (hs_sid (p_hs P)))
    by (rewrite Hsid; unfold id_addr; destruct (l_wa L); try contradiction; exact I).
  set (Cl := hcr5_q5_A4_C (hs_addr a) (offset_val 8 (hcr5_nfind NS a)) she (e_peer E)
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E) (hs_sid (p_hs P))
      (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
      (hs_ts (p_hs P))).
  set (QL := hcr5_q5_A4_QL x25519 gv L FR R S NS PS head T KE m M a P ck h).
  set (Q := hcr5_q5_A4_st gv L (hcr5_khead KE) m a (hcr5_nfind NS a) (hs_addr a)
            (offset_val 8 (hcr5_nfind NS a)) she (e_peer E) (succ_in (t_L T) (hs_addr a))
            (vin (hs_addr a) (t_L T)) (e_type E) (e_index E) (hs_sid (p_hs P)) (hs_lic (p_hs P))
            (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P))
            (fold_right_sepcon Cl -* fold_right_sepcon QL) []).
  apply semax_pre_post with (P' := Q) (R' := overridePost Q Rr).
  - subst Q. unfold hcr5_q5_A4_st. rewrite hcr5_q5_A4_S_eq. apply SEP_entail.
    subst Cl QL.
    exact (hcr5_q5_A4_open x25519 gv L FR R S NS PS head T KE m M a P ck h N E she _
             HwfT Hsf HIn HNa HNs' HS Hok Hfc (derives_refl _)).
  - destruct Rr as [r1 r2 r3 r4]. simpl_ret_assert.
    subst Q. unfold hcr5_q5_A4_st. rewrite hcr5_q5_A4_S_eq.
    eapply derives_trans; [apply SEP_entail with (R' := QL); apply hcr5_q5_A4_mp |].
    Exists R S NS PS head nb T KE m M. Exists a P ck h.
    subst QL. unfold hcr5_q5_A4_QL.
    apply hcr5_q5_A4_prop_intro. simpl. auto 10.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - subst Q. apply hcr5_q5_A4_core.
    unfold hcr5_q5_A4_hyps.
    pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    assert (Hwsh: writable_share she).
    { destruct HwfT as (_ & _ & _ & HF). apply hcr5_q5_A4_sfind_In in HS.
      rewrite Forall_forall in HF. apply (HF _ HS). }
    split; [auto |]. split; [exact Hpa |]. split; [exact Hpn |]. split; [exact Hps |].
    split; [apply hcr5_q5_A4_fch; exact Hfc |]. split; [exact Hfs |].
    split; [exact L1 |]. split; [exact L2 |]. split; [exact L4 |]. split; [exact L5 |]. split; [exact L8 |].
    subst Cl QL.
    exact (hcr5_q5_A4_hv x25519 gv L FR R S NS PS head T KE m M a P ck h E she HwfT Hsf HEp Hsid).
Qed.

End Seg.
