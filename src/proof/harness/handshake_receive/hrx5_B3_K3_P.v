(* law handshake_receive, phase B3, branch kind 3, segment P:
   stmt 6 (maybe a reply that decrypts for a picked node: hnodes_pick, insert its handshake entry if not hashed, receiver_index, have_sent_mac1 = true, nondet_bytes ck, xchacha20poly1305_encrypt): hrx5_K3_F -> hrx5_K3_F (new world: hrx5_B3_lem_stmt).
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Local Open Scope logic.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P_1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P_2.

Lemma hrx5_k3p_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hrx5_k3p_vp l NS : hnodes_rep4 W l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - Intros. subst l. apply valid_pointer_null.
  - Intros nx. subst l.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; computable].
Qed.

Lemma hrx5_k3p_seq {Espec: OracleKind} {cs: compspecs} Delta P Q R c1 c2 :
  semax Delta P c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros H1 H2. apply semax_seq with Q; auto.
  destruct R as [Rn Rb Rc Rr].
  eapply semax_post; [| | | | exact H1]; simpl; intros; try (apply andp_left2; apply derives_refl);
    apply andp_left2; apply FF_left.
Qed.

Section K3P.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3_P_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K3_F x25519 gv L FR) hrx5_K3_SP
    (overridePost (hrx5_K3_F x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY.
  pose proof (@hrx5_K3P_1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec) as HK1.
  pose proof (@hrx5_K3P_2_ok x25519 aead_enc aead_dec xaead_enc xaead_dec) as HK2.
  unfold hrx5_K3P_1_stmt in HK1. unfold hrx5_K3P_2_stmt in HK2.
  rewrite hrx5_K3P_SP_eq.
  rewrite (hrx5_K3P_F_eq x25519 gv L FR) at 1.
  unfold hrx5_Delta. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port mc img M.
  unfold hrx5_K3P_st, hrx5_K3P_props, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr;
    cbn [app].
  unfold hrx5_RB, hrx5_R. unfold hrx5_K3P_G, hrx5_K3P_c. abbreviate_semax.
  Intros. rename H into Hb, H0 into Hinv, H1 into Hst, H2 into Hi, H3 into Hmc, H4 into Hcm.
  assert_PROP (is_pointer_or_null (hrx5_head NS)) as Hpn by (sep_apply (hrx5_k3p_pn (hrx5_head NS) NS); entailer!).
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (EX v: int, PROPx ((v <> Int.zero -> NS <> []) :: P) (LOCALx (temp HM._t'68 (Vint v) :: Q) (SEPx SS))) end.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    eapply derives_trans with (hnodes_rep4 W (hrx5_head NS) NS * TT); [cancel |].
    apply sepcon_valid_pointer1, hrx5_k3p_vp. }
  { forward_call tt. Intros b. forward.
    match goal with |- context [temp HM._t'68 (Vint ?v)] => Exists v end. entailer!.
    all: try (intros _; destruct NS; [contradiction | discriminate]). }
  { forward. Exists Int.zero. entailer!. }
  Intros v.
  forward_if.
  - (* the reply for a picked node: P1 ; P2 *)
    assert (HNS: NS <> []) by auto.
    apply hrx5_K3P_body_split.
    eapply hrx5_k3p_seq.
    + eapply semax_pre;
        [| match goal with D := _ : tycontext |- _ =>
             change D with (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec);
             exact (HK1 Espec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port mc img M
                      HLEM HY HNS) end ].
      unfold hrx5_K3P_st, hrx5_K3P_props, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr;
        cbn [app].
      go_lower. apply andp_right.
      * apply prop_right. refine (conj Hb (conj Hinv (conj Hst (conj Hi (conj Hmc (conj Hcm _)))))).
        repeat split; try reflexivity; rewrite eqb_type_refl; reflexivity.
      * cancel.
    + Intros S1 T1 idx j P1.
      pose proof (HK2 Espec gv L FR R sec birth S1 w NS PS T1 head nk KE st i kc lul q proto ip4 ip6 port mc img
                    (hrx5_K3P_rcv M idx) j P1 HLEM HY) as HK2'.
      unfold hrx5_RB, hrx5_R in HK2'.
      match goal with D := _ : tycontext, PO := _ : ret_assert |- _ =>
        unfold PO, abbreviate; change D with (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec); exact HK2' end.
  - (* no reply: nothing changes *)
    forward.
    rewrite (hrx5_K3P_F_eq x25519 gv L FR).
    Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port mc img M.
    unfold hrx5_K3P_st, hrx5_K3P_props, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr;
      cbn [app].
    go_lower. apply andp_right.
    * apply prop_right. refine (conj Hb (conj Hinv (conj Hst (conj Hi (conj Hmc (conj Hcm _)))))).
        repeat split; try reflexivity; rewrite eqb_type_refl; reflexivity.
    * cancel.
Qed.

End K3P.
