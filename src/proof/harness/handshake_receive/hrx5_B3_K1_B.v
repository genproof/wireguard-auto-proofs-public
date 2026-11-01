(* law handshake_receive, B3 kind 1: segment B (hrx5_B3_K1_defs.v). *)
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

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K1_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Local Open Scope logic.

#[local] Instance hrx5_k1b_cce : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_k1b_init_cs sh (a b: val) (c d e f g: list val) p :
  @data_at Noise.CS sh t_init (a, (b, (c, (d, (e, (f, g)))))) p =
  @data_at W_handshake_receive sh t_init (a, (b, (c, (d, (e, (f, g)))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Noise.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_k1b_vp NS : forall l N, In N NS -> hnodes_rep4 W_handshake_receive l NS |-- valid_pointer (hn_addr N).
Proof.
  induction NS as [|N0 NS IH]; intros l N HIn; [destruct HIn |].
  simpl hnodes_rep4. Intros nx. destruct HIn as [<- | HIn].
  - subst l. entailer!.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hrx5_k1b_isptr NS : forall l N, In N NS -> hnodes_rep4 W_handshake_receive l NS |-- !! isptr (hn_addr N).
Proof.
  induction NS as [|N0 NS IH]; intros l N HIn; [destruct HIn |].
  simpl hnodes_rep4. Intros nx. destruct HIn as [<- | HIn].
  - subst l. entailer!. match goal with Hf: field_compatible _ _ _ |- _ => apply Hf end.
  - sep_apply (IH nx N HIn). entailer!.
Qed.

#[local] Hint Resolve hrx5_k1b_vp : valid_pointer.

Ltac k1b_false :=
  exfalso; match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => apply H; reflexivity
  | H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: 1 = 0 |- _ => discriminate H
  | H: Vptr _ _ = nullval |- _ => discriminate H
  | H: typed_true _ _ |- _ => revert H; simpl; first [discriminate | intros X; inversion X | congruence]
  | H: typed_false _ _ |- _ => revert H; simpl; first [discriminate | intros X; inversion X | congruence]
  end.

Section K1B.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K1_B_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K1_A x25519 gv L FR) hrx5_K1_SB
    (overridePost (hrx5_K1_B x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K1_A, hrx5_K1_St. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port mi img M IMG.
  unfold hrx5_K1_SB, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  unfold hrx5_K1_XA. Intros.
  rewrite <- hrx5_conv_init.
  forward_call (Ews, mi). Intros M0.
  assert (Hnk: nk = nullval \/ In nk (map hn_addr NS)) by apply H0.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Sx))) _ _ =>
    forward_if (EX v: int, PROPx P (LOCALx (temp HRM._t'51 (Vint v) :: Q) (SEPx Sx))) end.
  { destruct Hnk as [Hnk | Hnk].
    - subst nk. entailer!.
    - apply list_in_map_inv in Hnk. destruct Hnk as (N & EN & HN). subst nk.
      assert_PROP (isptr (hn_addr N)). { sep_apply (hrx5_k1b_isptr NS (hrx5_head NS) N HN). entailer!. }
      assert (VP: forall l, hnodes_rep4 W_handshake_receive l NS |-- valid_pointer (hn_addr N))
        by (intros; apply hrx5_k1b_vp; auto).
      destruct (hn_addr N) as [| | | | | nb no] eqn:EA; try contradiction. entailer!. }
  { destruct Hnk as [Hnk | Hnk].
    - subst nk. k1b_false.
    - forward_call tt. Intros b. forward.
      Exists (if Int.eq (Int.and (Int.repr b) (Int.repr 1)) Int.zero then Int.zero else Int.one). entailer!. }
  { destruct Hnk as [Hnk | Hnk].
    - subst nk. forward. Exists Int.zero. entailer!.
    - apply list_in_map_inv in Hnk. destruct Hnk as (N & EN & HN). subst nk.
      assert_PROP (isptr (hn_addr N)). { sep_apply (hrx5_k1b_isptr NS (hrx5_head NS) N HN). entailer!. }
      destruct (hn_addr N) as [| | | | | nb no] eqn:EA; try contradiction. k1b_false. }
  Intros v.
  assert (HX: x25519_props x25519) by (destruct HY; auto).
  assert (HRK: hrx5_run_ok R) by (destruct H; auto).
  assert (LK1: Zlength (mi_priv (hrx5_IK x25519 R)) = 32).
  { unfold hrx5_IK, mident_of, clamp; simpl. destruct HRK. rewrite !Zlength_upd_Znth; auto. }
  assert (LK2: Zlength (mi_pub (hrx5_IK x25519 R)) = 32) by (apply HX).
  assert (LD1: Zlength (mi_priv (hrx5_ID x25519 R)) = 32).
  { unfold hrx5_ID, mident_of, clamp; simpl. destruct HRK. rewrite !Zlength_upd_Znth; auto. }
  assert (LD2: Zlength (mi_pub (hrx5_ID x25519 R)) = 32) by (apply HX).
  assert (LS: Zlength (hrx5_ssk x25519 R) = 32).
  { unfold hrx5_ssk, m_precomputed_model.
    match goal with |- context [if ?b then _ else _] => destruct b end; [apply HX | reflexivity]. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Sx))) _ _ =>
    let F := eval pattern S, M0 in Sx in
    lazymatch F with ?G _ _ =>
    forward_if (EX S1: shim, EX M1: init_msg,
       PROPx (hrx5_base_ok R sec birth S1 :: (s_boot S1 = s_boot S) :: im_ok M1 :: P) (LOCALx Q (SEPx (G S1 M1)))) end end.
  { forward_call (gv, S, w, Ews, mi, M0, Tsh, l_ik L, hrx5_IK x25519 R, l_id L, hrx5_ID x25519 R, Tsh,
                  l_ssk L, hrx5_ssk x25519 R).
    Intros vret. destruct vret as [[M1 sec1] ns]. cbn [fst snd] in *.
    assert (HB: hrx5_base_ok R sec birth (shim_set_real S sec1 (Int64.repr ns))) by (apply HLEM; exact H).
    Exists (shim_set_real S sec1 (Int64.repr ns)) M1. entailer!. }
  { forward. Exists S M0. entailer!. }
  Intros S1 M1.
  forward_call (Int.repr 1). Intros r.
  unfold init_rep at 1. Intros. unfold init_val. rewrite hrx5_k1b_init_cs.
  forward.
  set (M2 := mkIM r (im_sender M1) (im_eph M1) (im_encs M1) (im_enct M1) (im_mac1 M1) (im_mac2 M1)).
  assert (OK2: im_ok M2) by exact H7.
  replace_SEP 0 (init_rep Ews mi M2).
  { unfold init_rep, init_val. subst M2; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
    rewrite hrx5_k1b_init_cs. entailer!. }
  rewrite <- hrx5_conv_bytes.
  forward_call (Ews, img, Ews, mi, M2).
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K1_B x25519 gv L FR) end.
  unfold hrx5_K1_B, hrx5_K1_St.
  Exists R sec birth S1 w NS PS T.
  Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port mi img M2.
  Exists (init_bytes M2).
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  rewrite H6. unfold hrx5_K1_XM.
  go_lower. apply andp_right.
  { apply prop_right. refine (conj H5 (conj H0 (conj H1 (conj H2 (conj H3 (conj (conj OK2 eq_refl) _)))))).
    repeat split; auto. }
  cancel.
Qed.

End K1B.
