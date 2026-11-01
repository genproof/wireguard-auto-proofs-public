(* law handshake_receive, phase B3, branch kind 0, segment I (the glue of stmt 6):
   the guards of KI1 / KI2 (nk != NULL && len > 148 && nondet_u8() % 4 == 0, then nk != NULL && len > 92 && ...).
   States and statements: hrx5_B3_K0_defs.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_I1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_I2.
Local Open Scope logic.

Section K0IG.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_k0ig_vp NS : forall l N, In N NS -> hnodes_rep4 W_handshake_receive l NS |-- valid_pointer (hn_addr N).
Proof.
  induction NS as [|N0 NS IH]; intros l N HIn; [destruct HIn |].
  simpl hnodes_rep4. Intros nx. destruct HIn as [<- | HIn].
  - subst l. entailer!.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hrx5_k0ig_isptr NS : forall l N, In N NS -> hnodes_rep4 W_handshake_receive l NS |-- !! isptr (hn_addr N).
Proof.
  induction NS as [|N0 NS IH]; intros l N HIn; [destruct HIn |].
  simpl hnodes_rep4. Intros nx. destruct HIn as [<- | HIn].
  - subst l. entailer!. match goal with Hf: field_compatible _ _ _ |- _ => apply Hf end.
  - sep_apply (IH nx N HIn). entailer!.
Qed.

#[local] Hint Resolve hrx5_k0ig_vp : valid_pointer.

Ltac k0ig_fif id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx S))) end.
Ltac k0ig_fifex id :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (EX v: int, PROPx P (LOCALx (temp id (Vint v) :: Q) (SEPx S))) end.

Ltac k0ig_pack0 :=
  unfold hrx5_K0_M, hrx5_K0_M1, hrx5_K0_M2, hrx5_K0_Mc.
Ltac k0ig_pack1 :=
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app]; entailer!.

Ltac k0ig_apply PP HK :=
  eapply semax_pre with (P' := PP);
  [ | match goal with D := _ : tycontext, PO := _ : ret_assert |- _ =>
        unfold PO, abbreviate; change D with (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) end; exact HK ].

Ltac k0ig_false :=
  exfalso; match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => apply H; reflexivity
  | H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: 1 = 0 |- _ => discriminate H
  | H: typed_true _ _ |- _ => revert H; simpl; first [discriminate | intros X; inversion X | congruence]
  | H: typed_false _ _ |- _ => revert H; simpl; first [discriminate | intros X; inversion X | congruence]
  end.

Ltac k0ig_cmp :=
  try (simpl; unfold Int64.ltu; rewrite !Int64.unsigned_repr by rep_lia;
       first [rewrite zlt_true by lia | rewrite zlt_false by lia]; reflexivity).

Ltac k0ig_start :=
  unfold hrx5_Delta, hrx5_K0_M at 1; unfold hrx5_K0_Mc at 1;
  Intros R sec birth S w NS PS T head;
  Intros nk KE st i kc lul q proto;
  Intros ip4 ip6 port B dp.

(* the response part: (nk != NULL && len > 92 && nondet_u8() % 4 == 0) -> I2 *)
Lemma hrx5_k0ig_else {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M x25519 gv L FR)
    (Ssequence hrx5_K0_Ic2 (Sifthenelse (Etempvar HRM._t'36 tint) hrx5_K0_I2 Sskip))
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY.
  pose proof (@hrx5_K0_I2_ok x25519 aead_enc aead_dec xaead_enc xaead_dec _ gv L FR HLEM HY) as HK2.
  revert HK2. generalize (hrx5_RB x25519 gv L FR) as RB. intros RB HK2. destruct RB as [rn rb rc rr].
  k0ig_start.
  unfold hrx5_K0_Ic2, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  assert (HBl: 0 <= Zlength B <= Int.max_unsigned) by (pose proof H3 as HB3; simpl in HB3; destruct HB3 as (_ & _ & _ & HB3); pose proof (Zlength_nonneg B); lia).
  assert (Hnk: nk = nullval \/ In nk (map hn_addr NS)) by apply H0.
  destruct (Val.eq nk nullval) as [En | En].
  - subst nk.
    k0ig_fif HRM._t'35 (Vint Int.zero); [k0ig_false | forward; entailer!; k0ig_cmp |].
    k0ig_fif HRM._t'36 (Vint Int.zero); [k0ig_false | forward; entailer!; k0ig_cmp |].
    forward_if; [k0ig_false |].
    forward. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head nullval KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
  - destruct Hnk as [Hnk | Hnk]; [contradiction |].
    apply list_in_map_inv in Hnk. destruct Hnk as (N & EN & HN). subst nk.
    assert_PROP (isptr (hn_addr N)). { sep_apply (hrx5_k0ig_isptr NS (hrx5_head NS) N HN). entailer!. }
    assert (VP: forall l, hnodes_rep4 W_handshake_receive l NS |-- valid_pointer (hn_addr N))
      by (intros; apply hrx5_k0ig_vp; auto).
    destruct (hn_addr N) as [| | | | | nb no] eqn:EA; try contradiction.
    destruct (Z_lt_dec 92 (Zlength B)) as [Hl | Hl].
    + k0ig_fif HRM._t'35 (Vint Int.one); [forward; entailer!; k0ig_cmp | k0ig_false |].
      k0ig_fifex HRM._t'36.
      { forward_call tt. Intros b. forward.
        { entailer!. try match goal with X: _ /\ Int.repr 4 = Int.mone |- _ => destruct X as [_ X];
            apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate X end. }
        Exists (if Int.eq (Int.mods (Int.repr b) (Int.repr 4)) (Int.repr 0) then Int.one else Int.zero).
        entailer!. destruct (Int.eq _ _); reflexivity. }
      { k0ig_false. }
      Intros v. forward_if.
      * k0ig_apply (hrx5_K0_M2 x25519 gv L FR) HK2. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
      * forward. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
    + k0ig_fif HRM._t'35 (Vint Int.zero); [forward; entailer!; k0ig_cmp | forward; entailer!; k0ig_cmp |].
      k0ig_fif HRM._t'36 (Vint Int.zero); [k0ig_false | forward; entailer!; k0ig_cmp |].
      forward_if; [k0ig_false |].
      forward. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
Qed.

Lemma hrx5_K0_I_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M x25519 gv L FR) hrx5_K0_I
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY.
  pose proof (@hrx5_K0_I1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec _ gv L FR HLEM HY) as HK1.
  pose proof (hrx5_k0ig_else gv L FR HLEM HY) as HKE.
  revert HK1 HKE. generalize (hrx5_RB x25519 gv L FR) as RB. intros RB HK1 HKE. destruct RB as [rn rb rc rr].
  rewrite hrx5_K0_I_eq.
  k0ig_start.
  unfold hrx5_K0_Ic1, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  assert (HBl: 0 <= Zlength B <= Int.max_unsigned) by (pose proof H3 as HB3; simpl in HB3; destruct HB3 as (_ & _ & _ & HB3); pose proof (Zlength_nonneg B); lia).
  assert (Hnk: nk = nullval \/ In nk (map hn_addr NS)) by apply H0.
  destruct (Val.eq nk nullval) as [En | En].
  - subst nk.
    k0ig_fif HRM._t'38 (Vint Int.zero); [k0ig_false | forward; entailer!; k0ig_cmp |].
    k0ig_fif HRM._t'39 (Vint Int.zero); [k0ig_false | forward; entailer!; k0ig_cmp |].
    forward_if; [k0ig_false |].
    k0ig_apply (hrx5_K0_M x25519 gv L FR) HKE. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head nullval KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
  - destruct Hnk as [Hnk | Hnk]; [contradiction |].
    apply list_in_map_inv in Hnk. destruct Hnk as (N & EN & HN). subst nk.
    assert_PROP (isptr (hn_addr N)). { sep_apply (hrx5_k0ig_isptr NS (hrx5_head NS) N HN). entailer!. }
    assert (VP: forall l, hnodes_rep4 W_handshake_receive l NS |-- valid_pointer (hn_addr N))
      by (intros; apply hrx5_k0ig_vp; auto).
    destruct (hn_addr N) as [| | | | | nb no] eqn:EA; try contradiction.
    destruct (Z_lt_dec 148 (Zlength B)) as [Hl | Hl].
    + k0ig_fif HRM._t'38 (Vint Int.one); [forward; entailer!; k0ig_cmp | k0ig_false |].
      k0ig_fifex HRM._t'39.
      { forward_call tt. Intros b. forward.
        { entailer!. try match goal with X: _ /\ Int.repr 4 = Int.mone |- _ => destruct X as [_ X];
            apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate X end. }
        Exists (if Int.eq (Int.mods (Int.repr b) (Int.repr 4)) (Int.repr 0) then Int.one else Int.zero).
        entailer!. destruct (Int.eq _ _); reflexivity. }
      { k0ig_false. }
      Intros v. forward_if.
      * k0ig_apply (hrx5_K0_M1 x25519 gv L FR) HK1. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
      * k0ig_apply (hrx5_K0_M x25519 gv L FR) HKE. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
    + k0ig_fif HRM._t'38 (Vint Int.zero); [forward; entailer!; k0ig_cmp | forward; entailer!; k0ig_cmp |].
      k0ig_fif HRM._t'39 (Vint Int.zero); [k0ig_false | forward; entailer!; k0ig_cmp |].
      forward_if; [k0ig_false |].
      k0ig_apply (hrx5_K0_M x25519 gv L FR) HKE. k0ig_pack0; Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q; Exists proto ip4 ip6 port B dp; k0ig_pack1.
Qed.

End K0IG.
