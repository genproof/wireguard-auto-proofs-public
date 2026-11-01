(* law keypairs, segment Op0 branch L, piece 4i: statement 23 for the initiator (the whole if (initiator) .. else ..: the shadow add_new_keypair, then-branch taken).

   States: hkp5_segOp0_L_defs.v; "Op0 branch L". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Export WgNoise.proof.harness.keypairs.hkp5_segOp0_L_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers (port of v1's 4i) *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0L4i_nonnull3 a b c : NoDup (hk5_nonnull [a; b; c]) ->
  (a = nullval \/ a <> c) /\ (b = nullval \/ b <> c) /\ (b = nullval \/ b <> a).
Proof.
  unfold hk5_nonnull, hk5_eqb. simpl. unfold eq_dec in *.
  destruct (EqDec_val a nullval), (EqDec_val b nullval), (EqDec_val c nullval); simpl; intros ND;
    repeat split; auto; inv ND; try (inv H2); simpl in *; intuition congruence.
Qed.

Lemma hkp5_o0L4i_mklist_ptr ML m : In m (map fst ML) -> hk5_mklist ML |-- !! isptr m.
Proof.
  induction ML as [|[x M] ML IH]; simpl; intros I; [contradiction|].
  destruct I as [<-|I].
  - unfold hk5_node. Intros. entailer!.
  - sep_apply (IH I). entailer!.
Qed.

Lemma hkp5_o0L4i_ptr_or_null ML m : m = nullval \/ In m (map fst ML) -> hk5_mklist ML |-- !! is_pointer_or_null m.
Proof.
  intros [->|I].
  - apply prop_right. simpl; auto.
  - sep_apply (hkp5_o0L4i_mklist_ptr ML m I). entailer!.
Qed.

Lemma hkp5_o0L4i_afind_in {A: Type} (l: list (val * A)) k : In k (map fst l) -> exists M, afind l k = Some M.
Proof.
  induction l as [| [x v] l IH]; cbn [map fst In afind]; [tauto |].
  intros [-> | Hin]; [rewrite if_true by auto; eauto |].
  destruct (eq_dec x k); eauto.
Qed.

Lemma hkp5_o0L4i_focus ML k M : afind ML k = Some M ->
  exists nx Rst, hk5_mklist ML = (data_at Ews t_mk5 (hk5_mk_val M nx) k * Rst)%logic.
Proof.
  induction ML as [| [x X] ML IH]; cbn [afind]; [discriminate |].
  intros E. cbn [hk5_mklist].
  destruct (eq_dec x k) as [<- | Hne].
  - injection E as <-. unfold hk5_node at 1.
    exists (hk5_head ML), ((!! (Zlength (m5_send X) = 32 /\ Zlength (m5_recv X) = 32) &&
      malloc_token Ews t_mk5 x) * hk5_mklist ML)%logic.
    rewrite <- sepcon_assoc. f_equal. rewrite sepcon_andp_prop. reflexivity.
  - destruct (IH E) as (nx & Rst & ->).
    exists nx, (hk5_node x X (hk5_head ML) * Rst)%logic.
    rewrite <- !sepcon_assoc, (sepcon_comm (hk5_node x X (hk5_head ML))). reflexivity.
Qed.

Lemma hkp5_o0L4i_valid ML k : In k (map fst ML) -> hk5_mklist ML |-- valid_pointer k.
Proof.
  intros Hin. destruct (hkp5_o0L4i_afind_in ML k Hin) as [M E].
  destruct (hkp5_o0L4i_focus ML k M E) as (nx & Rst & ->).
  apply sepcon_valid_pointer1. apply data_at_valid_ptr; [auto | reflexivity].
Qed.

Lemma hkp5_o0L_4i_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> hkp5_o0L_init O = true ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0L_2 x25519 F V steps FR i O) hkp5_o0L_s4
    (overridePost (hkp5_o0L_3 x25519 F V steps FR i O) R).
Proof.
  intros HF HX HO Hinit.
  assert (Ei: m5_init (hkp5_o0L_mk F O) = true)
    by (unfold hkp5_o0L_mk, hkp5_o0_mk; cbn [m5_init]; exact Hinit).
  unfold hkp5_o0L_2, hkp5_o0L_3, hkp5_Delta, hkp5_o0L_H3, hkp5_o0_hl.
  rewrite Ei.
  cbv zeta.
  unfold hkp5_o0L_H1, h5_set_ML.
  unfold hkp5_o0L_props, hkp5_o0_props, hkp5_o0L_locals2, hkp5_o0L_SEP, hkp5_o0L_fs, hk5_items, hkp5_globs, hkp5_hglobs,
    hkp5_lvars.
  rewrite Hinit.
  cbv zeta.
  cbn [app h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  set (HH := y_H (o_Y O)) in *.
  set (ML1 := (o_k O, hkp5_o0L_mk F O) :: h5_ML HH).
  destruct (eq_dec (h5_sn HH) nullval) as [Esn | Esn].
  - unfold hk5_hput, h5_set_slots. cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    destruct (hk5_put (h5_sp HH) true ML1 (h5_frees HH) (h5_warn HH)) as [[ML2 fr2] mw2] eqn:E1.
    cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    Intros.
    match goal with Hi: hkp5_inv0 _ _ _ |- _ => pose proof Hi as Hinv end.
    destruct Hinv as (Hrel & _).
    destruct Hrel as ((_ & ND & _ & _ & _ & Fsl & _) & NDs & _).
    assert (Isp: h5_sp HH = nullval \/ In (h5_sp HH) (map fst (h5_ML HH))).
    { rewrite Forall_forall in Fsl. apply Fsl. left; reflexivity. }
    assert (ND1: NoDup (map fst ML1)) by (subst ML1; cbn [map fst]; constructor; assumption).
    assert (In1: h5_sp HH = nullval \/ In (h5_sp HH) (map fst ML1)).
    { subst ML1; cbn [map fst]. destruct Isp as [E | E]; [left; exact E | right; right; exact E]. }
    destruct R as [Rn Rb Rc Rr].
    unfold hkp5_o0L_s4.
    abbreviate_semax.
    forward_if.
    2: (match goal with Hc: _ = Int.zero |- _ => discriminate Hc end).
    forward.
    { rewrite Esn. entailer!. }
    apply semax_if_seq.
    forward_if.
    { apply denote_tc_test_eq_split; rewrite Esn; apply valid_pointer_null. }
    { match goal with Hc: h5_sn HH <> nullval |- _ => contradiction (Hc Esn) end. }
    assert_PROP (is_pointer_or_null (h5_sp HH)) as Psp
      by (sep_apply (hkp5_o0L4i_ptr_or_null ML1 (h5_sp HH) In1); entailer!).
    assert (Isc: h5_sc HH = nullval \/ In (h5_sc HH) (map fst ML1)).
    { rewrite Forall_forall in Fsl. destruct (Fsl (h5_sc HH)) as [E | E]; [right; left; reflexivity | left; exact E |].
      right. subst ML1; cbn [map fst]. right; exact E. }
    assert_PROP (is_pointer_or_null (h5_sc HH)) as Psc
      by (sep_apply (hkp5_o0L4i_ptr_or_null ML1 (h5_sc HH) Isc); entailer!).
    forward.
    forward.
    forward.
    forward_call (f_gv F, ML1, h5_frees HH, h5_warn HH, h5_sp HH, true).
    rewrite E1. cbn [fst snd].
    forward.
    entailer!.
  - unfold hk5_hput, h5_set_slots. cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    destruct (hk5_put (h5_sc HH) true ML1 (h5_frees HH) (h5_warn HH)) as [[ML2 fr2] mw2] eqn:E1.
    cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    destruct (hk5_put (h5_sp HH) true ML2 fr2 mw2) as [[ML3 fr3] mw3] eqn:E2.
    cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    Intros.
    match goal with Hi: hkp5_inv0 _ _ _ |- _ => pose proof Hi as Hinv end.
    destruct Hinv as (Hrel & _).
    destruct Hrel as ((_ & ND & _ & _ & _ & Fsl & _) & NDs & _).
    assert (Isp: h5_sp HH = nullval \/ In (h5_sp HH) (map fst (h5_ML HH))).
    { rewrite Forall_forall in Fsl. apply Fsl. left; reflexivity. }
    assert (Isc0: h5_sc HH = nullval \/ In (h5_sc HH) (map fst (h5_ML HH))).
    { rewrite Forall_forall in Fsl. apply Fsl. right; left; reflexivity. }
    assert (Isn0: h5_sn HH = nullval \/ In (h5_sn HH) (map fst (h5_ML HH))).
    { rewrite Forall_forall in Fsl. apply Fsl. right; right; left; reflexivity. }
    destruct (hkp5_o0L4i_nonnull3 _ _ _ NDs) as (_ & _ & Dcp).
    assert (ND1: NoDup (map fst ML1)) by (subst ML1; cbn [map fst]; constructor; assumption).
    assert (Isn: In (h5_sn HH) (map fst ML1)).
    { subst ML1; cbn [map fst]. right. destruct Isn0 as [E | E]; [contradiction | exact E]. }
    assert (Isc: h5_sc HH = nullval \/ In (h5_sc HH) (map fst ML1)).
    { subst ML1; cbn [map fst]. destruct Isc0 as [E | E]; [left; exact E | right; right; exact E]. }
    assert (In1: h5_sp HH = nullval \/ In (h5_sp HH) (map fst ML1)).
    { subst ML1; cbn [map fst]. destruct Isp as [E | E]; [left; exact E | right; right; exact E]. }
    assert (ND2: NoDup (map fst ML2)).
    { replace ML2 with (fst (fst (hk5_put (h5_sc HH) true ML1 (h5_frees HH) (h5_warn HH)))) by (rewrite E1; reflexivity).
      apply hkp5_o0_put_nodup; exact ND1. }
    assert (In2: h5_sp HH = nullval \/ In (h5_sp HH) (map fst ML2)).
    { destruct (eq_dec (h5_sp HH) nullval) as [E | Np]; [left; exact E | right].
      destruct Isp as [E | Isp]; [contradiction |].
      assert (Ne: h5_sp HH <> h5_sc HH).
      { intros E. destruct Dcp as [Ec | Ec]; [apply Np; rewrite E; exact Ec | apply Ec; symmetry; exact E]. }
      replace ML2 with (fst (fst (hk5_put (h5_sc HH) true ML1 (h5_frees HH) (h5_warn HH)))) by (rewrite E1; reflexivity).
      apply hkp5_o0_put_in; [subst ML1; cbn [map fst]; right; exact Isp | exact Ne]. }
    destruct R as [Rn Rb Rc Rr].
    unfold hkp5_o0L_s4.
    abbreviate_semax.
    forward_if.
    2: (match goal with Hc: _ = Int.zero |- _ => discriminate Hc end).
    assert_PROP (is_pointer_or_null (h5_sn HH)) as Psn
      by (sep_apply (hkp5_o0L4i_ptr_or_null ML1 (h5_sn HH) (or_intror Isn)); entailer!).
    forward.
    apply semax_if_seq.
    forward_if.
    { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      apply (derives_trans _ (hk5_mklist ML1 * TT)%logic); [cancel |].
      apply sepcon_valid_pointer1, hkp5_o0L4i_valid, Isn. }
    2: { match goal with Hc: h5_sn HH = nullval |- _ => contradiction (Esn Hc) end. }
    assert_PROP (is_pointer_or_null (h5_sp HH)) as Psp
      by (sep_apply (hkp5_o0L4i_ptr_or_null ML1 (h5_sp HH) In1); entailer!).
    assert_PROP (is_pointer_or_null (h5_sc HH)) as Psc
      by (sep_apply (hkp5_o0L4i_ptr_or_null ML1 (h5_sc HH) Isc); entailer!).
    forward.
    forward.
    forward.
    forward.
    forward.
    forward_call (f_gv F, ML1, h5_frees HH, h5_warn HH, h5_sc HH, true).
    rewrite E1. cbn [fst snd].
    forward_call (f_gv F, ML2, fr2, mw2, h5_sp HH, true).
    rewrite E2. cbn [fst snd].
    forward.
    replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
    entailer!.
Qed.
