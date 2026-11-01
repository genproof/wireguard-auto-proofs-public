(* law keypairs, segment Op0 branch L, piece 4r: statement 23 for the responder (the whole if (initiator) .. else ..: the shadow add_new_keypair, else-branch taken).

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
(* Helpers (port of v1's hkp4_o0L4r_*, 64459e3)                            *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0L4r_nonnull3 a b c : NoDup (hk5_nonnull [a; b; c]) ->
  (a = nullval \/ a <> c) /\ (b = nullval \/ b <> c) /\ (b = nullval \/ b <> a).
Proof.
  unfold hk5_nonnull, hk5_eqb. simpl. unfold eq_dec in *.
  destruct (EqDec_val a nullval), (EqDec_val b nullval), (EqDec_val c nullval); simpl; intros ND;
    repeat split; auto; inv ND; try (inv H2); simpl in *; intuition congruence.
Qed.

Lemma hkp5_o0L4r_mklist_ptr ML m : In m (map fst ML) -> hk5_mklist ML |-- !! isptr m.
Proof.
  induction ML as [|[x M] ML IH]; simpl; intros I; [contradiction|].
  destruct I as [<-|I].
  - unfold hk5_node. Intros. entailer!.
  - sep_apply (IH I). entailer!.
Qed.

Lemma hkp5_o0L4r_ptr_or_null ML m : m = nullval \/ In m (map fst ML) -> hk5_mklist ML |-- !! is_pointer_or_null m.
Proof.
  intros [->|I].
  - apply prop_right. simpl; auto.
  - sep_apply (hkp5_o0L4r_mklist_ptr ML m I). entailer!.
Qed.

(* the harness's model after the responder's add_new_keypair *)
Lemma hkp5_o0L4r_H3 F O : hkp5_o0L_init O = false ->
  hkp5_o0L_H3 F O =
    let H := y_H (o_Y O) in
    let r1 := hk5_put (h5_sn H) true ((o_k O, hkp5_o0L_mk F O) :: h5_ML H) (h5_frees H) (h5_warn H) in
    let r2 := hk5_put (h5_sp H) true (fst (fst r1)) (snd (fst r1)) (snd r1) in
    mkH5 (fst (fst r2)) nullval (h5_sc H) (o_k O) (snd (fst r2)) (snd r2).
Proof.
  intros E. unfold hkp5_o0L_H3, hkp5_o0_hl.
  assert (Ei: m5_init (hkp5_o0L_mk F O) = false) by (unfold hkp5_o0L_mk, hkp5_o0_mk; cbn [m5_init]; exact E).
  rewrite Ei. unfold hk5_hput, h5_set_slots, h5_set_ML. cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  destruct (hk5_put (h5_sn (y_H (o_Y O))) _ _ _ _) as [[a b] c]. cbn [fst snd h5_ML h5_frees h5_warn].
  destruct (hk5_put (h5_sp (y_H (o_Y O))) _ _ _ _) as [[a' b'] c']. reflexivity.
Qed.

Lemma hkp5_o0L_4r_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> hkp5_o0L_init O = false ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0L_2 x25519 F V steps FR i O) hkp5_o0L_s4
    (overridePost (hkp5_o0L_3 x25519 F V steps FR i O) R).
Proof.
  intros HM HX HO Hinit.
  unfold hkp5_o0L_2, hkp5_o0L_3, hkp5_Delta.
  rewrite (hkp5_o0L4r_H3 F O Hinit).
  unfold hkp5_o0L_H1, h5_set_ML.
  unfold hkp5_o0L_props, hkp5_o0_props, hkp5_o0L_locals2, hkp5_o0L_SEP, hkp5_o0L_fs, hk5_items, hkp5_globs,
    hkp5_hglobs, hkp5_lvars.
  rewrite Hinit.
  cbv zeta.
  cbn [app h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  set (res := o5_res (f_p F) O).
  set (HH := y_H (o_Y O)).
  set (ML1 := (o_k O, hkp5_o0L_mk F O) :: h5_ML HH).
  Intros.
  match goal with Hi: hkp5_inv0 _ _ _ |- _ => pose proof Hi as Hinv end.
  destruct Hinv as (Hrel & _).
  destruct Hrel as ((_ & ND & _ & _ & _ & Fsl & _) & NDs & _).
  fold HH in ND, Fsl, NDs.
  assert (Isn: h5_sn HH = nullval \/ In (h5_sn HH) (map fst (h5_ML HH))).
  { rewrite Forall_forall in Fsl. apply Fsl. right; right; left; reflexivity. }
  assert (Isp: h5_sp HH = nullval \/ In (h5_sp HH) (map fst (h5_ML HH))).
  { rewrite Forall_forall in Fsl. apply Fsl. left; reflexivity. }
  destruct (hkp5_o0L4r_nonnull3 _ _ _ NDs) as (Dps & _ & _).
  assert (ND1: NoDup (map fst ML1)) by (subst ML1; cbn [map fst]; constructor; assumption).
  assert (In1: h5_sn HH = nullval \/ In (h5_sn HH) (map fst ML1)).
  { subst ML1; cbn [map fst]. destruct Isn as [E | E]; [left; exact E | right; right; exact E]. }
  destruct (hk5_put (h5_sn HH) true ML1 (h5_frees HH) (h5_warn HH)) as [[ML2 fr2] mw2] eqn:E1.
  assert (ND2: NoDup (map fst ML2)).
  { replace ML2 with (fst (fst (hk5_put (h5_sn HH) true ML1 (h5_frees HH) (h5_warn HH)))) by (rewrite E1; reflexivity).
    apply hkp5_o0_put_nodup; exact ND1. }
  assert (In2: h5_sp HH = nullval \/ In (h5_sp HH) (map fst ML2)).
  { destruct Dps as [E | Ne]; [left; exact E |].
    destruct Isp as [E | Isp]; [left; exact E | right].
    replace ML2 with (fst (fst (hk5_put (h5_sn HH) true ML1 (h5_frees HH) (h5_warn HH)))) by (rewrite E1; reflexivity).
    apply hkp5_o0_put_in; [subst ML1; cbn [map fst]; right; exact Isp | exact Ne]. }
  cbn [fst snd].
  destruct (hk5_put (h5_sp HH) true ML2 fr2 mw2) as [[ML3 fr3] mw3] eqn:E2.
  cbn [fst snd].
  destruct R as [Rn Rb Rc Rr].
  unfold hkp5_o0L_s4.
  abbreviate_semax.
  forward_if.
  { match goal with Hc: Int.zero <> Int.zero |- _ => contradiction (Hc eq_refl) end. }
  assert_PROP (is_pointer_or_null (h5_sn HH)) as Psn
    by (sep_apply (hkp5_o0L4r_ptr_or_null ML1 (h5_sn HH) In1); entailer!).
  forward.
  forward.
  forward_call (f_gv F, ML1, h5_frees HH, h5_warn HH, h5_sn HH, true).
  rewrite E1. cbn [fst snd].
  assert_PROP (is_pointer_or_null (h5_sp HH)) as Psp
    by (sep_apply (hkp5_o0L4r_ptr_or_null ML2 (h5_sp HH) In2); entailer!).
  forward.
  forward.
  forward_call (f_gv F, ML2, fr2, mw2, h5_sp HH, true).
  rewrite E2. cbn [fst snd].
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  entailer!.
Qed.
