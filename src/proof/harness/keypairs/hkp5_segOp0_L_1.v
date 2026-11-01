(* law keypairs, segment Op0 branch L, piece 1: statements 0..2 (initiator = st == 4; kp = the role's slot; CHECK(kp != NULL)).

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
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers (v1 hkp4_segOp0_L_1.v, 344939a, ported)                          *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hkp5_o0L1_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkp5_o0L1_kps_eq sh p (a b c d: val) :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_kps (a, (b, (c, d))) (kps_addr p) =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._keypairs] (a, (b, (c, d))) p.
Proof.
  intros FC. rewrite prot3_noise_rot_kps_field by auto.
  assert (Hc: cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0L1_CCE) t_peer = true)
    by (vm_compute; reflexivity).
  exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0L1_CCE sh t_peer
           [StructField prot_repr3.I._keypairs] (a, (b, (c, d))) (a, (b, (c, d))) (JMeq_refl _) Hc)).
Qed.

Definition hkp5_o0L1_kps (sh: share) (p: val) (P: peer) : mpred :=
  EX lk: val, @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._keypairs]
                (p_cur P, (p_prev P, (p_next P, lk))) p.

Lemma hkp5_o0L1_peer sh p P :
  peer_rep sh p P = sepcon (hkp5_o0L1_kps sh p P) (prot3_noise_rot_peer_rest sh p P).
Proof.
  rewrite prot3_noise_rot_peer_split. unfold prot3_noise_rot_peer_rest, kps_rep, hkp5_o0L1_kps.
  apply pred_ext.
  - Intros lk. Exists lk. rewrite hkp5_o0L1_kps_eq by auto. entailer!.
  - Intros lk. Exists lk. rewrite hkp5_o0L1_kps_eq by auto. entailer!.
Qed.

Lemma hkp5_o0L1_peer_fold sh p P lk :
  sepcon (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._keypairs]
            (p_cur P, (p_prev P, (p_next P, lk))) p)
         (prot3_noise_rot_peer_rest sh p P) |-- peer_rep sh p P.
Proof. rewrite hkp5_o0L1_peer. unfold hkp5_o0L1_kps. Exists lk. cancel. Qed.

(* a live keypair's entry is in the table's pool with share Ews *)
Lemma hkp5_o0L1_pool p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)) a K :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  In (a, K) KS -> exists E, sfind (t_D T) a = Some (Ews, E).
Proof.
  intros HF. induction HF as [|x y ML' KS' [Hxy Hm] _ IH]; simpl; intros Hi; [contradiction|].
  destruct Hi as [Hy|Hi]; [|auto].
  subst y. simpl in Hxy. subst a. destruct Hm as (_ & Hs & _). eauto.
Qed.

Lemma hkp5_o0L1_tc_kp sht t T a E (R: mpred) :
  sfind (t_D T) a = Some (Ews, E) -> sepcon (itable sht t T) R |-- denote_tc_test_eq a nullval.
Proof.
  intros Hs. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
  apply sepcon_valid_pointer1. eapply prot3_noise_rot_pool_valid; eauto.
Qed.

Lemma hkp5_o0L1_cmp_null v : isptr v ->
  typed_true tint (match sem_unary_operation Onotbool tint (force_val (sem_cmp_pp Cne v (Vlong (Int64.repr 0)))) with
                   | Some v' => v' | None => Vundef end) -> False.
Proof.
  destruct v; try contradiction; intros _ Ht. unfold sem_cmp_pp in Ht. simpl in Ht. discriminate.
Qed.

Lemma hkp5_o0L_1_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> 
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_M2 x25519 F V steps FR i O) hkp5_o0L_s1
    (overridePost (hkp5_o0L_1 x25519 F V steps FR i O) R).
Proof.
  intros HF HX HO.
  unfold hkp5_o0L_facts in HO. cbv zeta in HO.
  unfold hkp5_o0_M2, hkp5_o0L_1, hkp5_Delta.
  unfold hkp5_o0L_props, hkp5_o0L_locals1, hkp5_o0L_fs, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items,
    hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta. cbn [app].
  set (res := o5_res (f_p F) O) in *.
  set (P' := snd (fst (fst res))) in *.
  set (KS' := kw_KS (snd (fst res))) in *.
  set (T' := kw_T (snd (fst res))) in *.
  destruct HO as (_ & _ & _ & _ & _ & _ & Hslot & HinK & _ & _ & _ & _ & Hrel & _).
  destruct (hkp5_o0L1_pool _ _ _ _ _ _ (proj1 (proj1 Hrel)) HinK) as (Ek & HEk).
  rewrite hkp5_o0L1_peer at 1. unfold hkp5_o0L1_kps. Intros lk.
  assert_PROP (isptr (o_kp O)) as Pkp.
  { sep_apply (prot3_noise_rot_ks_ptrs W_keypairs KS'). Intros. apply prop_right.
    match goal with Hk: forall k, In k _ -> isptr k |- _ => apply Hk end.
    apply (in_map fst _ _ HinK). }
  destruct (hkp5_o0L_init O) eqn:Hinit.
  all: destruct R as [Rn Rb Rc Rr].
  all: unfold hkp5_o0L_s1; abbreviate_semax.
  all: assert (Hst: Int.eq (hs_state (p_hs (y_P (o_Y O)))) (Int.repr 4) = hkp5_o0L_init O) by reflexivity.
  - forward. rewrite Hst, Hinit.
    assert (PNc: is_pointer_or_null (p_cur P')) by (rewrite Hslot; apply isptr_is_pointer_or_null; exact Pkp).
    match goal with |- semax _ (PROPx ?PP (LOCALx (?a :: _ :: ?QQ) (SEPx ?SS))) _ _ =>
      forward_if (PROPx PP (LOCALx (a :: temp KC._kp (o_kp O) :: QQ) (SEPx SS))) end.
    { forward. entailer!. }
    { match goal with Hc: Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if.
      { eapply derives_trans; [| apply (hkp5_o0L1_tc_kp Tsh (f_t F) T' (o_kp O) Ek TT HEk)]. cancel. }
      { match goal with Ht: typed_true _ _ |- _ => exfalso; exact (hkp5_o0L1_cmp_null _ Pkp Ht) end. }
      forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    match goal with Hpo := @abbreviate ret_assert _ |- _ => unfold Hpo, abbreviate end.
    cbn [RA_normal overridePost].
    sep_apply (hkp5_o0L1_peer_fold Tsh (f_p F) P' lk).
    entailer!.
  - forward. rewrite Hst, Hinit.
    assert (PNn: is_pointer_or_null (p_next P')) by (rewrite Hslot; apply isptr_is_pointer_or_null; exact Pkp).
    match goal with |- semax _ (PROPx ?PP (LOCALx (?a :: _ :: ?QQ) (SEPx ?SS))) _ _ =>
      forward_if (PROPx PP (LOCALx (a :: temp KC._kp (o_kp O) :: QQ) (SEPx SS))) end.
    { match goal with Hc: ?x <> Int.zero |- _ => exfalso; apply Hc; reflexivity end. }
    { forward. entailer!. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if.
      { eapply derives_trans; [| apply (hkp5_o0L1_tc_kp Tsh (f_t F) T' (o_kp O) Ek TT HEk)]. cancel. }
      { match goal with Ht: typed_true _ _ |- _ => exfalso; exact (hkp5_o0L1_cmp_null _ Pkp Ht) end. }
      forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    match goal with Hpo := @abbreviate ret_assert _ |- _ => unfold Hpo, abbreviate end.
    cbn [RA_normal overridePost].
    sep_apply (hkp5_o0L1_peer_fold Tsh (f_p F) P' lk).
    entailer!.
Qed.
