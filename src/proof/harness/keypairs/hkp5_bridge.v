(* law keypairs: the contexts of the segments lifted into main's context (hc4_G_keypairs: funspec_sub from the v4 common.h specs to the v3 / local specs the segments use). *)
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.common.hc3_lift.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_br_entry_in T a E : t_entry T a = Some E -> In a (saddrs (t_D T)).
Proof.
  unfold t_entry. destruct T as [D L]; simpl. induction D as [|[[x sh] v] D IH]; simpl; [discriminate|].
  destruct (EqDec_val x a); [subst; auto|]. intros H; right; auto.
Qed.

Lemma hkp5_br_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hkp5_br_succ_in T a :
  itable_wf T -> succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & HI & _). destruct (hkp5_br_succ (t_L T) a) as [-> | Hin]; auto.
Qed.

Lemma hkp5_br_itable_wf sh tab T : itable sh tab T |-- !! itable_wf T.
Proof. unfold itable. apply andp_left1. auto. Qed.

Lemma hkp5_br_take : funspec_sub (snd hs_take4_spec) (snd hs_take_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x g. repeat (destruct x as [x ?]). simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
  Exists (x, v1, s0, v0, p, true, s, v, t) (@emp mpred _ _). simpl.
  assert (HD: t_entry_d t (hs_addr v0) = e) by (unfold t_entry_d; rewrite H3; auto).
  unfold hs_snap_cur, hs_mem; rewrite HD. rewrite emp_sepcon.
  apply andp_right.
  - unfold argsassert2assert, local, lift1, liftx; simpl. rewrite sepcon_emp.
    pose proof (hkp5_br_entry_in _ _ _ H3). entailer!.
  - apply prop_right. intros rho. rewrite emp_sepcon, !sepcon_emp. apply andp_derives; auto. apply andp_left2. auto.
Qed.

Lemma hkp5_br_randomize : funspec_sub (snd hs_randomize4_spec) (snd hs_randomize_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x g. repeat (destruct x as [x ?]). simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
  Exists (x, v, p, false) (@emp mpred _ _). simpl. rewrite emp_sepcon.
  apply andp_right.
  - unfold argsassert2assert, local, lift1, liftx; simpl. entailer!.
  - apply prop_right. intros rho. rewrite emp_sepcon. apply andp_left2. auto.
Qed.

Lemma hkp5_br_same : funspec_sub (snd (hs_same4_spec W_keypairs)) (snd hs_same_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x g. repeat (destruct x as [x ?]). simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
  destruct H4 as (HE & Hp & Hsp & Hss & Hps & Hnx).
  assert (HD: t_entry_d t (hs_addr v1) = e) by (unfold t_entry_d; rewrite HE; auto).
  Exists (x, v2, h, s1, v1, p, true, s0, v0, t, [VDev s v d]) (@emp mpred _ _). simpl.
  unfold hs_snap_cur, hs_mem, vobjs; rewrite HD. simpl. rewrite emp_sepcon.
  apply andp_right.
  2:{ apply prop_right. intros rho. rewrite emp_sepcon. apply andp_left2.
      apply andp_derives; auto. apply andp_derives; auto. rewrite !sepcon_emp; auto. }
  unfold argsassert2assert, local, lift1, liftx; simpl.
  pose proof (hkp5_br_entry_in _ _ _ HE).
  assert_PROP (itable_wf t) as HW by (sep_apply (hkp5_br_itable_wf s0 v0 t); entailer!).
  assert (HF: Forall (vp_ok (hs_own v1 t [VDev s v d])) (hs_ptrs h (snap_of t (hs_addr v1) e (p_hs p)))).
  { pose proof (hkp5_br_succ_in t (hs_addr v1) HW) as Hs.
    unfold hs_ptrs, hs_ptrs_nn, snap_of, hs_own, vp_ok; simpl. rewrite Hp, Hsp, Hss, Hps.
    repeat (apply Forall_cons; [simpl; rewrite ?in_app_iff; simpl; intuition auto|]); apply Forall_nil. }
  entailer!.
Qed.

Lemma hkp5_br_zf : funspec_sub (snd (hs_zeroed_from4_spec W_keypairs)) (snd hk5_zf_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x g. repeat (destruct x as [x ?]). simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
  destruct H4 as (HE & Hp & Hsp & Hss & Hps).
  assert (HD: t_entry_d t (hs_addr v1) = e) by (unfold t_entry_d; rewrite HE; auto).
  Exists (x, v2, h, s1, v1, p, true, s0, v0, t, [VDev s v d]) (@emp mpred _ _). simpl.
  unfold hs_snap_cur, hs_mem, vobjs; rewrite HD. simpl. rewrite emp_sepcon.
  apply andp_right.
  2:{ apply prop_right. intros rho. rewrite emp_sepcon. apply andp_left2.
      apply andp_derives; auto. apply andp_derives; auto. rewrite !sepcon_emp; auto. }
  unfold argsassert2assert, local, lift1, liftx; simpl.
  pose proof (hkp5_br_entry_in _ _ _ HE).
  assert_PROP (itable_wf t) as HW by (sep_apply (hkp5_br_itable_wf s0 v0 t); entailer!).
  assert (HF: Forall (vp_ok (hs_own v1 t [VDev s v d])) (hs_ptrs_nn h (snap_of t (hs_addr v1) e (p_hs p)))).
  { pose proof (hkp5_br_succ_in t (hs_addr v1) HW) as Hs.
    unfold hs_ptrs, hs_ptrs_nn, snap_of, hs_own, vp_ok; simpl. rewrite Hp, Hsp, Hss, Hps.
    repeat (apply Forall_cons; [simpl; rewrite ?in_app_iff; simpl; intuition auto|]); apply Forall_nil. }
  entailer!.
Qed.

Lemma hkp5_br_rcf : funspec_sub (snd replay_counter_fresh4_spec) (snd hk5_rcf_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x g. repeat (destruct x as [x ?]). simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
  Exists (x, v0, i, v, l) (@emp mpred _ _). simpl. rewrite emp_sepcon.
  apply andp_right.
  - unfold argsassert2assert, local, lift1, liftx; simpl. entailer!.
  - apply prop_right. intros rho. rewrite emp_sepcon. apply andp_left2.
    rewrite sepcon_emp; unfold rc_fresh; apply derives_refl.
Qed.

(* main's variables are not functions of its context *)
Lemma hkp5_br_vsub x25519 aead_enc aead_dec xaead_enc xaead_dec :
  hc3_Vsub hkp5_V hkp5_V (hkp5_Gmain x25519 aead_enc aead_dec xaead_enc xaead_dec).
Proof. unfold hc3_Vsub; repeat (apply Forall_cons; [split; reflexivity|]); apply Forall_nil. Qed.

(* one callee: its specification in main's context, and the subsumption *)
Ltac hkp5_br_ent :=
  cbv beta;
  match goal with
  | |- exists phi, _ /\ funspec_sub phi (snd hs_take_spec) =>
      exists (snd hs_take4_spec); split; [reflexivity | exact hkp5_br_take]
  | |- exists phi, _ /\ funspec_sub phi (snd hs_same_spec) =>
      exists (snd (hs_same4_spec W_keypairs)); split; [reflexivity | exact hkp5_br_same]
  | |- exists phi, _ /\ funspec_sub phi (snd hs_randomize_spec) =>
      exists (snd hs_randomize4_spec); split; [reflexivity | exact hkp5_br_randomize]
  | |- exists phi, _ /\ funspec_sub phi (snd hk5_zf_spec) =>
      exists (snd (hs_zeroed_from4_spec W_keypairs)); split; [reflexivity | exact hkp5_br_zf]
  | |- exists phi, _ /\ funspec_sub phi (snd hk5_rcf_spec) =>
      exists (snd replay_counter_fresh4_spec); split; [reflexivity | exact hkp5_br_rcf]
  | |- exists phi, _ /\ funspec_sub phi (snd ?ip) =>
      exists (snd ip); split; [reflexivity | apply funspec_sub_refl]
  end.

Lemma hkp5_bridge_ok x25519 aead_enc aead_dec xaead_enc xaead_dec :
  Forall (fun G => tycontext_sub (hkp5_Delta G)
                     (func_tycontext KC.f_main hkp5_V (hkp5_Gmain x25519 aead_enc aead_dec xaead_enc xaead_dec) []))
    [hkp5_G_L0; hkp5_G_Op0; hkp5_G_Op1b; hkp5_G_Op2; hkp5_G_Op3; hkp5_G_Op7; hkp5_G_Op45; hkp5_G_Op6;
     hkp5_G_LC x25519; hkp5_G_Op1a x25519; hkp5_G_A x25519; hkp5_G_F x25519].
Proof.
  repeat apply Forall_cons; try apply Forall_nil;
  unfold hkp5_Delta;
  (apply hc3_tycontext_sub;
   [ unfold hc3_Gsub; repeat (apply Forall_cons; [hkp5_br_ent|]); apply Forall_nil | apply hkp5_br_vsub ]).
Qed.
