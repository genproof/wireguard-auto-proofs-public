(* law keypairs, the end F of main: the cut of hkp5_segF (statements
   30..40 of main) and its states.

   hkp5_segF = hkp5_seql (hkp5_l 30 11) = hkp5_seql (lA ++ lH ++ lC ++ lZ):
     A = hkp5_l 30 2 : wg_noise_keypairs_clear(&p.keypairs); { old = s_next; s_next = NULL; m_put(old, 1);
                       prev; cur }                         : hkp5_Inv -> hkp5F_S hkp5F_P1   (port of hkp5_segOp3)
     H = hkp5_l 32 1 : for (k = live; k; k = kn) { kn = k->next; while (k->held > 0) { k->held--;
                       wg_noise_keypair_put(k->kp, false); if (k->refs == 1) { m_put(k, 0); break; } m_put(k, 0); } }
                                                           : hkp5F_S hkp5F_P1 -> hkp5F_S hkp5F_P2
     C = hkp5_l 33 5 : CHECK(check_all(&p, &t, &w)); nlive = 0; for (k = live; k; k = k->next)
                       { CHECK(k->refs == M_SATURATED && !k->hashed); nlive++; }
                       CHECK(allocs - allocs0 == frees - frees0 + nlive); CHECK(the warnings 2, 1, 4 == warn0's)
                                                           : hkp5F_S hkp5F_P2 -> hkp5F_S hkp5F_P2
     Z = hkp5_l 38 3 : kents_free(kes); hnodes_free(others); return 0
                                                           : hkp5F_S hkp5F_P2 -> main's return (hkp5_R)
   The state hkp5F_S: the loop's state (hkp5_inv, hkp5_SEP with the other peers hkp5_othR .. O * FR) without i,
   plus a fact on the harness's model: P1 = the three slots NULL; P2 = P1 and every live node SATURATED. *)
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
Require Export WgNoise.proof.harness.keypairs.hkp5_spec.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition hkp5F_sA := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in
  (hkp5_seql (hkp5_l 30 2)) in exact x).
Definition hkp5F_sH := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in
  (hkp5_seql (hkp5_l 32 1)) in exact x).
Definition hkp5F_sC := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in
  (hkp5_seql (hkp5_l 33 5)) in exact x).
Definition hkp5F_sZ := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in
  (hkp5_seql (hkp5_l 38 3)) in exact x).

Lemma hkp5F_shape :
  hkp5_segF = hkp5_seql (hkp5_l 30 2 ++ hkp5_l 32 1 ++ hkp5_l 33 5 ++ hkp5_l 38 3) /\
  hkp5F_sA = hkp5_seql (hkp5_l 30 2) /\ hkp5F_sH = hkp5_seql (hkp5_l 32 1) /\
  hkp5F_sC = hkp5_seql (hkp5_l 33 5) /\ hkp5F_sZ = hkp5_seql (hkp5_l 38 3) /\
  hkp5_l 30 2 <> [] /\ hkp5_l 32 1 <> [] /\ hkp5_l 33 5 <> [] /\ hkp5_l 38 3 <> [] /\
  hkp5_l 32 1 ++ hkp5_l 33 5 ++ hkp5_l 38 3 <> [] /\ hkp5_l 33 5 ++ hkp5_l 38 3 <> [].
Proof. repeat split; discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

(* the facts on the harness's model *)
Definition hkp5F_P1 (H: hk5_state) : Prop :=
  h5_sp H = nullval /\ h5_sc H = nullval /\ h5_sn H = nullval.
Definition hkp5F_P2 (H: hk5_state) : Prop :=
  hkp5F_P1 H /\ Forall (fun x => m5_refs (snd x) = REFCOUNT_SATURATED) (h5_ML H).

Section States.
Variable x25519: list byte -> list byte -> list byte.

Definition hkp5F_S (F: hkp5_fix) (V: hkp5_val) (steps: Z) (O: hkp5_oth) (FR: mpred) (Pr: hk5_state -> Prop)
  : environ -> mpred :=
  EX Y: hkp5_dyn,
  PROPx [hkp5_fix_ok F V; hkp5_inv F V Y; Pr (y_H Y)]
  (LOCALx (hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O * FR)))).

End States.
