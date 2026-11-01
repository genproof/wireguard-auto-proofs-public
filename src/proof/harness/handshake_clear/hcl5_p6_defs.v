(* law handshake_clear, phase P6: the three statements, the opened
   state hcl5_p6_Q (target node at W, cleared peer, lent objects; the rest framed) and small facts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_lem.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

(* the three statements of the phase *)
Definition hcl5_p6_s16 := ltac:(let x := eval cbv delta [hcl5_P6] in hcl5_P6 in
  match x with Ssequence ?a _ => exact a end).
Definition hcl5_p6_s17 := ltac:(let x := eval cbv delta [hcl5_P6] in hcl5_P6 in
  match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hcl5_p6_s18 := ltac:(let x := eval cbv delta [hcl5_P6] in hcl5_P6 in
  match x with Ssequence _ (Ssequence _ ?a) => exact a end).

Lemma hcl5_p6_stmts : hcl5_P6 = Ssequence hcl5_p6_s16 (Ssequence hcl5_p6_s17 hcl5_p6_s18).
Proof. reflexivity. Qed.

Lemma hcl5_p6_peer_fc sh p P : peer_rep sh p P |-- !! @field_compatible Noise.CS t_peer [] p.
Proof. unfold peer_rep. entailer!. Qed.

Lemma hcl5_p6_vo1 sh wg D : vobjs W [VDev sh wg D] = device_rep sh wg D.
Proof. unfold vobjs. simpl. apply sepcon_emp. Qed.

Lemma hcl5_p6_zf T p P :
  zeroed_from (hs_snap_cur T p P) (hs_snap_cur (t_remove T (hs_addr p)) p (p_set_hs P (hs_zero (p_hs P)))) = true.
Proof. unfold hs_snap_cur. apply hcl5_p6_zeroed. Qed.

(* the opened state: the target node at W, the cleared peer, the lent objects, the rest framed *)
Definition hcl5_p6_Q (gv: globals) (L: hcl5_loc) (KE: list kent4) (x p: val) (P: peer) (T: tstate) (nx: val)
  (D: device) (others: list (val * share * peer)) (WN FRM: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp HC._kes (hcl5_khead KE); temp HC._target x; temp HC._h (hs_addr p);
         lvar HC._w t_dev (l_w L); lvar HC._it t_itab (l_it L); lvar HC._pt t_ptab (l_pt L);
         lvar HC._raw (tarray tuchar 32) (l_raw L); lvar HC._pub (tarray tuchar 32) (l_pub L);
         lvar HC._peers (tptr t_hnode4) (l_peers L); lvar HC._ds t_dsnap (l_ds L);
         lvar HC._ss t_ssnap (l_ss L); gvars gv)
  SEP (@data_at W Ews t_hnode4 (hcl5_p6_nv p (hs_snap_cur T p P) (p_refs P) P nx) x;
       peer_rep Ews p (p_set_hs P (hs_zero (p_hs P)));
       itable Tsh (l_it L) (t_remove T (hs_addr p));
       device_rep Tsh (l_w L) D;
       kents_rep W (hcl5_khead KE) (map (kent_snapped T) KE);
       peers_rep others; WN; FRM).

