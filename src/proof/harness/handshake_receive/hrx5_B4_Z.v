(* law handshake_receive, phase B4, segment Z: statement 25 (the model block) for a raw buffer OBuf b (fwd is false): hrx5_B4_Q -> hrx5_S4. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

Lemma hrx5_B4_Z_fwd (b: list byte) : obj_ok (OBuf b) -> hrx5_fwd b = false.
Proof.
  intros (H1 & H2 & H3 & _). unfold hrx5_fwd.
  destruct (4 <=? Zlength b); [| reflexivity]. cbn [andb].
  destruct (Zlength b =? 148) eqn:E1; [apply Z.eqb_eq in E1; contradiction |].
  destruct (Zlength b =? 92) eqn:E2; [apply Z.eqb_eq in E2; contradiction |].
  destruct (Zlength b =? 64) eqn:E3; [apply Z.eqb_eq in E3; contradiction |].
  rewrite !andb_false_r. reflexivity.
Qed.

Lemma hrx5_B4_Z_ok : hrx5_B4_Z_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul
    q proto ip4 ip6 port o dp img HY Ho.
  destruct o as [b | M | M | M]; try contradiction. clear Ho.
  unfold hrx5_B4_Q, hrx5_B4_M, hrx5_Delta.
  Intros.
  abbreviate_semax.
  cbn [obj_bytes obj_kind] in *. rewrite (hrx5_B4_Z_fwd b H3).
  unfold hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app]. repeat apply -> seq_assoc.
  forward_if (temp HRM._t'95 (Vint Int.zero)).
  { congruence. } { forward. entailer!. }
  forward_if (temp HRM._t'96 (Vint Int.zero)).
  { congruence. } { forward. entailer!. }
  forward_if (temp HRM._t'97 (Vint Int.zero)).
  { congruence. } { forward. entailer!. }
  forward_if.
  { congruence. }
  repeat apply -> seq_assoc. forward_if (temp HRM._t'93 (Vint Int.zero)).
  { congruence. } { forward. entailer!. }
  forward_if (temp HRM._t'94 (Vint Int.zero)).
  { congruence. } { forward. entailer!. }
  forward_if.
  { congruence. }
  forward_if (temp HRM._t'92 (Vint Int.zero)).
  { congruence. } { forward. entailer!. }
  forward_if.
  { congruence. }
  forward.
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
  unfold hrx5_S4.
  Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q. Exists proto ip4 ip6 port (OBuf b) dp img nullval.
  Exists 0 0.
  replace (hrx5_scr4 x25519 aead_dec xaead_dec R L T PS (OBuf b) (s_boot S)) with (hrx5_scr L) by reflexivity.
  cbn [obj_bytes obj_kind]. rewrite (hrx5_B4_Z_fwd b H3).
  unfold hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app].
  entailer!.
  unfold hrx5_acc_ok; cbn. auto.
Qed.
