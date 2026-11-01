(* law keypairs: the cut of operation 1 (wg_noise_received_with_keypair) into
   Op1a = statement 0: `if (kes != NULL && nondet_u8() % 8 == 0) { a keypair of ANOTHER peer: received_with_keypair,
          CHECK(!r), CHECK(check_all(..)), continue }` (reads the kent list: stated over the common.h v2 layer, later)
   Op1b = statements 1..4: k = NULL or any live node; r = received_with_keypair(&p.keypairs, k ? k->kp : NULL);
          if (k == s_next) { old = s_prev; s_prev = s_cur; m_put(old, 1); s_cur = k; s_next = NULL; CHECK(r) }
          else CHECK(!r).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Export WgNoise.proof.harness.keypairs.hkp5_defs.

Definition hkp5_op1_a : statement := ltac:(let x := eval cbv beta iota delta [nth hkp5_op1_stmts] in
  (nth 0 hkp5_op1_stmts Sskip) in exact x).
Definition hkp5_op1_b : statement := ltac:(let x := eval cbv beta iota delta [hkp5_seql skipn hkp5_op1_stmts] in
  (hkp5_seql (skipn 1 hkp5_op1_stmts)) in exact x).

Lemma hkp5_op1_shape : hkp5_sOp1 = Ssequence hkp5_op1_a hkp5_op1_b.
Proof. reflexivity. Qed.

Definition hkp5_G_Op1b : funspecs :=
  [nondet_u8_spec; hk5_pick_live_spec; P4.wg_noise_received_with_keypair_spec W_keypairs; hk5_m_put_spec;
   check_failed_spec].
