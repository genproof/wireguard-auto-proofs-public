(* law prim_aead: the harness piece, from the body files. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require WgNoise.proof.harness.prim_aead.haead_small_body3 WgNoise.proof.harness.prim_aead.haead_chacha_body3
        WgNoise.proof.harness.prim_aead.haead_rp_body3 WgNoise.proof.harness.prim_aead.haead_tag_body3
        WgNoise.proof.harness.prim_aead.haead_ref_body3 WgNoise.proof.harness.prim_aead.haead_cda_body3
        WgNoise.proof.harness.prim_aead.haead_main_body3.
Require WgNoise.proof.harness.hrp1305_math3 WgNoise.proof.harness.prim_aead.haead_model3
        WgNoise.proof.harness.prim_aead.haead_props3.

Lemma haead_hrp_facts_ok : haead_hrp_facts.
Proof.
  Import WgNoise.proof.harness.hrp1305_math3.
  split; [exact hrp_add_length |]. split; [exact hrp_init_r_length |]. split; [exact hrp_mul_length |].
  split; [exact hrp_final_h_length |]. split; [exact hrp_final_out_length |]. split; [exact hrp_inv_zero |].
  split; [exact hrp_init_r_ok |]. split; [exact hrp_block_c_ok |]. split; [exact hrp_mul_ok | exact hrp_final_ok].
Qed.

Lemma haead_hyps_ok : haead_hyps.
Proof.
  split; [exact haead_hrp_facts_ok |].
  split; [exact (haead_model3.haead_model3_all haead_hrp_facts_ok) | exact haead_props3.haead_props3_ok].
Qed.

Theorem haead_piece3 : piece_ok [u_haead] haead_imports haead_G.
Proof.
  destruct (haead_small_body3.haead_small_bodies3 haead_hyps_ok) as [B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 [B9 B10]]]]]]]]].
  destruct (haead_chacha_body3.haead_chacha_bodies3 haead_hyps_ok) as [C1 [C2 [C3 [C4 [C5 C6]]]]].
  destruct (haead_rp_body3.haead_rp_bodies3 haead_hyps_ok) as [R1 [R2 [R3 [R4 R5]]]].
  destruct (haead_tag_body3.haead_tag_bodies3 haead_hyps_ok) as [T1 [T2 T3]].
  destruct (haead_ref_body3.haead_ref_bodies3 haead_hyps_ok) as [E1 [E2 [E3 E4]]].
  pose proof (haead_cda_body3.haead_cda_body3 haead_hyps_ok) as D.
  pose proof (haead_main_body3.haead_main_body3 haead_hyps_ok) as M.
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  change (haead_imports (u_cs u_haead) ++ haead_G) with haead_Gprog.
  repeat constructor.
  all: exists u_haead; split; [left; reflexivity |]; eexists; split; [reflexivity | assumption].
Qed.
