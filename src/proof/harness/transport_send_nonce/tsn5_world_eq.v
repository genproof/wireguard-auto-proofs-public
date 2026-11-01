(* Law transport_send_nonce: W_tsn5 is the compspecs of transport_send_nonce.whole_prog's composite environment
   (the one harness_safe needs); template: law counter's counter_world_eq.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_world.
Require WgNoise.contracts.x_transport_send_nonce.

Lemma tsn5_env_eq :
  QP.prog_comp_env WgNoise.contracts.x_transport_send_nonce.whole_prog =
  QPcomposite_env_of_composite_env (@cenv_cs W_tsn5) (@ha_env_cs W_tsn5) (@la_env_cs W_tsn5).
Proof. vm_compute; reflexivity. Qed.

Lemma tsn5_OK : QPprogram_OK WgNoise.contracts.x_transport_send_nonce.whole_prog.
Proof.
  split.
  - apply compute_list_norepet_e; reflexivity.
  - rewrite tsn5_env_eq. apply QPcompspecs_OK_i; repeat constructor.
Qed.

Lemma tsn5_eq : W_tsn5 = compspecs_of_QPcomposite_env _ (proj2 tsn5_OK).
Proof.
  apply asm_compspecs_eq; vm_compute; reflexivity.
Qed.
