(* main's unit, context and
   specification.  main is proved at the world W_transport_keepalive with the whole
   program's varspecs; it imports the environment, the kernel AEAD, wg_counter_validate (ht4k_cnt.v), the shared common.h functions it calls and the transport.h shadow model. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Export WgNoise.proof.harness.common4t.ht4_worlds.
Require Export WgNoise.proof.harness.common4t.ht4c_spec.
Require Export WgNoise.proof.harness.common4t.ht4r_spec.
Require Export WgNoise.proof.harness.common4t.ht4a_aead.
Require Export WgNoise.proof.harness.transport_keepalive.ht4k_wm_spec.
Require Export WgNoise.proof.harness.transport_keepalive.ht4k_cnt.
Require WgNoise.contracts.x_transport_keepalive.
Require WgNoise.harness.x_transport_keepalive.code.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Module KA := WgNoise.harness.x_transport_keepalive.code.

(* rp_final's static minusp in this program *)
Definition hka5_mp : ident := KA._x_transport_keepalive__minusp.

(* the varspecs of the whole program (literal) *)
Definition hka5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_transport_keepalive.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hka5 : unit_ctx := mk_unit W_transport_keepalive hka5_V KA.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition hka5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hka5_main_spec : ident * funspec :=
  (KA._main, QPmain_spec_ext' WgNoise.contracts.x_transport_keepalive.whole_prog tt hka5_post).

(* what main calls *)
Definition hka5_imports (cs: compspecs) : funspecs :=
  @asm_env.env_specs W_transport_keepalive ++
  [@ht4_encrypt_spec W_transport_keepalive; @ht4_decrypt_spec W_transport_keepalive; ht4k_cnt_validate_spec;
   ht4_check_failed_spec; @ht4_le32_store_spec W_transport_keepalive;
   @ht4_le64_store_spec W_transport_keepalive; ref_aead_decrypt_spec_n W_transport_keepalive hka5_mp] ++
  ht4k_wm_G.

Definition hka5_G : funspecs := [hka5_main_spec].

(* the context of main's body proof *)
Definition hka5_Gprog : funspecs := hka5_imports W_transport_keepalive ++ hka5_G.
