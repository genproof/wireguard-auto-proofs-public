(* The harness's interface for law ae_split_chacha20 (harness/ae_split_chacha20.c), in the law's world
   W_ae_split_chacha20: main's specification (QPmain_spec_ext', postcondition TT: the law is the safety of the
   program, its check being gp_assert) and the context of main's body: the externals main calls (QuickProof.Env's
   malloc, nondet_u8, nondet_u32, gp_assert; asm_env's nondet_bytes of an owned buffer), the wg_laws.h helpers
   (wl_spec.v) and the ChaCha20 inlines of include/crypto/chacha.h compiled into the harness (chacha_init,
   chacha20_crypt, with their shared specifications of aead_spec.v / aead_spec3.v). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_world.
Require WgNoise.contracts.ae_split_chacha20.
Require WgNoise.harness.ae_split_chacha20.code.

#[local] Existing Instance W_ae_split_chacha20.

Definition asc_V : varspecs := QPvarspecs WgNoise.contracts.ae_split_chacha20.Harness.qp.

Definition asc_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition asc_main_spec : ident * funspec :=
  (WgNoise.harness.ae_split_chacha20.code._main,
   QPmain_spec_ext' WgNoise.contracts.ae_split_chacha20.whole_prog tt asc_post).

(* the context of main: every function main calls *)
Definition asc_main_ctx : funspecs :=
  [(_quickproof_malloc, malloc_spec'); nondet_u8_spec; nondet_u32_spec; asm_env.nondet_bytes_spec;
   gp_assert_spec; upto_spec; any_bytes_spec; bytes_eq_spec; chacha_init_spec; chacha20_crypt_spec3].
