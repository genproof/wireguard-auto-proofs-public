(* handshake_safe3_from.
   The law handshake (harness/handshake.c), from the lower pieces (the hypotheses), the libc piece, the
   protocol piece (prot_piece3.v), the common.h piece (hc_bodies3.v) and the law's own piece (main and the
   harness's local functions), assembled with asm_lib's asm_harness_safe in the world W_handshake (wg3_worlds.v).
   spec-hc3, spec-protocol3, recipe-assembly, recipe-worlds. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.
Require WgNoise.contracts.x_handshake.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_asm.
Require WgNoise.proof.libc.libc_bytes.

(* prot_rep_lemmas3 gives hhs3_rep (its last conjunct states the keypair's bytes at the world compspecs) *)
Lemma hhs3_rep_ok : hhs3_rep.
Proof.
  destruct prot_rep_lemmas3 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  repeat (split; [assumption |]).
  intros CSw k K E n h. rewrite (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs Noise.CS CSw).
  apply A8.
Qed.

Lemma handshake_safe3_from :
  blake2s3_ok ->
  (exists (G: funspecs) enc dec xenc xdec,
     aead_props enc dec /\ xaead_props xenc xdec /\
     piece_ok aead_units3 aead_imports3 G /\ map fst G = aead_idents3 /\
     asm_covers G (aead_iface3 enc dec xenc xdec) /\
     asm_covers G [@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS dec;
                   @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xdec] /\
     Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G) ->
  (exists (G: funspecs) x,
     x25519_props x /\ hhs3_comm x /\ piece_ok x25519_units3 x25519_imports3 G /\ map fst G = x25519_idents3 /\
     asm_covers G (x25519_iface3 x) /\
     Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G) ->
  harness_safe WgNoise.contracts.x_handshake.whole_prog.
Proof.
  intros (Gb & HpB & HidB & HcovB) (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA)
         (Gx & x & Hxp & Hcomm & HpX & HidX & HcovX & HccX).
  exact (hhs3a_safe Gb Ga Gx x enc dec xenc xdec HpB HidB HcovB Hap Hxap HpA HidA HcovA HcovD Hxp HpX HidX HcovX
           HccA HccX Hcomm hhs3_rep_ok).
Qed.
