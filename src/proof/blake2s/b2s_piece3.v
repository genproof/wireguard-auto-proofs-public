(* the BLAKE2s piece for the new interface (wg3_iface.blake2s3_ok, b2s_spec3.v): every body proved
   against b2s_prog3's contexts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.proof.blake2s.b2s_small_body3 WgNoise.proof.blake2s.b2s_compress_body3
        WgNoise.proof.blake2s.b2s_update_body3 WgNoise.proof.blake2s.b2s_final_body3
        WgNoise.proof.blake2s.b2s_inline_body3.

Local Ltac b2s_body3 := first
  [ assumption
  | exact b2s_compress_body3.body_blake2s_compress_generic
  | exact b2s_update_body3.body_blake2s_update3
  | exact b2s_final_body3.body_blake2s_final ].

Theorem blake2s_piece3 : piece_ok [u_blake2s; u_cookie] blake2s_imports3 blake2s_G3.
Proof.
  destruct b2s_small_body3.b2s_small_bodies as [Hror [Hinc [Hlast [Hle32 Hmz]]]].
  destruct b2s_inline_body3.b2s_inline_bodies as [Hinit0 [Hinit [Hinitk Hb2s]]].
  split; [repeat constructor; simpl; intuition discriminate |].
  change (blake2s_imports3 Blake2s.CS ++ blake2s_G3) with b2s_Gprog3 in *.
  change (blake2s_imports3 Cookie.CS ++ blake2s_G3) with b2s_Gprog3_cookie in *.
  repeat constructor.
  all: first [ exists u_blake2s; split; [simpl; auto |]; eexists; split; [reflexivity |]; b2s_body3
             | exists u_cookie; split; [simpl; auto |]; eexists; split; [reflexivity |]; b2s_body3 ].
Qed.

Lemma asm_covers_refl (G: funspecs) : list_norepet (map fst G) -> asm_covers G G.
Proof.
  intros H. unfold asm_covers. apply Forall_forall. intros [i s] Hin. exists s. split.
  - apply initial_world.find_id_i; auto.
  - apply funspec_sub_refl.
Qed.

Theorem blake2s3_ok_proof : blake2s3_ok.
Proof.
  exists blake2s_G3. split; [exact blake2s_piece3 | split; [reflexivity |]].
  apply asm_covers_refl. apply (proj1 blake2s_piece3).
Qed.
