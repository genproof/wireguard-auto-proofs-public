(* The field decomposition of struct poly1305_desc_ctx with a concrete value (for aead_poly_small_body.v).
   Its kernel check is slow (the reptype casts of unfold_data_at on the 112-byte context): kept in its own file. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code.
Require Import WgNoise.proof.aead.aead_spec.

Local Open Scope Z_scope.

Section PolySmallCtx.
#[local] Existing Instance Poly1305.CS.

Lemma aead_ps_ctx_split sh buf buflen s h r desc :
  data_at sh t_p1305_ctx (p1305_ctx_val buf buflen s h r) desc =
  (field_at sh t_p1305_ctx (DOT poly1305.code._buf) buf desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen) (Vint (Int.repr buflen)) desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._s) (map Vint s) desc *
   spacer sh 36 40 desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h r) desc)%logic.
Proof.
  unfold_data_at (data_at _ _ _ desc).
  rewrite !sepcon_assoc. reflexivity.
Qed.

End PolySmallCtx.
