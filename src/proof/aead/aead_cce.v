(* change_composite_env instances between the units of the AEAD piece (for change_compspecs around calls
   whose specification is stated in another unit's compspecs: struct chacha_state, the poly1305 structs). *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.

#[export] Instance cce_c20p_chacha : change_composite_env Chacha20poly1305.CS Chacha.CS.
Proof. make_cs_preserve Chacha20poly1305.CS Chacha.CS. Defined.
#[export] Instance cce_chacha_c20p : change_composite_env Chacha.CS Chacha20poly1305.CS.
Proof. make_cs_preserve Chacha.CS Chacha20poly1305.CS. Defined.
#[export] Instance cce_c20p_block : change_composite_env Chacha20poly1305.CS ChachaBlock.CS.
Proof. make_cs_preserve Chacha20poly1305.CS ChachaBlock.CS. Defined.
#[export] Instance cce_block_c20p : change_composite_env ChachaBlock.CS Chacha20poly1305.CS.
Proof. make_cs_preserve ChachaBlock.CS Chacha20poly1305.CS. Defined.
#[export] Instance cce_chacha_block : change_composite_env Chacha.CS ChachaBlock.CS.
Proof. make_cs_preserve Chacha.CS ChachaBlock.CS. Defined.
#[export] Instance cce_block_chacha : change_composite_env ChachaBlock.CS Chacha.CS.
Proof. make_cs_preserve ChachaBlock.CS Chacha.CS. Defined.
#[export] Instance cce_c20p_poly : change_composite_env Chacha20poly1305.CS Poly1305.CS.
Proof. make_cs_preserve Chacha20poly1305.CS Poly1305.CS. Defined.
#[export] Instance cce_poly_c20p : change_composite_env Poly1305.CS Chacha20poly1305.CS.
Proof. make_cs_preserve Poly1305.CS Chacha20poly1305.CS. Defined.
#[export] Instance cce_poly_donna : change_composite_env Poly1305.CS Poly1305Donna32.CS.
Proof. make_cs_preserve Poly1305.CS Poly1305Donna32.CS. Defined.
#[export] Instance cce_donna_poly : change_composite_env Poly1305Donna32.CS Poly1305.CS.
Proof. make_cs_preserve Poly1305Donna32.CS Poly1305.CS. Defined.
