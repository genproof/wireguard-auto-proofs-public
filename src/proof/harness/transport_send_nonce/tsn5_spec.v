(* Law transport_send_nonce: the harness piece's interface (harness/transport_send_nonce.c),
   in the world compspecs W_tsn5 (tsn5_world.v).  The harness calls no function of the code under test: its
   imports are the external world QuickProof.Env only. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_world.
Require WgNoise.contracts.x_transport_send_nonce.
Require WgNoise.harness.x_transport_send_nonce.code.

Definition u_tsn5 : unit_ctx :=
  mk_unit W_tsn5 (QPvarspecs WgNoise.contracts.x_transport_send_nonce.Harness.qp)
    WgNoise.harness.x_transport_send_nonce.code.prog.

Definition tsn5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition tsn5_main_spec : ident * funspec :=
  (WgNoise.harness.x_transport_send_nonce.code._main,
   QPmain_spec_ext' WgNoise.contracts.x_transport_send_nonce.whole_prog tt tsn5_post).

Definition tsn5_draw_steps_spec :=
  DECLARE WgNoise.harness.x_transport_send_nonce.code._draw_steps
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

Definition tsn5_draw_u64_spec :=
  DECLARE WgNoise.harness.x_transport_send_nonce.code._draw_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

Definition tsn5_imports (cs: compspecs) : funspecs := @asm_env.env_specs W_tsn5.

Definition tsn5_G : funspecs := [tsn5_draw_steps_spec; tsn5_draw_u64_spec; tsn5_main_spec].
