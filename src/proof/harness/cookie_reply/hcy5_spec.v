(* law cookie_reply: the law's own
   functions m_expired, m_cookie, main: their specifications.  Port of the proof's hcy4_spec.v: the same C functions m_expired / m_cookie, main's
   specification from the v2 whole program.  The imports (protocol4 + common4 layers) are NOT here: every phase
   of main is proved in its own small context (hcy5_defs.v, hcy5_Delta G) and lifted. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require WgNoise.contracts.x_cookie_reply.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types) *)
Definition hcy5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_cookie_reply.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hcy5 : unit_ctx := mk_unit W_cookie_reply hcy5_V HY.prog.

Definition hcy5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hcy5_main_spec : ident * funspec :=
  (HY._main, QPmain_spec_ext' WgNoise.contracts.x_cookie_reply.whole_prog tt hcy5_post).

Section LocalSpecs.
#[local] Existing Instance W_cookie_reply.

(* m_expired(birthdate, seconds, now) = wg_birthdate_has_expired as the model states it *)
Definition hcy5_m_expired_spec : ident * funspec :=
  DECLARE HY._m_expired
  WITH b: int64, s: int64, n: int64
  PRE [ tulong, tulong, tulong ]
    PROP () PARAMS (Vlong b; Vlong s; Vlong n) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (if birthdate_expired b s n then Int.one else Int.zero)) SEP ().

(* m_cookie(out, secret, skb): B's cookie for the packet's source with the secret SECRET *)
Definition hcy5_m_cookie_spec : ident * funspec :=
  DECLARE HY._m_cookie
  WITH gv: globals, sho: share, o: val, shk: share, k: val, SECRET: list byte, shs: share, sp: val, s: skb
  PRE [ tptr tuchar, tptr tuchar, tptr t_skb ]
    PROP (writable_share sho; readable_share shk; readable_share shs; Zlength SECRET = 32)
    PARAMS (o; k; sp) GLOBALS (gv)
    SEP (hout sho 16 o; hbytes shk SECRET k; skb_rep shs sp s; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (cookie_of SECRET s) o; hbytes shk SECRET k; skb_rep shs sp s; blake2s_globals gv).

End LocalSpecs.

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hcy5_imports (cs: compspecs) : funspecs :=
  hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_cookie_reply cs ++
  hc4_G_cookie_reply x25519 aead_enc aead_dec W_cookie_reply.

End Piece.

Definition hcy5_G : funspecs := [hcy5_m_expired_spec; hcy5_m_cookie_spec; hcy5_main_spec].
