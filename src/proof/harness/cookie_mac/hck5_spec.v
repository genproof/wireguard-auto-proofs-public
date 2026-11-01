(* law cookie_mac: the law's own functions
   m_cookie, m_expired, main: their specifications.  Port of the proof's
   hck3_spec.v: the same C functions m_cookie / m_expired (same specifications), main's specification from the v2
   whole program; the imports are common4's (hc4_imports: environment with nondet_size, lower pieces, protocol4's
   prot_G4) and the unit's common.h functions (hc4_G_cookie_mac). *)
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
Require WgNoise.contracts.x_cookie_mac.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types) *)
Definition hck5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_cookie_mac.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hck5 : unit_ctx := mk_unit W_cookie_mac hck5_V HK.prog.

Definition hck5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hck5_main_spec : ident * funspec :=
  (HK._main, QPmain_spec_ext' WgNoise.contracts.x_cookie_mac.whole_prog tt hck5_post).

Section LocalSpecs.
#[local] Existing Instance W_cookie_mac.

(* m_expired(birthdate, seconds, now) = wg_birthdate_has_expired as the model states it *)
Definition hck5_m_expired_spec : ident * funspec :=
  DECLARE HK._m_expired
  WITH b: int64, s: int64, n: int64
  PRE [ tulong, tulong, tulong ]
    PROP () PARAMS (Vlong b; Vlong s; Vlong n) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (if birthdate_expired b s n then Int.one else Int.zero)) SEP ().

(* m_cookie(out, secret, skb): B's cookie for the packet's source with the secret SECRET *)
Definition hck5_m_cookie_spec : ident * funspec :=
  DECLARE HK._m_cookie
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

Definition hck5_imports (cs: compspecs) : funspecs :=
  hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_cookie_mac cs ++
  hc4_G_cookie_mac x25519 aead_enc aead_dec W_cookie_mac.

End Piece.

Definition hck5_G : funspecs := [hck5_m_cookie_spec; hck5_m_expired_spec; hck5_main_spec].
