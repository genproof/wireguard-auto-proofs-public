(* create_initiation, stage A (ci_B1): `if (!handshake->static_identity->has_identity) break;` *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.protocol4.prot4_ci_defs.

Section CI.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Lemma prot4_ci_sA:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms me mes met hst he hh hc kv tv S w T (Qc: environ -> mpred) (R: ret_assert),
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  (has = false ->
   ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
     True ret mt ms me mes met hst he hh hc kv tv S w T |-- RA_normal R) ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes met hst he hh hc kv tv S w T)
    ci_B1
    (overridePost
      (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         (has = true) ret mt ms me mes met hst he hh hc kv tv S w T)
      (loop1_ret_assert Qc R)).
Proof.
intros until R. intros SHm SHp SHd SHt HF.
unfold ci_Delta. simplify_func_tycontext. unfold ci_A, ci_B1. abbreviate_semax.
destruct R as [Rn Rb Rc Rr]; simpl RA_normal in HF.
forward. forward. { entailer!. destruct has; simpl; auto. }
forward_if.
{ forward. destruct has; [discriminate|]. eapply derives_trans; [|apply HF; reflexivity]. unfold ci_A. entailer!. }
{ forward. destruct has; [|discriminate]. entailer!. }
Qed.
End CI.
