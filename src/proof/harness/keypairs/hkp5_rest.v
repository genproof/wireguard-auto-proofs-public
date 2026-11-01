(* law keypairs: the specification of keypairs.c's rest_same.
   rest_same(&prm, p) compares the rest of P (device, dead flag, last sent handshake,
   cookie state via ck_same, internal id, public-key table link; not the keypair slots) with the snapshot prm.
   Used by check_all only, with prm = hk5_prsnap_val P (the loop invariant): it returns 1. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Export WgNoise.proof.harness.keypairs.hkp5_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Definition hk5_rest_same_spec :=
  DECLARE KC._rest_same
  WITH shs: share, s: val, shp: share, p: val, P: peer, shd: share, wg: val, D: device
  PRE [ tptr (Tstruct KC._pr_snap noattr), tptr (Tstruct KC._wg_peer noattr) ]
    PROP (readable_share shs; readable_share shp; readable_share shd; p_device P = wg; p_pknext P = nullval)
    PARAMS (s; p)
    SEP (data_at shs (Tstruct KC._pr_snap noattr) (hk5_prsnap_val P) s; peer_rep shp p P; device_rep shd wg D)
  POST [ tint ]
    PROP () RETURN (Vint Int.one)
    SEP (data_at shs (Tstruct KC._pr_snap noattr) (hk5_prsnap_val P) s; peer_rep shp p P; device_rep shd wg D).

Definition hk5_G_rest_same : funspecs := [ck_same_spec].
