(* law keypairs: the specification hk5_zf_spec of common.h's hs_zeroed_from, with a WEAKER
   precondition than the shared hs_zeroed_from_spec (hc_specs3.v): hk5_cmp_pre drops the snapshot's `next` condition
   (sn_next sn = nullval or in the pool).  hs_zeroed_from does not read the snapshot's next field, and in law keypairs
   the condition fails: after begin_session (responder) the snapshot's next entry may be a keypair that
   add_new_keypair has just freed.  Body: hkp5_zf.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require WgNoise.harness.x_handshake.code.

Module FH := WgNoise.harness.x_handshake.code.

(* the comparisons' pointers: the snapshot is of the same peer's handshake (same peer, same static identity at wg);
   nothing about its next field *)
Definition hk5_cmp_pre (sn: hsnap) (T: tstate) (p wg: val) (P: peer) (E: entry) : Prop :=
  t_entry T (hs_addr p) = Some E /\ e_peer E = p /\ e_peer (sn_entry sn) = p /\
  hs_sid (sn_hs sn) = id_addr wg /\ hs_sid (p_hs P) = id_addr wg.

Lemma hk5_cmp_pre_weaker sn T p wg P E : hs_cmp_pre sn T p wg P E -> hk5_cmp_pre sn T p wg P E.
Proof. unfold hs_cmp_pre, hk5_cmp_pre. tauto. Qed.

Section Spec4.
#[local] Existing Instance HCS.
Definition hk5_zf_spec :=
  DECLARE FH._hs_zeroed_from
  WITH shs: share, s: val, sn: hsnap, shp: share, p: val, P: peer, sht: share, tab: val, T: tstate,
       E: entry, shd: share, wg: val, D: device
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (readable_share shs; readable_share shp; readable_share sht; readable_share shd;
          hk5_cmp_pre sn T p wg P E)
    PARAMS (s; hs_addr p)
    SEP (data_at shs t_hsnap (hsnap_val sn) s; peer_rep shp p P; itable sht tab T; device_rep shd wg D)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if zeroed_from sn (snap_of T (hs_addr p) E (p_hs P)) then Int.one else Int.zero))
    SEP (data_at shs t_hsnap (hsnap_val sn) s; peer_rep shp p P; itable sht tab T; device_rep shd wg D).
End Spec4.

