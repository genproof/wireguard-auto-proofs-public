(* segment E of main's loop body (statements 18..20: the three frees), ending the body in hka5_Cont.
   States and segments: hka5_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.
Require Import WgNoise.proof.harness.transport_keepalive.hka5e_lemmas.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Lemma hka5_segE_ok {Espec: OracleKind} gv vrc vwm vsnap vkey key steps FR i top S bm ha ln hdr c pkt po rp :
  semax hka5_Delta (hka5_PE gv vrc vwm vsnap vkey key steps FR i top S bm ha ln hdr c pkt po rp) hka5_segE
    (hka5_LR gv vrc vwm vsnap vkey key steps FR).
Proof.
  unfold hka5_Delta, hka5_PE, hka5_segE, hka5_LR, hka5_pkt, hka5_tl, hka5_lv, hka5_cw, hka5_fr.
  simpl app. abbreviate_semax.
  Intros.
  assert_PROP (malloc_compatible (sizeof (tarray tuchar (16 + Zlength c))) pkt) as Hmc by entailer!.
  assert_PROP (isptr pkt) as Hpk by entailer!.
  pose proof (Zlength_nonneg c) as Hc0.
  assert (Hfc: field_compatible (tarray tuchar (16 + Zlength c)) [] pkt) by (apply hka5e_fc; [lia | exact Hmc]).
  sep_apply (hka5e_pkt_join Ews pkt hdr c H2 Hfc).
  forward_call (tarray tuchar (16 + Zlength c), pkt, gv).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  forward_call (tarray tuchar 0, po, gv).
  { unfold hka5_mb. cancel. }
  forward_call (tarray tuchar 0, rp, gv).
  unfold hka5_Cont, hka5_tl, hka5_lv, hka5_cw, hka5_fr. simpl app.
  Exists i top S bm ha ln. entailer!.
Qed.
