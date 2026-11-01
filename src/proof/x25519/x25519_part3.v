(* the Curve25519 piece (interface wg3_iface.x25519_ok3): a functional specification (any Coq function of scalar and point, e.g. a transliteration of the fiat32 limb code) and memory safety; NOT the proof that it is X25519. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.

Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.x25519.x25519_spec.
Require WgNoise.proof.x25519.x25519_small3 WgNoise.proof.x25519.x25519_wrap3
        WgNoise.proof.x25519.x25519_mul3 WgNoise.proof.x25519.x25519_sqr3
        WgNoise.proof.x25519.x25519_mul121666_3 WgNoise.proof.x25519.x25519_bytes3
        WgNoise.proof.x25519.x25519_invert3 WgNoise.proof.x25519.x25519_generic3
        WgNoise.proof.x25519.x25519_curve3.

Module BS3 := WgNoise.proof.x25519.x25519_small3.
Module BW3 := WgNoise.proof.x25519.x25519_wrap3.
Module BB3 := WgNoise.proof.x25519.x25519_bytes3.
Module BC3 := WgNoise.proof.x25519.x25519_curve3.

(* one entry of the Forall of piece_ok: the body lemma L proved in unit u *)
Local Ltac x25_entry3 u L :=
  apply Forall_cons; [exists u; split; [simpl; auto 20 |]; eexists; split; [reflexivity | exact L] |].

Lemma x25519_piece3 : piece_ok x25519_units3 x25519_imports3 x25_G.
Proof.
  destruct BS3.x25519_small3 as (Sclamp & Sa25 & Sa26 & Ss25 & Ss26 & Scmov & Scopy & Scopylt & S0 & S1
    & Sadd & Ssub & Scswap).
  destruct BW3.x25519_wrap3 as (Wfrom & Wadd & Wsub & Wttt & Wtlt & Wtll & Wsqtl & Wsqtt & Wm121666 & Winv).
  destruct BB3.x25519_bytes3 as (Bfrom & Bfreeze & Btob).
  destruct BC3.x25519_curve3 as (Carch & Cbase & Ccurve & Cgen).
  split; [repeat constructor; simpl; intuition discriminate |].
  change (x25519_imports3 Curve25519Fiat32.CS ++ x25_G) with x25_Gprog.
  change (x25519_imports3 Curve25519.CS ++ x25_G) with x25_Gprog_c.
  unfold x25_G at 1.
  x25_entry3 u_curve25519_fiat32 Sclamp.
  x25_entry3 u_curve25519_fiat32 Bfrom.
  x25_entry3 u_curve25519_fiat32 Wfrom.
  x25_entry3 u_curve25519_fiat32 Sa25.
  x25_entry3 u_curve25519_fiat32 Sa26.
  x25_entry3 u_curve25519_fiat32 Ss25.
  x25_entry3 u_curve25519_fiat32 Ss26.
  x25_entry3 u_curve25519_fiat32 Scmov.
  x25_entry3 u_curve25519_fiat32 Bfreeze.
  x25_entry3 u_curve25519_fiat32 Btob.
  x25_entry3 u_curve25519_fiat32 Scopy.
  x25_entry3 u_curve25519_fiat32 Scopylt.
  x25_entry3 u_curve25519_fiat32 S0.
  x25_entry3 u_curve25519_fiat32 S1.
  x25_entry3 u_curve25519_fiat32 Sadd.
  x25_entry3 u_curve25519_fiat32 Wadd.
  x25_entry3 u_curve25519_fiat32 Ssub.
  x25_entry3 u_curve25519_fiat32 Wsub.
  x25_entry3 u_curve25519_fiat32 WgNoise.proof.x25519.x25519_mul3.x25519_mul3.
  x25_entry3 u_curve25519_fiat32 Wttt.
  x25_entry3 u_curve25519_fiat32 Wtlt.
  x25_entry3 u_curve25519_fiat32 Wtll.
  x25_entry3 u_curve25519_fiat32 WgNoise.proof.x25519.x25519_sqr3.x25519_sqr3.
  x25_entry3 u_curve25519_fiat32 Wsqtl.
  x25_entry3 u_curve25519_fiat32 Wsqtt.
  x25_entry3 u_curve25519_fiat32 WgNoise.proof.x25519.x25519_invert3.x25519_invert3.
  x25_entry3 u_curve25519_fiat32 Winv.
  x25_entry3 u_curve25519_fiat32 Scswap.
  x25_entry3 u_curve25519_fiat32 WgNoise.proof.x25519.x25519_mul121666_3.x25519_mul121666_3.
  x25_entry3 u_curve25519_fiat32 Wm121666.
  x25_entry3 u_curve25519_fiat32 WgNoise.proof.x25519.x25519_generic3.x25519_generic3.
  x25_entry3 u_curve25519 Carch.
  x25_entry3 u_curve25519 Cbase.
  x25_entry3 u_curve25519 Ccurve.
  x25_entry3 u_curve25519 Cgen.
  constructor.
Qed.

Theorem x25519_part3 :
  x25519_ok3.
Proof.
  exists x25_G, x25519_m.
  split; [exact x25519_m_length |].
  split; [exact x25519_piece3 |].
  split; [reflexivity |].
  apply asm_covers_incl.
  - repeat constructor; simpl; intuition discriminate.
  - unfold x25519_iface3, x25_G. intros a Ha. simpl in Ha |- *. intuition (subst; tauto).
Qed.
