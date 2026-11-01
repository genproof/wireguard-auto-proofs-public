(* the tactics of the common.h pieces' assembly (hc4a_<law>.v), as
   hc_bodies3.v's: cspecs_sub of a small compspecs, the callee context against the law's (hc3_Gsub, with the
   cross-compspecs lemmas of hc3_xcs.v), the globals (hc3_Vsub), one entry = hc3_lift of a body lemma. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.common.hc3_xcs.

Ltac hc4a_cssub :=
  split3; intros ?i; apply sub_option_get; apply Forall_forall; intros ?x ?Hx; vm_compute in Hx;
  repeat destruct Hx as [<-|Hx]; try contradiction; vm_compute; reflexivity.

Ltac hc4a_gsub :=
  unfold hc3_Gsub;
  repeat (apply Forall_cons;
          [eexists; split;
           [reflexivity
           | first [ apply funspec_sub_refl | apply hc3_curve25519_generic_xcs | apply hc3_chacha_enc_xcs
                   | apply hc3_chacha_dec3_xcs | apply hc3_nondet_bytes_xcs ] ] | ]);
  apply Forall_nil.

Ltac hc4a_vsub := unfold hc3_Vsub; repeat (apply Forall_cons; [split; reflexivity | ]); apply Forall_nil.

Ltac hc4a_entry B CSUB :=
  eexists; split; [left; reflexivity | ]; refine (hc3_lift _ _ _ _ _ _ _ B _ _ _ _ _);
  [ reflexivity | exact CSUB | repeat constructor | hc4a_gsub | hc4a_vsub ].
