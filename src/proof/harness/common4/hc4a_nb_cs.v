(* small compspecs WITHOUT struct blake2s_ctx, for the unit of law handshake_clear
   (handshake_clear.c never hashes: clightgen dropped blake2s_ctx from its composites, so no compspecs of hc3_cs.v /
   hc4_cs.v is a sub-compspecs of it).  Same names as hc3_cs.v / hc4_cs.v minus blake2s_ctx. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_cookie_mac.code.

Module NH := WgNoise.harness.x_handshake.code.
Module NK := WgNoise.harness.x_cookie_reply.code.
Module NC := WgNoise.harness.x_cookie_mac.code.

Definition hc4nb_kernel_names : list ident :=
  filter (fun i => negb (Pos.eqb i NH._blake2s_ctx)) hc3_kernel_names.

Definition hc4nb_comp_k : list composite_definition :=
  Eval vm_compute in hc3_filter hc4nb_kernel_names NH.composites.
Definition hc4nb_prog_k := Clightdefs.mkprogram hc4nb_comp_k [] [] NH._main Logic.I.
Definition CSknb : compspecs := ltac:(make_compspecs hc4nb_prog_k).

Definition hc4nb_comp_kh : list composite_definition :=
  Eval vm_compute in hc3_filter (hc4nb_kernel_names ++ [NH._hs_snap]) NH.composites.
Definition hc4nb_prog_kh := Clightdefs.mkprogram hc4nb_comp_kh [] [] NH._main Logic.I.
Definition CSkhnb : compspecs := ltac:(make_compspecs hc4nb_prog_kh).

Definition hc4nb_comp_kck : list composite_definition :=
  Eval vm_compute in hc3_filter (hc4nb_kernel_names ++ [NK._ck_snap]) NK.composites.
Definition hc4nb_prog_kck := Clightdefs.mkprogram hc4nb_comp_kck [] [] NH._main Logic.I.
Definition CSkcknb : compspecs := ltac:(make_compspecs hc4nb_prog_kck).

Definition hc4nb_names : list ident :=
  hc4nb_kernel_names ++ [NC._hs_snap; NC._ck_snap; NC._pr_snap; NC._hnode; NC._kent; NC._dev_snap].
Definition hc4nb_comp : list composite_definition := Eval vm_compute in hc3_filter hc4nb_names NC.composites.
Definition hc4nb_prog := Clightdefs.mkprogram hc4nb_comp [] [] NC._main Logic.I.
Definition CS4nb : compspecs := ltac:(make_compspecs hc4nb_prog).

Definition hc4nb_comp_s : list composite_definition :=
  Eval vm_compute in hc3_filter (hc4nb_names ++ [NC._shim_snap]) NC.composites.
Definition hc4nb_prog_s := Clightdefs.mkprogram hc4nb_comp_s [] [] NC._main Logic.I.
Definition CS4snb : compspecs := ltac:(make_compspecs hc4nb_prog_s).
