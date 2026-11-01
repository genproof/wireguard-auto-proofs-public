(* small compspecs for the bodies of the common.h v2 functions, as hc3_cs.v:
   each body is proved ONCE at a compspecs whose composites are in every unit that contains the function
   (cspecs_sub), then lifted with hc3_lift.v.
   CS4: the kernel structs + hs_snap, ck_snap, pr_snap, hnode, kent, dev_snap (in the 9 any-state units);
   CS4s: CS4 + shim_snap (shim_take / shim_same / shim_no_warning: not in keypairs' unit, which has no shim_snap);
   CS4skb: CS4 + the socket buffer structs and skb_snap (skb_take / skb_same). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require WgNoise.harness.x_cookie_mac.code.

Module HC := WgNoise.harness.x_cookie_mac.code.

Definition hc4_names : list ident :=
  hc3_kernel_names ++ [HC._hs_snap; HC._ck_snap; HC._pr_snap; HC._hnode; HC._kent; HC._dev_snap].

Definition hc4_comp : list composite_definition := Eval vm_compute in hc3_filter hc4_names HC.composites.
Definition hc4_prog := Clightdefs.mkprogram hc4_comp [] [] HC._main Logic.I.
Definition CS4 : compspecs := ltac:(make_compspecs hc4_prog).

Definition hc4_comp_s : list composite_definition :=
  Eval vm_compute in hc3_filter (hc4_names ++ [HC._shim_snap]) HC.composites.
Definition hc4_prog_s := Clightdefs.mkprogram hc4_comp_s [] [] HC._main Logic.I.
Definition CS4s : compspecs := ltac:(make_compspecs hc4_prog_s).

Definition hc4_comp_skb : list composite_definition :=
  Eval vm_compute in hc3_filter (hc4_names ++ [HC._in_addr; HC._in6_addr; HC._iphdr; HC._ipv6hdr; HC._udphdr;
                                               HC._sk_buff; HC._skb_snap]) HC.composites.
Definition hc4_prog_skb := Clightdefs.mkprogram hc4_comp_skb [] [] HC._main Logic.I.
Definition CS4skb : compspecs := ltac:(make_compspecs hc4_prog_skb).
