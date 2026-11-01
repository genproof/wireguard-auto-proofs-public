(* Law transport_send_nonce: the world compspecs of transport_send_nonce.whole_prog's
   composite environment, built so that it computes (as make_compspecs does for a unit); the template is law
   counter's counter_world.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.contracts.x_transport_send_nonce.

Definition tsn5_comps : list composite_definition :=
  ltac:(let c := eval vm_compute in
          (map compdef_of_compenv_element
             (sort_rank (Maps.PTree.elements
                (QP.prog_comp_env WgNoise.contracts.x_transport_send_nonce.whole_prog)) []))
        in exact c).

Definition tsn5_cenv : composite_env :=
  ltac:(let c := eval unfold tsn5_comps in tsn5_comps in
        let ce := make_composite_env c in
        match ce with Errors.OK ?e => exact e end).

#[export] Instance W_tsn5 : compspecs. make_compspecs_cenv tsn5_cenv. Defined.
