(* law handshake_clear, phase P6: statement 17,
   if (target->snap.hashed) CHECK(h->entry.next == NULL); else CHECK(h->entry.next == target->snap.next). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_lem.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_defs.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

Section S17.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p6_seg17 {Espec: OracleKind} gv L KE x p P T nx D others WN FRM Rp :
  In (hs_addr p) (saddrs (t_D T)) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  semax (hcl5_Delta x25519) (hcl5_p6_Q gv L KE x p P T nx D others WN FRM) hcl5_p6_s17
    (overridePost (hcl5_p6_Q gv L KE x p P T nx D others WN FRM) Rp).
Proof.
  intros Hin Hsh. destruct Rp as [Rn Rb Rc Rr].
  unfold hcl5_Delta. simplify_func_tycontext. unfold hcl5_p6_s17, hcl5_p6_Q. abbreviate_semax.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as FC.
  { sep_apply (hcl5_p6_peer_fc Ews p (p_set_hs P (hs_zero (p_hs P)))). entailer!. }
  assert_PROP (field_compatible t_hnode4 [] x) as FCx by entailer!.
  assert (FCs: field_compatible t_hnode4 [StructField HC._snap] x) by auto with field_compatible.
  (* t'34 = target->snap.hashed *)
  sep_apply (hcl5_p6_node_snap Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros. rewrite hcl5_p6_HW.
  assert_PROP (offset_val 16 (offset_val 8 x) =
               field_address t_hsnap [StructField HCL5._hashed] (field_address t_hnode4 [StructField HC._snap] x)).
  { entailer!. rewrite field_address_offset by auto with field_compatible. rewrite field_address_offset by auto.
    rewrite offset_offset_val. reflexivity. }
  forward.
  { entailer!. destruct (vin (hs_addr p) (t_L T)); simpl; auto. }
  match goal with |- context [temp HCL5._t'34 ?v] => change v with (Val.of_bool (vin (hs_addr p) (t_L T))) end.
  rewrite <- hcl5_p6_HW.
  sep_apply (hcl5_p6_mp (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T p P))
                           (field_address t_hnode4 [StructField HC._snap] x))).
  destruct (vin (hs_addr p) (t_L T)) eqn:Hv.
  - forward_if.
    2: { exfalso. inv H0. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { pose proof (hcl5_p6_itab_open Tsh (l_it L) T p FC Hin Hsh) as A; unfold hcl5_p6_acc in A; sep_apply A; clear A.
      Intros. forward.
      match goal with |- context [temp HCL5._t'37 ?v] => change v with nullval end.
      sep_apply (hcl5_p6_mp (@field_at W Ews t_hs [StructField HCL5._entry]
                               (entry_val (t_entry_d T (hs_addr p)) nullval false) (hs_addr p))).
      forward_if.
      { exfalso. rewrite Int64.eq_true in *. apply Int.one_not_zero. assumption. }
      forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    unfold POSTCONDITION, abbreviate. simpl RA_normal. unfold hcl5_p6_Q. entailer!.
  - forward_if.
    { exfalso. inv H0. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { pose proof (hcl5_p6_itab_open Tsh (l_it L) T p FC Hin Hsh) as A; unfold hcl5_p6_acc in A; sep_apply A; clear A.
      Intros. forward.
      match goal with |- context [temp HCL5._t'35 ?v] => change v with nullval end.
      sep_apply (hcl5_p6_mp (@field_at W Ews t_hs [StructField HCL5._entry]
                               (entry_val (t_entry_d T (hs_addr p)) nullval false) (hs_addr p))).
      sep_apply (hcl5_p6_node_snap Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros. rewrite hcl5_p6_HW.
      assert_PROP (offset_val 8 (offset_val 8 x) =
                   field_address t_hsnap [StructField HCL5._next] (field_address t_hnode4 [StructField HC._snap] x)).
      { entailer!. rewrite field_address_offset by auto with field_compatible. rewrite field_address_offset by auto.
        rewrite offset_offset_val. reflexivity. }
      assert (Hnx: succ_in (t_L T) (hs_addr p) = nullval) by exact (hcl5_p6_succ_notin _ _ (hcl5_p6_vin_true _ _ Hv)).
      forward.
      { entailer!. unfold hs_snap_cur, snap_of, hsnap_val; cbn [sn_next]. rewrite Hnx. auto. }
      match goal with |- context [temp HCL5._t'36 ?v] => change v with (succ_in (t_L T) (hs_addr p)) end.
      rewrite Hnx.
      rewrite <- hcl5_p6_HW.
      sep_apply (hcl5_p6_mp (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T p P))
                               (field_address t_hnode4 [StructField HC._snap] x))).
      forward_if.
      { exfalso. rewrite Int64.eq_true in *. apply Int.one_not_zero. assumption. }
      forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    unfold POSTCONDITION, abbreviate. simpl RA_normal. unfold hcl5_p6_Q. entailer!.
Qed.

End S17.
