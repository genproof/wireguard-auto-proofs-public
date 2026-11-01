(* law handshake_clear, phase P6: statement 16,
   CHECK(hs_zeroed_from(&target->snap, h) && !h->entry.hashed && h->entry.index == target->snap.index). *)
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

Section S16.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p6_seg16 {Espec: OracleKind} gv L KE x p P T nx D others WN FRM Rp :
  In (hs_addr p) (saddrs (t_D T)) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  e_peer (t_entry_d T (hs_addr p)) = p ->
  hs_sid (p_hs P) = id_addr (l_w L) ->
  semax (hcl5_Delta x25519) (hcl5_p6_Q gv L KE x p P T nx D others WN FRM) hcl5_p6_s16
    (overridePost (hcl5_p6_Q gv L KE x p P T nx D others WN FRM) Rp).
Proof.
  intros Hin Hsh Hep Hsid. destruct Rp as [Rn Rb Rc Rr].
  unfold hcl5_Delta. simplify_func_tycontext. unfold hcl5_p6_s16. abbreviate_semax.
  unfold hcl5_p6_Q.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as FC.
  { sep_apply (hcl5_p6_peer_fc Ews p (p_set_hs P (hs_zero (p_hs P)))). entailer!. }
  assert_PROP (field_compatible t_hnode4 [] x) as FCx by entailer!.
  assert (FCs: field_compatible t_hnode4 [StructField HC._snap] x) by auto with field_compatible.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hcl5_p6_node_snap Ews p (hs_snap_cur T p P) (p_refs P) P nx x).
    rewrite hcl5_p6_HW.
    rewrite <- (hcl5_p6_vo1 Tsh (l_w L) D).
    change (peer_rep Ews p (p_set_hs P (hs_zero (p_hs P)))) with (hs_mem true Ews p (p_set_hs P (hs_zero (p_hs P)))).
    forward_call (Ews, field_address t_hnode4 [StructField HC._snap] x, hs_snap_cur T p P, Ews, p,
                  p_set_hs P (hs_zero (p_hs P)), true, Tsh, l_it L, t_remove T (hs_addr p), [VDev Tsh (l_w L) D]).
    { cancel. }
    { split; [constructor; [simpl; auto | constructor]|].
      unfold hs_ptrs_nn, hs_snap_cur, snap_of; cbn [sn_entry sn_hs].
      change (t_entry_d (t_remove T (hs_addr p)) (hs_addr p)) with (t_entry_d T (hs_addr p)).
      rewrite Hep. cbn [hs_zero hs_sid p_set_hs p_hs]. rewrite Hsid. unfold hs_own, vp_ok.
      apply Forall_forall; intros y Hy; right; simpl in Hy |- *.
      destruct Hy as [<-|[<-|[<-|[<-|[]]]]]; auto 10.
      all: right; apply in_app_iff; right; simpl; auto. }
    rewrite hcl5_p6_zf.
    rewrite <- hcl5_p6_HW.
    sep_apply (hcl5_p6_mp (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T p P))
                             (field_address t_hnode4 [StructField HC._snap] x))).
    rewrite hcl5_p6_vo1. unfold hs_mem.
    forward_if (temp HCL5._t'7 (Vint Int.one)).
    { pose proof (hcl5_p6_itab_open Tsh (l_it L) T p FC Hin Hsh) as A; unfold hcl5_p6_acc in A; sep_apply A; clear A.
      Intros. forward. forward.
      sep_apply (hcl5_p6_mp (@field_at W Ews t_hs [StructField HCL5._entry]
                               (entry_val (t_entry_d T (hs_addr p)) nullval false) (hs_addr p))).
      entailer!. }
    { exfalso; apply Int.one_not_zero; assumption. }
    forward_if (temp HCL5._t'8 (Vint Int.one)).
    { pose proof (hcl5_p6_itab_open Tsh (l_it L) T p FC Hin Hsh) as A; unfold hcl5_p6_acc in A; sep_apply A; clear A.
      Intros. forward.
      sep_apply (hcl5_p6_node_snap Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros. rewrite hcl5_p6_HW.
      assert_PROP (offset_val 24 (offset_val 8 x) =
                   field_address t_hsnap [StructField HCL5._index] (field_address t_hnode4 [StructField HC._snap] x)).
      { entailer!. rewrite field_address_offset by auto with field_compatible. rewrite field_address_offset by auto.
        rewrite offset_offset_val. reflexivity. }
      forward.
      match goal with |- context [temp HCL5._t'38 ?v] => change v with (Vint (e_index (t_entry_d T (hs_addr p)))) end.
      match goal with |- context [temp HCL5._t'39 ?v] => change v with (Vint (e_index (t_entry_d T (hs_addr p)))) end.
      forward.
      rewrite <- hcl5_p6_HW.
      sep_apply (hcl5_p6_mp (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T p P))
                               (field_address t_hnode4 [StructField HC._snap] x))).
      sep_apply (hcl5_p6_mp (@field_at W Ews t_hs [StructField HCL5._entry]
                               (entry_val (t_entry_d T (hs_addr p)) nullval false) (hs_addr p))).
      entailer!. rewrite Int.eq_true. reflexivity. }
    { exfalso; apply Int.one_not_zero; assumption. }
    forward_if.
    { exfalso; apply Int.one_not_zero; assumption. }
    forward. entailer!.
  }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.

End S16.
