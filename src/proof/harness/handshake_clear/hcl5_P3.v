(* law handshake_clear: main's phase P3, statement 6: if (peers == NULL) return 0 (the return: hcl5_closeH, the stack frame back as data_at_ W).
   (states: hcl5_defs.v). *)
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
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

(* the stack frame of a return: the locals back to data_at_ at the world *)
Lemma hcl5_p3_hbytes32 bs p : Zlength bs = 32 ->
  hbytes Tsh bs p |-- @data_at_ W_handshake_clear Tsh (tarray tuchar 32) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hcl5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hcl5_p3_ptable p head : ptable Tsh p head |-- @data_at_ W_handshake_clear Tsh t_ptab p.
Proof. unfold ptable. rewrite <- hcl5_conv_ptab. apply data_at_data_at_. Qed.

(* the node list: its head is a valid pointer, NULL iff the list is empty *)
Lemma hcl5_p3_vp l NS : hnodes_rep4 W_handshake_clear l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hcl5_p3_pn l NS : hnodes_rep4 W_handshake_clear l NS |-- !! (is_pointer_or_null l /\ (l = nullval <-> NS = [])).
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!. tauto.
  - Intros nx. subst. entailer!. destruct H0 as [Hp _]. destruct (hn_addr N); simpl in *; try contradiction.
    split; auto. split; intros; discriminate.
Qed.

#[local] Hint Resolve hcl5_p3_vp : valid_pointer.

Section P3.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_P3_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 -> hcl5_closeH ->
  semax (hcl5_Delta x25519) (hcl5_SA x25519 gv L FR) hcl5_P3
    (overridePost (hcl5_SB x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH HC. unfold hcl5_SA, hcl5_Delta, hcl5_R, hcl5_P3. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head.
  unfold hcl5_lvars, hcl5_scr, hcl5_world, hcl5_globs, hcl5_snaps0; cbn [app].
  assert_PROP (is_pointer_or_null (hcl5_head NS) /\ (hcl5_head NS = nullval <-> NS = [])) as Hpp.
  { sep_apply (hcl5_p3_pn (hcl5_head NS) NS). entailer!. }
  destruct Hpp as [Hpn Hnl].
  forward.
  forward_if.
  - (* return *)
    assert (HN: NS = []) by (apply Hnl; assumption). subst NS.
    destruct H0 as (Hok & Hwf & Hch & Hnp & HT & Hsl).
    destruct PS as [| x PS']; [| unfold hnodes_peers4 in Hnp; discriminate].
    destruct HT as (HT1 & HT2 & _ & _).
    destruct HC as [HCd HCp].
    sep_apply (HCp (l_it L) T [] [] [] [] HT1 HT2 eq_refl).
    { constructor. }
    simpl hnodes_rep4. simpl iter_sepcon. Intros.
    sep_apply (HCd Tsh (l_w L) (hcl5_D x25519 R L)).
    apply hcl5_post_canon.
    forward.
    destruct H as (Hra & _).
    rewrite hcl5_conv_dev, hcl5_conv_itab, hcl5_conv_devsnap, hcl5_conv_shimsnap, !hcl5_conv_bytes.
    sep_apply (hcl5_p3_hbytes32 (r_raw R) (l_raw L) Hra).
    sep_apply (hcl5_p3_ptable (l_pt L) head).
    sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hcl5_head []) (l_peers L)).
    simpl. cancel.
  - forward. unfold hcl5_SB. Exists R S w NS PS T head.
    unfold hcl5_lvars, hcl5_scr, hcl5_world, hcl5_globs, hcl5_snaps0; cbn [app].
    entailer!.
Qed.

End P3.
