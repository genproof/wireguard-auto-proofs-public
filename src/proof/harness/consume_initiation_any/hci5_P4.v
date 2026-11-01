(* law consume_initiation_any: main's phase P4, statements 13..14: msg = malloc(sizeof( *msg)); if (msg == NULL) { kents_free(kes); hnodes_free(peers); return 0; }.
   (states: hci5_defs.v).
   harness/consume_initiation_any/hci3_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* the stack frame of a return: the locals back to data_at_ at the world *)
Lemma hci5_p4_hbytes32 bs p : Zlength bs = 32 ->
  hbytes Tsh bs p |-- @data_at_ W_consume_initiation_any Tsh (tarray tuchar 32) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hci5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hci5_p4_ptable p head : ptable Tsh p head |-- @data_at_ W_consume_initiation_any Tsh t_ptab p.
Proof. unfold ptable. rewrite <- hci5_conv_ptab. apply data_at_data_at_. Qed.

Lemma hci5_p4_mident v p : @data_at HCS Tsh t_mident v p |-- @data_at_ W_consume_initiation_any Tsh t_mident p.
Proof. rewrite <- hci5_conv_mident. apply data_at_data_at_. Qed.

Section P4.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_P4_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hci5_closeH ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_SK x25519 gv L FR) hci5_P4
    (overridePost (hci5_S4 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH HC. unfold hci5_SK, hci5_Delta, hci5_R, hci5_P4. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE.
  unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
  forward_call (t_init, gv).
  Intros m.
  destruct (eq_dec m nullval) as [Hm | Hm].
  - subst m. forward_if.
    + assert_PROP (is_pointer_or_null (hci5_khead KE)) as Hkh.
      { destruct KE as [|e KE']; [entailer! |]. unfold kents_rep; fold (kents_rep W). Intros nx.
        unfold kent_cell. Intros. entailer!. }
      assert_PROP (is_pointer_or_null (hci5_head NS)) as Hhd.
      { destruct NS as [|N NS']; [entailer! |]. unfold hnodes_rep4; fold (hnodes_rep4 W). Intros nx. entailer!.
        match goal with Hf: field_compatible t_hnode4 [] _ |- _ => destruct Hf as [? _] end.
        apply isptr_is_pointer_or_null; assumption. }
      destruct HC as [HCd HCp].
      destruct H0 as (Hok & Hwf & Hch & Hnp & Hna & HT & Hsl). destruct HT as (HT1 & HT2 & _ & _).
      (* the index table dissolved: its pool back to the peers' structs and the kents' entries *)
      sep_apply (HCp (l_itb L) T PS PS KE NS HT1 HT2 eq_refl).
      { eapply Forall_impl; [| exact Hok]. intros [[a sh] P] Hp. apply Hp. }
      Intros.
      forward_call (gv, hci5_khead KE, KE).
      forward.
      forward_call (gv, hci5_head NS, NS).
      apply hci5_post_canon.
      sep_apply (HCd Tsh (l_wb L) (hci5_DB x25519 R L)).
      forward.
      destruct H as (Hra & Hrb & _).
      rewrite hci5_conv_dev, hci5_conv_itab, hci5_conv_mcinit, hci5_conv_minit, hci5_conv_devsnap,
        hci5_conv_shimsnap, !hci5_conv_bytes.
      sep_apply (hci5_p4_hbytes32 (r_rawa R) (l_rawa L) Hra).
      sep_apply (hci5_p4_hbytes32 (r_rawb R) (l_rawb L) Hrb).
      sep_apply (hci5_p4_ptable (l_ptb L) head).
      sep_apply (hci5_p4_mident (mident_val (hci5_IA x25519 R)) (l_ia L)).
      sep_apply (hci5_p4_mident (mident_val (hci5_IB x25519 R)) (l_ib L)).
      sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hci5_head NS) (l_peers L)).
      cancel.
    + exfalso; apply H1; reflexivity.
  - Intros. forward_if.
    + subst m; contradiction.
    + forward. unfold hci5_S4. Exists R S w NS PS T head na KE m.
      unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0, hci5_tok; cbn [app].
      rewrite <- hci5_conv_init. entailer!.
Qed.

End P4.
