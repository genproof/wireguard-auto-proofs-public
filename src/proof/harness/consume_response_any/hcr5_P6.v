(* law consume_response_any, phase P6: statement 14 of main, if (msg != NULL) { ... },
   from the then-branch's phases Q1a .. Q5 (the port of v1's hcr3_P6.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_Q1a.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_Q1b.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_Q2.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_Q3.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_Q4.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_Q5.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_P6_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_S5 x25519 gv L FR) hcr5_P6
    (overridePost (hcr5_SE x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH.
  rewrite hcr5_P6_eq.
  unfold hcr5_S5. Intros R S NS PS head nb T KE m.
  destruct hcr5_qphases_eq as (E1 & E2 & E3 & E4 & E5 & E6).
  (* the then-branch, from the phases Q1a .. Q5 *)
  assert (HT: semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_S5n x25519 gv L FR)
    (hcr5_seqs (hcr5_tl 0 3) (hcr5_seqs (hcr5_tl 3 1) (hcr5_seqs (hcr5_tl 4 8) (hcr5_seqs (hcr5_tl 12 2)
      (hcr5_seqs (hcr5_tl 14 3) (hcr5_seql (hcr5_tl 17 2)))))))
    (overridePost (hcr5_SE x25519 gv L FR) (hcr5_R gv))).
  { eapply hcr5_semax_cut with (Q := hcr5_SQ1a x25519 gv L FR);
      [discriminate | rewrite hcr5_overridePost2, <- E1; apply hcr5_Q1a_ok; exact HH |].
    eapply hcr5_semax_cut with (Q := hcr5_SQ1b x25519 gv L FR);
      [discriminate | rewrite hcr5_overridePost2, <- E2; apply hcr5_Q1b_ok; exact HH |].
    eapply hcr5_semax_cut with (Q := hcr5_SQ2 x25519 aead_dec gv L FR);
      [discriminate | rewrite hcr5_overridePost2, <- E3; apply hcr5_Q2_ok; exact HH |].
    eapply hcr5_semax_cut with (Q := hcr5_SQ3 x25519 aead_dec gv L FR);
      [discriminate | rewrite hcr5_overridePost2, <- E4; apply hcr5_Q3_ok; exact HH |].
    eapply hcr5_semax_cut with (Q := hcr5_SQ4 x25519 aead_dec gv L FR);
      [discriminate | rewrite hcr5_overridePost2, <- E5; apply hcr5_Q4_ok; exact HH |].
    rewrite <- E6. apply hcr5_Q5_ok; auto. }
  unfold hcr5_Delta, hcr5_cond, hcr5_R. simplify_func_tycontext.
  abbreviate_semax. unfold hcr5_world, hcr5_lvars, hcr5_globs, hcr5_snaps0, hcr5_scr; cbn [app].
  destruct (eq_dec m nullval) as [Hm|Hm].
  - subst m. unfold hcr5_mbuf at 1. rewrite if_true by auto. forward_if (hcr5_SE x25519 gv L FR).
    + discriminate.
    + forward. unfold hcr5_SE. destruct H0 as (Hpok & ? & ? & ? & ? & ?). Exists R S NS NS PS head T KE.
      unfold hcr5_world, hcr5_lvars, hcr5_globs, hcr5_snaps0, hcr5_scr; cbn [app]. entailer!.
      eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hp. apply Hp.
  - unfold hcr5_mbuf at 1. rewrite if_false by auto. Intros. forward_if (hcr5_SE x25519 gv L FR).
    + eapply semax_pre; [| exact HT].
      unfold hcr5_S5n. Exists R S NS PS head nb T KE m.
      unfold hcr5_world, hcr5_lvars, hcr5_globs, hcr5_snaps0, hcr5_scr; cbn [app]. entailer!.
    + contradiction.
Qed.

End Phase.
