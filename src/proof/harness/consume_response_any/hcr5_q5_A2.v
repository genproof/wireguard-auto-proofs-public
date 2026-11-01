(* law consume_response_any, phase Q5, segment A2: CHECK(hnodes_same_except(peers, target->p)).
   States and statements: hcr5_q5_defs.v; pure facts: hcr5_q5_pure.v (its statement is a hypothesis here,
   proved separately); (section Q5);
   src/proof/harness/consume_response_any/hcr3_q5_A2*.v. *)
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A2_sep.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_q5_A2_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hcr5_q5_pure_stmt x25519 aead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_QA1 x25519 aead_dec gv L FR) hcr5_q5_A2 (overridePost (hcr5_q5_QA1 x25519 aead_dec gv L FR) (hcr5_R gv)).
Proof.
  intros Hy Hpure.
  unfold hcr5_q5_QA1 at 1, hcr5_Delta, hcr5_q5_A2. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T KE m M. Intros a P ck h.
  unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_q5_scr, hcr5_snaps; cbn [app].
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  destruct Hpure as (Hp1 & _ & Hp3 & Hp4 & _ & Hp6).
  match goal with Hl: hcr5_list_ok _ _ _ _ _ _, Hpo: hcr5_pool _ _ _, Ht: hcr5_tg _ _ _ _ _ _ = Some _ |- _ =>
    destruct (Hp4 R L NS PS head nb KE T M a P ck h Hl Hpo HwfT Ht)
      as (NS1 & N & NS2 & PS1 & PS2 & E & HPS & Hsf & Hsupd & HNS & HNa & HNp & _);
    destruct (Hp6 PS a P M ck h Hsf) as [Hkeep _];
    destruct (Hp1 R L NS PS head nb KE T (supd PS a (hcr5_q5_put P M ck h)) Hl Hpo HwfT
                (or_intror (ex_intro _ a (ex_intro _ _ (conj eq_refl Hkeep)))))
      as (Hvo & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9) end.
  pose proof (Hp3 T PS a (hcr5_q5_put P M ck h)) as Hsame.
  assert (Hin: In a (map peer_addr4 (supd PS a (hcr5_q5_put P M ck h)))).
  { rewrite Hsupd, map_app. apply in_or_app. right. left. reflexivity. }
  clear Hp1 Hp3 Hp4 Hp6.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { assert_PROP (is_pointer_or_null (hcr5_head NS)) as Hhd.
    { sep_apply (hcr5_q5_A2_hn_pn (hcr5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
    forward.
    assert (HinN: In N (hnodes_snapped4 T NS PS)) by (rewrite HNS; apply in_or_app; right; left; reflexivity).
    pose proof (hcr5_q5_A2_node_acc (hcr5_head NS) _ N HinN) as A1. unfold hcr5_q5_A2_acc in A1. sep_apply A1. clear A1. flatten_sepcon_in_SEP.
    rewrite <- HNa.
    forward.
    rewrite HNp.
    sep_apply wand_frame_elim.
    sep_apply (hcr5_q5_A2_vo Tsh (l_wa L) (hcr5_DAL x25519 R L) (hcr5_khead KE) (map (kent_snapped T) KE)).
    forward_call (hcr5_head NS, hnodes_snapped4 T NS PS, supd PS a (hcr5_q5_put P M ck h),
                  hcr5_sns T PS, hcr5_rs PS, hcr5_prs PS, a, Tsh, l_ita L, T,
                  hcr5_q5_VO x25519 R L T KE).
    rewrite Hsame.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. rewrite HNa. unfold hcr5_q5_VO. rewrite <- hcr5_q5_A2_vo. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold hcr5_q5_QA1.
  Exists R S NS PS head nb T KE m M. Exists a P ck h.
  unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_q5_scr, hcr5_snaps; cbn [app].
  entailer!.
Qed.

End Seg.
