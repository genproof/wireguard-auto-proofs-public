(* law consume_response_any, phase Q2: statements 4..11 of P6's then-branch: resp_img(img, msg); wg_shim_boottime_ns = draw_boottime(); hnodes_snap(peers); kents_snap(kes); dev_take(&ds, &wa); head0 = ita.head; shim_take(&ss); ret = wg_noise_handshake_consume_response(msg, &wa).
*)
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
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q2_lem.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_Q2_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SQ1b x25519 gv L FR) hcr5_Q2
    (overridePost (hcr5_SQ2 x25519 aead_dec gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_SQ1b, hcr5_Delta, hcr5_R, hcr5_Q2. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T KE m M.
  unfold hcr5_lvars, hcr5_scr, hcr5_world, hcr5_globs, hcr5_snaps0; cbn [app].
  forward_call (Tsh, l_img L, Ews, m, M).
  forward_call tt. Intros n.
  unfold shim_state4. rewrite (hcr5_q2_core_open gv S). Intros. rename H5 into HSok.
  forward.
  sep_apply (hcr5_q2_shim_fold gv S n hcr5_w0 HSok).
  assert_PROP (is_pointer_or_null (hcr5_head NS)) as Hpn by (sep_apply (hcr5_q2_pn (hcr5_head NS) NS); entailer!).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) KE) as Hkp by (sep_apply (hcr5_q2_kptrs (hcr5_khead KE) KE); entailer!).
  assert_PROP (isptr (l_wa L) /\ isptr (l_pta L) /\ isptr (l_ita L)) as Hlv by entailer!.
  destruct Hlv as (Hwa & Hpt & Hit).
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  pose proof H0 as Hok. destruct Hok as (Hpok & Hwf & Hch & Hnp & Hnd & Hnb).
  forward.
  forward_call (hcr5_head NS, NS, PS, Tsh, l_ita L, T).
  { apply (hcr5_q2_snap_pre L KE NS PS head nb T H0 H1 HwfT Hkp Hwa). }
  forward_call (hcr5_khead KE, KE, Tsh, l_ita L, T).
  { apply (hcr5_q2_ksnap_pre L KE NS PS head nb T H0 H1 HwfT). }
  change (ptable Tsh (l_pta L) head) with (ptable Tsh (d_ptab (hcr5_DAL x25519 R L)) head).
  forward_call (Tsh, l_ds L, Tsh, l_wa L, hcr5_DAL x25519 R L, Tsh, head).
  { pose proof (hcr5_q2_head head PS Hch (hcr5_q2_pptrs _ _ _ Hpok)).
    unfold hcr5_DAL, hcr5_DA, setup_dev; cbn.
    repeat constructor; try discriminate; auto; intro X; rewrite X in *; contradiction. }
  rewrite hcr5_q2_itable_open. Intros.
  pose proof (hcr5_q2_hd_pn L KE NS PS head nb T H0 H1 HwfT Hkp) as Hhd.
  forward.
  sep_apply (hcr5_q2_itable_fold Tsh (l_ita L) T HwfT).
  forward_call (gv, Tsh, l_ss L, shim_set_boot S n, hcr5_w0).
  change (itable Tsh (l_ita L) T) with (itable Tsh (d_itab (hcr5_DAL x25519 R L)) T).
  forward_call (gv, shim_set_boot S n, hcr5_w0, Ews, m, M, Tsh, l_wa L, hcr5_DAL x25519 R L, Tsh, T, PS).
  { split; [eapply hcr5_q2_ppok; eassumption | eapply hcr5_q2_refs_ok; exact Hpok]. }
  forward.
  unfold hcr5_SQ2. Exists R (shim_set_boot S n) NS PS head nb T KE m M.
  unfold hcr5_lvars, hcr5_scr, hcr5_world, hcr5_globs, hcr5_snaps, hcr5_res; cbn [app].
  change (d_ptab (hcr5_DAL x25519 R L)) with (l_pta L).
  change (d_itab (hcr5_DAL x25519 R L)) with (l_ita L).
  entailer!.
Qed.

End Phase.
