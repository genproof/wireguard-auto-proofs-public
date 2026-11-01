(* law handshake_receive: main's phase PZ = kents_free, hnodes_free, return 0 (statements 21..23).
   From hrx5_SX to hrx5_FF (hrx5_defs.v; the cut: hrx5_cut.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PZ_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section PZ.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_PZ_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SX x25519 gv L FR) hrx5_PZ
    (overridePost (FF) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_SX, hrx5_SLc, hrx5_Delta, hrx5_R, hrx5_PZ. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w NS PS T.
  Intros head nk KE st i kc lul.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_skb0; cbn [app].
  destruct H0 as (Hpok & Hwf & Hnd & Hch & Hnp & Hnk & Hpool).
  assert (HF: Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS).
  { eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hx. unfold hrx5_pok in Hx. tauto. }
  sep_apply (hrx5_PZ_pool (l_itd L) T PS KE NS Hpool HF Hnp).
  forward_call (gv, hrx5_khead KE, KE).
  { cancel. }
  assert_PROP (is_pointer_or_null (hrx5_head NS)) as Hhd by (sep_apply (hrx5_PZ_pn (hrx5_head NS) NS); entailer!).
  forward.
  forward_call (gv, hrx5_head NS, NS).
  apply hrx5_post_canon.
  forward.
  destruct H as ((Hrd & Hrk) & _).
  destruct HH as (Hx & _).
  rewrite hrx5_conv_itab, hrx5_conv_skb, hrx5_conv_devsnap, hrx5_conv_shimsnap, hrx5_conv_skbsnap,
    hrx5_conv_mcinit, !hrx5_conv_mstate, hrx5_conv_init, hrx5_conv_resp, !hrx5_conv_bytes.
  sep_apply (hrx5_PZ_dev_W Tsh (l_wd L) (hrx5_DL x25519 R L sec birth)).
  sep_apply (hrx5_PZ_ptable (l_ptd L) head).
  sep_apply (hrx5_PZ_mident (mident_val (hrx5_ID x25519 R)) (l_id L)).
  sep_apply (hrx5_PZ_mident (mident_val (hrx5_IK x25519 R)) (l_ik L)).
  sep_apply (hrx5_PZ_hbytes32 (rr_rawd R) (l_rawd L) Hrd).
  sep_apply (hrx5_PZ_hbytes32 (rr_rawk R) (l_rawk L) Hrk).
  sep_apply (hrx5_PZ_hbytes32 (hrx5_mk1 x25519 R) (l_mk1 L) (hrx5_PZ_mk1_len x25519 R)).
  sep_apply (hrx5_PZ_hbytes32 (hrx5_ssk x25519 R) (l_ssk L) (hrx5_PZ_ssk_len x25519 R Hx)).
  sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hrx5_head NS) (l_peers L)).
  cancel.
Qed.

End PZ.
