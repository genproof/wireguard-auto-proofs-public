(* law consume_initiation_any, phase P8, segment A3, statement s7 (port of v1's hci3_p8_A3_s7.v):
     CHECK(bytes_eq(h->latest_timestamp, ci.ts, 12))
   Shared: hci5_p8_A3_defs.v (statements, cut), hci5_p8_A3_pure.v
   (hci5_p8_A3_facts), hci5_p8_A3_sep.v (accessors). *)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_s7_eqb_refl A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hci5_p8_A3_s7_c4 sh ck h key spub t ci : Zlength t = 12 ->
     @data_at HCS sh t_mcinit (mcinit_val ck h key spub (bytes t)) ci |--
     hbytes sh t (offset_val 128 ci) *
     (hbytes sh t (offset_val 128 ci) -* @data_at HCS sh t_mcinit (mcinit_val ck h key spub (bytes t)) ci).
Proof.
  intros L. assert_PROP (@field_compatible HCS t_mcinit [] ci) by entailer!.
  unfold mcinit_val. unfold_data_at (@data_at HCS _ _ _ ci).
  rewrite (@field_at_data_at HCS sh t_mcinit [StructField HH._ts]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

Lemma hci5_p8_A3_s7_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR)
    hci5_p8_A3_s7 (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. destruct HH as (Hx & Ha & Hxa & Hrep).
  unfold hci5_p8_QA1, hci5_Delta, hci5_R, hci5_p8_A3_s7. simplify_func_tycontext.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct (hci5_p8_A3_facts x25519 aead_enc aead_dec R L NS PS KE T head na M (s_boot S) a P t ck2 h2 Ha H0 Hwf H1 H3)
    as (NS1 & N & NS2 & PS1 & PS2 & HNS & Hna & Hnp & Hsn & Hnr & Hnrest & HPS & Hdel & Hsf & Hin & Hpok & HinT & Hep
        & Hpkn & Hslot & Lt & Lck & Lh).
  rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf). Intros.
  sep_apply (hci5_p8_A3_pk_ts Ews a (hci5_p8_put P M (s_boot S) t ck2 h2)). Intros.
  rewrite (hci5_p8_A3_put_ts P M (s_boot S) t ck2 h2).
  sep_apply (hci5_p8_A3_s7_c4 Tsh ck2 h2 key spub t (l_ci L) Lt). Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - assert_PROP (isptr a) as Pa.
    { unfold hbytes. entailer!.
      match goal with Hf: field_compatible _ _ (offset_val 328 ?x) |- isptr ?x =>
        destruct Hf as [Hp _]; destruct x; try contradiction; exact I end. }
    forward_call (Ews, offset_val 328 a, t, Tsh, offset_val 128 (l_ci L), t).
    { unfold hs_addr. match goal with |- isptr (offset_val _ ?x) => destruct x; try contradiction; exact I end. }
    { entailer!. rewrite Lt. unfold hs_addr. simpl. normalize. }
    rewrite hci5_p8_A3_s7_eqb_refl.
    forward_if True.
    { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    { forward. entailer!. }
    forward. entailer!.
  - sep_apply (hci5_p8_A3_mp (hbytes Tsh t (offset_val 128 (l_ci L)))
      (@data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L))).
    sep_apply (hci5_p8_A3_mp (hbytes Ews t (offset_val 328 a))
      (peer_rep Ews a (hci5_p8_put P M (s_boot S) t ck2 h2))).
    Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
    rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf).
    entailer!.
Qed.

End Seg.
