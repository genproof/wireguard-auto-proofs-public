(* law keypairs, segment Op0 part A, piece A3: statements 11..12 of the op 0 branch
   (hs_take(&snap, &p.handshake); r = wg_noise_handshake_begin_session(&p.handshake, &p.keypairs)).
   States: hkp5_segOp0_A_defs.v; "Op0 part A". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_o0A_3_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i Y E k R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0A_N x25519 F V steps FR i Y E k) hkp5_o0A_s3
    (overridePost (EX O: hkp5_o0, hkp5_o0_M x25519 F V steps FR i O) R).
Proof.
  intros HF HX.
  pose proof HF as (HMpre & HMslots & _).
  unfold hkp5_o0A_N, hkp5_Delta, hkp5_o0A_s3.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ws kc P KS T HH now next_id id_known hsn].
  unfold hkp5_SEP, hkp5_world, hkp5_hglobs, hkp5_globs, hk5_items, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn] in *.
  Intros.
  pose proof H1 as Hinv0.
  destruct H1 as (Hrel & Hwarn & Hdev & Hsid & Hrefs & Hfr & Hal & Hid & Hnow).
  cbn [y_P y_H y_KS y_T y_S y_kc y_now y_next_id y_id_known f_w f_p] in Hrel, Hdev, Hsid.
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
    f_snap := snap; f_opub := opub; f_first := first; f_second := second |}) in *.
  abbreviate_semax.
  pose proof Hrel as (Hcore & _).
  destruct (HMpre _ _ _ _ _ _ _ Hcore) as (Hkpool & Hhpool & _).
  pose proof (HMslots _ _ _ _ _ _ _ Hrel) as Hslots.
  pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & (idx & Hhs) & _)).
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfcp by (unfold peer_rep; entailer!).
  assert_PROP (isptr w) as Pw by (unfold device_rep; entailer!).
  assert (Pp: isptr p) by (destruct Hfcp; auto).
  assert (HE: E = mkEntry p IDX_HANDSHAKE idx)
    by (match goal with Hx: t_entry T _ = Some E |- _ => unfold t_entry in Hx; rewrite Hhs in Hx; inversion Hx end;
        reflexivity).
  assert_PROP (~ In k (map fst (h5_ML HH))) as Hkf.
  { sep_apply (hkp5_o0_fresh_node k (h5_ML HH)). entailer!. }
  forward_call (Tsh, snap, Tsh, p, P, Tsh, t, T, E).
  { split; [subst E; cbn [e_peer]; destruct p; try contradiction; discriminate |].
    rewrite Hsid. unfold id_addr. destruct w; try contradiction; discriminate. }
  change (itable Tsh t T) with (itable Tsh (d_itab (hkp5_D x25519 F0 V)) T).
  forward_call (gv, S, ws, kc, KS, T, Tsh, p, P, Tsh, w, hkp5_D x25519 F0 V, Tsh).
  Intros kp.
  forward.
  destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
  Exists (mkO5 (mkKY5 S ws kc P KS T HH now next_id id_known hsn) E k kp).
  unfold hkp5_o0_M, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, o5_res, o5_w, o5_sn, hk5_items, hkp5_hglobs,
    hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta.
  cbn [app o_Y o_E o_k o_kp f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS
       y_T y_H y_now y_next_id y_id_known y_hsn].
  replace (force_val (sem_cast tbool tbool (Val.of_bool (fst (fst (fst (P4.bs_res P p kp kc KS T S)))))))
    with (Val.of_bool (fst (fst (fst (P4.bs_res P p kp kc KS T S)))))
    by (destruct (fst (fst (fst (P4.bs_res P p kp kc KS T S)))); reflexivity).
  change (d_itab (hkp5_D x25519 F0 V)) with t.
  change (f_gv F0) with gv. change (f_w F0) with w. change (f_t F0) with t. change (f_pt F0) with pt.
  change (f_p F0) with p. change (f_raw F0) with raw. change (f_pub F0) with pub. change (f_snap F0) with snap.
  change (f_opub F0) with opub. change (f_first F0) with first. change (f_second F0) with second.
  entailer!.
Qed.
