(* law handshake_receive, phase B3, branch kind 0, segment C:
   stmt 8: if (len >= 32 && (nondet_u8() & 1)) draw_macs(buf, len, mk1, wd.cookie_checker.secret, &skb).
   States and statements: hrx5_B3_K0_defs.v. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_C_lem.
Local Open Scope logic.

Lemma hrx5_k0c_hbytes sh bs p : bytes_at sh bs p = hbytes sh bs p.
Proof. unfold bytes_at, hbytes. apply data_at_tarray_tuchar_cs. Qed.

Section K0C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K0_C_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M x25519 gv L FR) hrx5_K0_C
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K0_M, hrx5_K0_Mc. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port B dp.
  unfold hrx5_K0_C, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (EX v: int, PROPx [v <> Int.zero -> 32 <= Zlength B] (LOCALx (temp HRM._t'45 (Vint v) :: Q) (SEPx SS))) end.
  - forward_call. Intros u. forward.
    assert (32 <= Zlength B).
    { destruct H3 as (_ & _ & _ & H3).
      rewrite !Int64.unsigned_repr in H5 by (pose proof (Zlength_nonneg B); rep_lia). lia. }
    Exists (if Int.eq (Int.and (Int.repr u) (Int.repr 1)) Int.zero then Int.zero else Int.one).
    go_lower. apply andp_right; [| cancel]. apply prop_right.
    split; [intros; lia|]. split; [reflexivity|]. repeat split; auto.
  - forward. Exists Int.zero.
    go_lower. apply andp_right; [| cancel]. apply prop_right.
    split; [intros; congruence|]. split; [reflexivity|]. repeat split; auto.
  - Intros v.
    forward_if.
    + specialize (H5 H6).
      assert (HBm: Zlength B <= Int.max_unsigned) by (destruct H3 as (_ & _ & _ & H3); exact H3).
      unfold hrx5_skb_part, wg_consts. Intros dv lv. Intros.
      set (D := hrx5_DL x25519 R L sec birth).
      rewrite (hrx5_k0c_dev_split Tsh (l_wd L) D).
      assert_PROP (@field_compatible Noise.CS t_dev [] (l_wd L)) as FCB by (unfold hrx5_k0c_drest; entailer!).
      rewrite (hrx5_k0c_cc_open Tsh (l_wd L) (d_cc D)) by exact FCB. Intros.
      match goal with Hc: cc_ok (d_cc D) |- _ => rename Hc into HCC end.
      assert (Hs: Zlength (cc_secret (d_cc D)) = 32) by (destruct HCC as (Hs & _); exact Hs).
      match goal with Hp: 0 <= proto <= 65535 /\ _ |- _ => destruct Hp as (Hp1 & Hp2 & Hp3 & Hp4) | _ => idtac end.
      sep_apply (derives_refl' _ _ (hrx5_k0c_skb_src dv lv proto ip4 ip6 port (l_skb L) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto))).
      assert (Hmk: Zlength (hrx5_mk1 x25519 R) = 32) by apply hrx5_k0c_mk1_len.
      unfold obj_rep. Intros. rewrite hrx5_k0c_hbytes.
      forward_call (gv, Ews, dp, B, Tsh, l_mk1 L, hrx5_mk1 x25519 R, Tsh, cc_addr (l_wd L),
                    cc_secret (d_cc D), Tsh, l_skb L, mkSkb nullval Int.zero proto ip4 ip6 port, dv, lv).
      Intros B'.
      match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K0_M x25519 gv L FR) end.
      sep_apply (hrx5_k0c_cc_close Tsh (l_wd L) (d_cc D) FCB HCC).
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_k0c_dev_split Tsh (l_wd L) D))).
      sep_apply (hrx5_k0c_skb_part L dv lv proto ip4 ip6 port).
      match goal with Hl: Zlength B' = Zlength B |- _ => rename Hl into LB end.
      assert (OKB: obj_ok (OBuf B')) by (unfold obj_ok in *; rewrite LB; exact H3).
      rewrite <- hrx5_k0c_hbytes.
      unfold hrx5_K0_M, hrx5_K0_Mc.
      Exists R sec birth S w NS PS T.
      Exists head nk KE st i kc lul q.
      Exists proto ip4 ip6 port B' dp.
      unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, wg_consts; cbn [app].
      unfold obj_rep. rewrite LB.
      go_lower. apply andp_right.
      { apply prop_right. refine (conj H (conj H0 (conj H1 (conj H2 (conj OKB (conj H4 (conj I _))))))).
        repeat split; auto. }
      subst D. cancel.
    + forward.
      unfold hrx5_K0_M, hrx5_K0_Mc.
      Exists R sec birth S w NS PS T.
      Exists head nk KE st i kc lul q.
      Exists proto ip4 ip6 port B dp.
      unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
      go_lower. apply andp_right.
      { apply prop_right. refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj H4 (conj I _))))))).
        repeat split; auto. }
      cancel.
Qed.

End K0C.
