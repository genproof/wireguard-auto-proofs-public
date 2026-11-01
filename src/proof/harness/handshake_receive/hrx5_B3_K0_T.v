(* law handshake_receive, phase B3, branch kind 0, segment T:
   stmt 7: if (len >= 4 && (nondet_u8() & 1)) le32_store(buf, draw_type(1 + nondet_u8() % 4)) (the first 4 bytes of buf).
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
Local Open Scope logic.

(* helpers: the first 4 bytes of the kind-0 buffer (as hrx5_B3_K0_I1's split / join at 148) *)
Lemma hrx5_k0t_hbytes sh bs p : bytes_at sh bs p = hbytes sh bs p.
Proof. unfold bytes_at, hbytes. apply data_at_tarray_tuchar_cs. Qed.

Lemma hrx5_k0t_fc (B: list byte) (dp: val) : 0 <= Zlength B -> malloc_compatible (Zlength B) dp ->
  @field_compatible Noise.CS (tarray tuchar (Zlength B)) [] dp.
Proof.
  intros N MC. apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
  replace (@sizeof Noise.CS (tarray tuchar (Zlength B))) with (Zlength B) by (simpl; lia). exact MC.
Qed.

Lemma hrx5_k0t_eqB (B: list byte) : 4 <= Zlength B ->
  B = sublist 0 4 B ++ sublist 4 (Zlength B) B.
Proof. intros. rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. Qed.

Lemma hrx5_k0t_split (B: list byte) (dp: val) : 4 <= Zlength B -> malloc_compatible (Zlength B) dp ->
  bytes_at Ews B dp |-- hout Ews 4 dp * bytes_at Ews (sublist 4 (Zlength B) B) (offset_val 4 dp).
Proof.
  intros N MC. pose proof (hrx5_k0t_fc B dp ltac:(lia) MC) as FC.
  rewrite (hrx5_k0t_eqB B N) at 1. rewrite prot_rep3_bytes_app.
  2: { rewrite <- Zlength_app, <- hrx5_k0t_eqB by lia. exact FC. }
  rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia. cancel.
  unfold bytes_at, hout. rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia.
  rewrite (@data_at__tarray_tuchar_cs HCS Noise.CS). apply data_at_data_at_.
Qed.

Lemma hrx5_k0t_join (B X: list byte) (dp: val) : Zlength X = 4 -> 4 <= Zlength B -> malloc_compatible (Zlength B) dp ->
  hbytes Ews X dp * bytes_at Ews (sublist 4 (Zlength B) B) (offset_val 4 dp) |--
  bytes_at Ews (X ++ sublist 4 (Zlength B) B) dp.
Proof.
  intros LX N MC. pose proof (hrx5_k0t_fc B dp ltac:(lia) MC) as FC.
  rewrite prot_rep3_bytes_app.
  2: { rewrite Zlength_sublist, LX by lia. replace (4 + (Zlength B - 4)) with (Zlength B) by lia. exact FC. }
  rewrite LX. cancel. rewrite hrx5_k0t_hbytes. apply derives_refl.
Qed.

Lemma hrx5_k0t_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Section K0T.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K0_T_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M x25519 gv L FR) hrx5_K0_T
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K0_M, hrx5_K0_Mc. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port B dp.
  unfold hrx5_K0_T, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (EX v: int, PROPx [v <> Int.zero -> 4 <= Zlength B] (LOCALx (temp HRM._t'43 (Vint v) :: Q) (SEPx SS))) end.
  - forward_call. Intros u. forward.
    assert (4 <= Zlength B).
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
    + forward_call. Intros u.
      forward_call (Int.add (Int.repr 1) (Int.mods (Int.repr u) (Int.repr 4))).
      { split.
        - unfold Int.mods. rewrite (Int.signed_repr u) by rep_lia. rewrite (Int.signed_repr 4) by rep_lia.
          assert (0 <= Z.rem u 4 < 4) by (split; [apply Z.rem_nonneg; lia | apply Z.rem_bound_pos; lia]).
          rewrite Int.signed_repr by rep_lia. rep_lia.
        - intros [_ X]. apply (f_equal Int.unsigned) in X. vm_compute in X. discriminate. }
      Intros r. specialize (H5 H6). unfold obj_rep. Intros. sep_apply (hrx5_k0t_split B dp H5 H4).
      forward_call (Ews, dp, r). { cancel. }
      match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K0_M x25519 gv L FR) end.
      set (B' := le32 r ++ sublist 4 (Zlength B) B).
      assert (LB: Zlength B' = Zlength B).
      { subst B'. rewrite Zlength_app, hrx5_k0t_le32_len, Zlength_sublist by lia. lia. }
      assert (OKB: obj_ok (OBuf B')) by (unfold obj_ok in *; rewrite LB; exact H3).
      sep_apply (hrx5_k0t_join B (le32 r) dp (hrx5_k0t_le32_len r) H5 H4). fold B'.
      unfold hrx5_K0_M, hrx5_K0_Mc.
      Exists R sec birth S w NS PS T.
      Exists head nk KE st i kc lul q.
      Exists proto ip4 ip6 port B' dp.
      unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
      unfold obj_rep. rewrite LB.
      go_lower. apply andp_right.
      { apply prop_right. refine (conj H (conj H0 (conj H1 (conj H2 (conj OKB (conj H4 (conj I _))))))).
        repeat split; auto. }
      cancel.
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

End K0T.
