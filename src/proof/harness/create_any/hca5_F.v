(* law create_any: main's body, phase F (statement 25: if (op == 0) F0 else F1, from
   the segments of hca5_fdefs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
Require Import WgNoise.proof.harness.create_any.hca5_F0a.
Require Import WgNoise.proof.harness.create_any.hca5_F0b.
Require Import WgNoise.proof.harness.create_any.hca5_F0c.
Require Import WgNoise.proof.harness.create_any.hca5_F1a.
Require Import WgNoise.proof.harness.create_any.hca5_F1b.
Require Import WgNoise.proof.harness.create_any.hca5_F1c.
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope logic.

Lemma hca5_p_set_hs_same P : p_set_hs P (p_hs P) = P.
Proof. destruct P; reflexivity. Qed.

Section F.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hca5_F0_ok {Espec: OracleKind} (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SEo x25519 gv L FR w 0)
    hca5_F0
    (overridePost (hca5_SF x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH.
  rewrite hca5_F0_eq. unfold hca5_F0m, hca5_F0cond.
  unfold hca5_SEo, hca5_Delta, hca5_R. abbreviate_semax.
  Intros R S P T KS E.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  forward_call (t_init_W, gv).
  Intros m.
  forward_if (hca5_SF x25519 gv L FR w).
  { destruct (eq_dec m nullval) as [Hm|Hm].
    - subst m. entailer!.
    - entailer!. }
  - destruct (eq_dec m nullval) as [Hm|Hm]; [contradiction |].
    eapply semax_pre with (P' := hca5_F0S0 x25519 gv L FR w m).
    { unfold hca5_F0S0. Exists R S P T KS E.
      unfold hca5_globs, hca5_world, hca5_scr, hca5_scr0, hca5_lvars, hca5_tok. cbn [app]. entailer!. }
    rewrite hca5_F0body_eq.
    destruct hca5_F0segs_eq as (Ea & Eb & Ec).
    eapply hca5_semax_cut with (Q := hca5_F0S1 x25519 aead_enc gv L FR w m);
      [discriminate | rewrite <- Ea; apply hca5_F0a_ok; exact HH |].
    eapply hca5_semax_cut with (Q := hca5_F0S2 x25519 aead_enc gv L FR w m);
      [discriminate | rewrite <- Eb; apply hca5_F0b_ok; exact HH |].
    rewrite <- Ec. apply hca5_F0c_ok; exact HH.
  - forward.
    destruct (eq_dec m nullval) as [Hm|Hm]; [| contradiction].
    unfold hca5_SF. Exists R P T KS E false (p_hs P) Int.zero T S S.
    rewrite hca5_p_set_hs_same. unfold hca5_res_ok, hca5_pok in *.
    unfold hca5_globs, hca5_world, hca5_scr, hca5_scr0, hca5_lvars. cbn [app].
    sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L)).
    entailer!. tauto.
Qed.

Lemma hca5_F1_ok {Espec: OracleKind} (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SEo x25519 gv L FR w 1)
    hca5_F1
    (overridePost (hca5_SF x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH.
  rewrite hca5_F1_eq. unfold hca5_F1m, hca5_F1cond.
  unfold hca5_SEo, hca5_Delta, hca5_R. abbreviate_semax.
  Intros R S P T KS E.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  forward_call (t_resp_W, gv).
  Intros m.
  forward_if (hca5_SF x25519 gv L FR w).
  { destruct (eq_dec m nullval) as [Hm|Hm].
    - subst m. entailer!.
    - entailer!. }
  - destruct (eq_dec m nullval) as [Hm|Hm]; [contradiction |].
    eapply semax_pre with (P' := hca5_F1S0 x25519 gv L FR w m).
    { unfold hca5_F1S0. Exists R S P T KS E.
      unfold hca5_globs, hca5_world, hca5_scr, hca5_scr0, hca5_lvars, hca5_tok. cbn [app]. entailer!. }
    rewrite hca5_F1body_eq.
    destruct hca5_F1segs_eq as (Ea & Eb & Ec).
    eapply hca5_semax_cut with (Q := hca5_F1S1 x25519 aead_enc gv L FR w m);
      [discriminate | rewrite <- Ea; apply hca5_F1a_ok; exact HH |].
    eapply hca5_semax_cut with (Q := hca5_F1S2 x25519 aead_enc gv L FR w m);
      [discriminate | rewrite <- Eb; apply hca5_F1b_ok; exact HH |].
    rewrite <- Ec. apply hca5_F1c_ok; exact HH.
  - forward.
    destruct (eq_dec m nullval) as [Hm|Hm]; [| contradiction].
    unfold hca5_SF. Exists R P T KS E false (p_hs P) Int.zero T S S.
    rewrite hca5_p_set_hs_same. unfold hca5_res_ok, hca5_pok in *.
    unfold hca5_globs, hca5_world, hca5_scr, hca5_scr0, hca5_lvars. cbn [app].
    sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L)).
    entailer!. tauto.
Qed.

End F.

Lemma hca5_PF_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SE x25519 gv L FR w)
    hca5_PF
    (overridePost (hca5_SF x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH.
  unfold hca5_SE. apply semax_extract_exists. intros o.
  apply semax_extract_prop. intros Ho.
  assert (Ho': o = 0 \/ o = 1) by lia.
  rewrite hca5_PF_eq, hca5_Fcond_eq.
  destruct Ho' as [-> | ->].
  - pose proof (@hca5_F0_ok x25519 aead_enc aead_dec xaead_enc xaead_dec Espec gv L FR w HH) as H0.
    unfold hca5_SEo in *. unfold hca5_Delta, hca5_R in *. abbreviate_semax.
    Intros R S P T KS E.
    forward_if (hca5_SF x25519 gv L FR w).
    + eapply semax_pre; [| exact H0].
      Exists R S P T KS E. unfold hca5_globs, hca5_world, hca5_scr, hca5_scr0, hca5_lvars. cbn [app].
      entailer!.
    + exfalso. lia.
  - pose proof (@hca5_F1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec Espec gv L FR w HH) as H1.
    unfold hca5_SEo in *. unfold hca5_Delta, hca5_R in *. abbreviate_semax.
    Intros R S P T KS E.
    forward_if (hca5_SF x25519 gv L FR w).
    + exfalso. lia.
    + eapply semax_pre; [| exact H1].
      Exists R S P T KS E. unfold hca5_globs, hca5_world, hca5_scr, hca5_scr0, hca5_lvars. cbn [app].
      entailer!.
Qed.
