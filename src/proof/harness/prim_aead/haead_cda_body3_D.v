(* law prim_aead: check_decrypt_any, segment D (the checks (ok == rok, bytes_eq) and the four frees).
   the cut and the states: haead_cda_body3_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_defs.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma cdaD_free (n: Z) (v: list val) (p: val) : p <> nullval ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic |--
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p).
Proof. intros. rewrite if_false by auto. cancel. Qed.

Ltac cdaD_free p n v gv :=
  let Hn := fresh "Hnn" in
  assert_PROP (p <> nullval) as Hn by (entailer!; destruct p; try contradiction; intro; discriminate);
  sep_apply (cdaD_free n v p Hn);
  forward_call (tarray tuchar n, p, gv).

Lemma cda_D_ok {Espec: OracleKind} (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals) (c: list byte) (c2 d2 db rd2: val) (bs: list byte) :
  readable_share ksh -> readable_share xsh -> readable_share ash -> readable_share csh ->
  Int.min_signed <= x <= Int.max_signed -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  Zlength xnonce = 24 -> Zlength a <= Int64.max_signed -> 16 <= Zlength ct <= Int64.max_signed ->
  semax cda_Delta (cda_P3 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv c c2 d2 db rd2 bs) cda_D (cda_R x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv).
Proof.
  intros. unfold cda_Delta, cda_P3, cda_R, cda_D. simplify_func_tycontext. abbreviate_semax.
  Intros. unfold cda_out, cda_rout, cda_b.
  destruct (cda_dec x key nonce xnonce a c) as [pt |] eqn:Hd.
  - match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_if; [discriminate |]. forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    assert_PROP (Zlength pt = Z.max 0 (Zlength c - 16)) as Hpt.
    { entailer!. rewrite Zlength_map in *. auto. }
    rewrite <- Hpt.
    match goal with |- semax _ ?P _ _ => forward_if P end.
    + match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      { apply ENTAIL_refl. }
      { forward_call (Ews, d2, pt, Ews, rd2, pt).
        rewrite if_true by auto.
        match goal with |- semax _ ?P _ _ => forward_if P end.
        { discriminate. }
        { forward. entailer!. }
        forward. entailer!. }
    + discriminate.
    + cdaD_free c2 (Zlength c) (map Vubyte c) gv. cdaD_free d2 (Zlength pt) (map Vubyte pt) gv.
      cdaD_free db (Zlength pt) (map Vubyte bs) gv. cdaD_free rd2 (Zlength pt) (map Vubyte pt) gv.
      entailer!.
  - match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_if; [discriminate |]. forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    rewrite <- H10.
    match goal with |- semax _ ?P _ _ => forward_if P end.
    + contradiction.
    + match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      { apply ENTAIL_refl. }
      { forward_call (Ews, d2, bs, Ews, db, bs).
        rewrite if_true by auto.
        match goal with |- semax _ ?P _ _ => forward_if P end.
        { discriminate. }
        { forward. entailer!. }
        forward. entailer!. }
    + cdaD_free c2 (Zlength c) (map Vubyte c) gv. cdaD_free d2 (Zlength bs) (map Vubyte bs) gv.
      cdaD_free db (Zlength bs) (map Vubyte bs) gv. cdaD_free rd2 (Zlength bs) (Zrepeat Vundef (Zlength bs)) gv.
      entailer!.
Qed.
