(* law prim_aead: check_decrypt_any, segment A (the first if: c2 = malloc'd copy of ct with maybe one byte flipped, or ANY m <= PTRDIFF_MAX bytes).
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

Lemma cda_tc_Vubyte (y: byte) : tc_val tuchar (Vubyte y).
Proof. simpl. unfold Vubyte. pose proof (Byte.unsigned_range_2 y). rewrite Int.unsigned_repr; rep_lia. Qed.

Lemma cda_ze8 (w: int) : Vint (Int.zero_ext 8 w) = Vubyte (Byte.repr (Int.unsigned w)).
Proof.
  unfold Vubyte. f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 w)).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma cda_bytes_Vubyte (bs: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; [reflexivity |]. simpl. rewrite IHForall. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma cda_A_ok {Espec: OracleKind} (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals) :
  readable_share ksh -> readable_share xsh -> readable_share ash -> readable_share csh ->
  Int.min_signed <= x <= Int.max_signed -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  Zlength xnonce = 24 -> Zlength a <= Int64.max_signed -> 16 <= Zlength ct <= Int64.max_signed ->
  semax cda_Delta (cda_P0 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv) cda_A
    (overridePost (EX c: list byte, EX c2: val, cda_P1 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv c c2) (cda_R x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv)).
Proof.
  intros. unfold cda_Delta, cda_P0, cda_R, cda_A. cbv [hd]. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros b.
  forward_if.
  - (* copy of ct, maybe one byte flipped *)
    forward.
    assert (Em: Int64.add (Int64.repr (Zlength ct - 16)) (Int64.repr (Int.signed (Int.repr 16))) =
                Int64.repr (Zlength ct)).
    { change (Int.signed (Int.repr 16)) with 16. rewrite Int64.add_signed.
      rewrite !Int64.signed_repr by rep_lia. f_equal; lia. }
    rewrite Em; clear Em.
    forward_call (tarray tuchar (Zlength ct), gv).
    { simpl sizeof. rep_lia. }
    Intros c2.
    destruct (eq_dec c2 nullval) as [Hn | Hn].
    { subst c2. forward_if; [| contradiction].
      forward. entailer!. }
    Intros. forward_if; [contradiction |].
    forward_call (Ews, c2, csh, cp, ct).
    forward_call tt. Intros i.
    forward_if.
    + forward_call tt. Intros v.
      forward.
      { entailer!. apply cda_tc_Vubyte. }
      rewrite Znth_map by lia.
      forward.
      { entailer!. unfold Int.mods. rewrite (Int.signed_repr v) by rep_lia.
        rewrite (Int.signed_repr 255) by rep_lia. rewrite Z.rem_mod_nonneg by lia.
        pose proof (Z.mod_pos_bound v 255 ltac:(lia)). rewrite Int.signed_repr by rep_lia.
        split; [rep_lia |]. intros [_ E]. discriminate E. }
      match goal with |- context [upd_Znth i (map Vubyte ct) (Vint (Int.zero_ext 8 ?w))] =>
        rewrite (cda_ze8 w), upd_Znth_map; Exists (upd_Znth i ct (Byte.repr (Int.unsigned w))) c2 end.
      unfold cda_P1. rewrite upd_Znth_Zlength by lia. entailer!.
    + forward. Exists ct c2. unfold cda_P1. entailer!.
  - (* ANY m bytes *)
    forward_call tt. Intros m.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m <= Int64.max_signed) :: P) (LOCALx Q (SEPx R))) end.
    { forward. }
    { forward. entailer!. }
    Intros.
    forward_if.
    { exfalso. match goal with Hl: Int64.ltu _ _ = true |- _ => revert Hl end.
      unfold Int64.ltu. rewrite (Int64.unsigned_repr m) by rep_lia.
      change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned.
      destruct (zlt _ _); [lia | discriminate]. }
    forward_call (tarray tuchar m, gv).
    { simpl sizeof. rep_lia. }
    Intros c2.
    destruct (eq_dec c2 nullval) as [Hn | Hn].
    { subst c2. forward_if; [| contradiction].
      forward. entailer!. }
    Intros. forward_if; [contradiction |].
    forward_call (c2, m, Ews).
    Intros bs.
    Exists (map Byte.repr bs) c2. unfold cda_P1. rewrite Zlength_map.
    rewrite cda_bytes_Vubyte by assumption. subst m. entailer!.
Qed.
