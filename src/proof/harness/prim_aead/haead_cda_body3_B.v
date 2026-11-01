(* law prim_aead: check_decrypt_any, segment B (dn, the three mallocs of dn bytes, the NULL test (frees all four and returns)).
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

(* a malloc result: NULL, or a token and an uninitialised buffer of n bytes *)
Definition cdaB_mres (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.
Definition cdaB_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma cdaB_mres_valid (n: Z) (p: val) : cdaB_mres n p |-- valid_pointer p.
Proof.
  unfold cdaB_mres. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
      simpl. rewrite Z.max_r by lia. lia.
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

Lemma cdaB_mres_local (n: Z) (p: val) : cdaB_mres n p |-- !! is_pointer_or_null p.
Proof.
  unfold cdaB_mres. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

Lemma cdaB_cmp (p: val) : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if cdaB_nul p then Int.one else Int.zero).
Proof.
  intros Hp. unfold cdaB_nul. destruct (eq_dec p nullval) as [-> | Hn]; [reflexivity |].
  destruct p; try contradiction; simpl in Hp.
  - subst. contradiction Hn. reflexivity.
  - reflexivity.
Qed.

#[local] Hint Resolve cdaB_mres_valid : valid_pointer.
#[local] Hint Resolve cdaB_mres_local : saturate_local.

Lemma cda_B_ok {Espec: OracleKind} (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals) (c: list byte) (c2: val) (rest: statement) :
  readable_share ksh -> readable_share xsh -> readable_share ash -> readable_share csh ->
  Int.min_signed <= x <= Int.max_signed -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  Zlength xnonce = 24 -> Zlength a <= Int64.max_signed -> 16 <= Zlength ct <= Int64.max_signed ->
  (forall d2 db rd2, semax cda_Delta (cda_P2 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv c c2 d2 db rd2) rest (cda_R x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv)) ->
  semax cda_Delta (cda_P1 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv c c2) (cda_seqs cda_lB rest) (cda_R x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv).
Proof.
  intros. unfold cda_lB; simpl cda_seqs. unfold cda_Delta, cda_P1, cda_R. simplify_func_tycontext. abbreviate_semax.
  Intros. assert (0 <= Zlength c) by apply Zlength_nonneg.
  forward_if (temp CD._t'7 (Vlong (Int64.repr (Z.max 0 (Zlength c - 16))))).
  { rewrite !Int64.unsigned_repr in H12 by rep_lia. forward. entailer!. }
  { rewrite !Int64.unsigned_repr in H12 by rep_lia. forward. entailer!. rewrite Z.max_l by lia. reflexivity. }
  forward. forward_call (tarray tuchar (Z.max 0 (Zlength c - 16)), gv).
  { entailer!. simpl. do 3 f_equal. lia. }
  { simpl sizeof. rep_lia. }
  Intros d2. fold (cdaB_mres (Z.max 0 (Zlength c - 16)) d2).
  forward_call (tarray tuchar (Z.max 0 (Zlength c - 16)), gv).
  { entailer!. simpl. do 3 f_equal. lia. }
  { simpl sizeof. rep_lia. }
  Intros db. fold (cdaB_mres (Z.max 0 (Zlength c - 16)) db).
  forward_call (tarray tuchar (Z.max 0 (Zlength c - 16)), gv).
  { entailer!. simpl. do 3 f_equal. lia. }
  { simpl sizeof. rep_lia. }
  Intros rd2. fold (cdaB_mres (Z.max 0 (Zlength c - 16)) rd2).
  forward_if (temp CD._t'11 (Vint (if orb (cdaB_nul d2) (cdaB_nul db) then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite cdaB_cmp by auto. unfold cdaB_nul at 1.
    destruct (eq_dec d2 nullval); [contradiction | reflexivity]. }
  forward_if (temp CD._t'12 (Vint (if orb (orb (cdaB_nul d2) (cdaB_nul db)) (cdaB_nul rd2) then Int.one else Int.zero))).
  { forward. destruct (cdaB_nul d2 || cdaB_nul db)%bool; [entailer! | contradiction H12; reflexivity]. }
  { destruct (cdaB_nul d2 || cdaB_nul db)%bool; [contradiction Int.one_not_zero | ].
    forward. entailer!. rewrite cdaB_cmp by auto. reflexivity. }
  assert_PROP (c2 <> nullval) as Hc2.
  { entailer!. }
  destruct (cdaB_nul d2 || cdaB_nul db || cdaB_nul rd2)%bool eqn:E.
  - forward_if.
    + unfold cdaB_mres. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength c)) (map Vubyte c) c2).
      forward_call (tarray tuchar (Zlength c), c2, gv).
      { destruct (eq_dec c2 nullval); [contradiction |]. cancel. }
      forward_call (tarray tuchar (Z.max 0 (Zlength c - 16)), d2, gv).
      forward_call (tarray tuchar (Z.max 0 (Zlength c - 16)), db, gv).
      forward_call (tarray tuchar (Z.max 0 (Zlength c - 16)), rd2, gv).
      forward. cancel.
    + contradiction Int.one_not_zero.
  - unfold cdaB_mres, cdaB_nul in *.
    destruct (eq_dec d2 nullval); [discriminate |]. destruct (eq_dec db nullval); [discriminate |].
    destruct (eq_dec rd2 nullval); [discriminate |]. simpl orb.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    + contradiction.
    + forward. entailer!.
    + eapply semax_pre; [| apply H9]. unfold cda_P2. entailer!.
Qed.
