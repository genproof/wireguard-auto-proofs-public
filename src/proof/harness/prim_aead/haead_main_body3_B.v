(* law prim_aead: main of prim_aead.h, segment B (statements 9..16: the seven mallocs and the NULL test (frees + return)); main.
*)
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
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_defs.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

(* a malloc result: NULL, or a token and an uninitialised buffer of n bytes *)
Definition hm3B_mres (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.
Definition hm3B_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma hm3B_mres_valid (n: Z) (p: val) : hm3B_mres n p |-- valid_pointer p.
Proof.
  unfold hm3B_mres. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
      simpl. rewrite Z.max_r by lia. lia.
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

Lemma hm3B_mres_local (n: Z) (p: val) : hm3B_mres n p |-- !! is_pointer_or_null p.
Proof.
  unfold hm3B_mres. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

Lemma hm3B_cmp (p: val) : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if hm3B_nul p then Int.one else Int.zero).
Proof.
  intros Hp. unfold hm3B_nul. destruct (eq_dec p nullval) as [-> | Hn]; [reflexivity |].
  destruct p; try contradiction; simpl in Hp.
  - subst. contradiction Hn. reflexivity.
  - reflexivity.
Qed.

#[local] Hint Resolve hm3B_mres_valid : valid_pointer.
#[local] Hint Resolve hm3B_mres_local : saturate_local.

Lemma hm3_segB_ok {Espec: OracleKind} gv vk vxn FR :
  semax hm3_Delta (hm3_PA gv vk vxn FR) hm3_segB (overridePost (hm3_PB gv vk vxn FR) (hm3_R gv)).
Proof.
  unfold hm3_PA. Intros x key nonce xn adlen n.
  unfold hm3_Delta, hm3_segB, hm3_R. apply hm3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  match goal with H: hm3_ranges _ _ _ _ _ _ |- _ => pose proof H as Hr; destruct H as (Hx & Hk & Hno & Hxn & Had & Hn) end.
  unfold hm3_tA, hm3_lv. simpl app.
  forward_call (tarray tuchar adlen, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros ad. fold (hm3B_mres adlen ad).
  forward_call (tarray tuchar adlen, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros ad_copy. fold (hm3B_mres adlen ad_copy).
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros pt. fold (hm3B_mres n pt).
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros pt_copy. fold (hm3B_mres n pt_copy).
  forward_call (tarray tuchar (n + 16), gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros ct. fold (hm3B_mres (n + 16) ct).
  forward_call (tarray tuchar (n + 16), gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros rct. fold (hm3B_mres (n + 16) rct).
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros dec. fold (hm3B_mres n dec).
  forward_if (temp HAC._t'14 (Vint (if orb (hm3B_nul ad) (hm3B_nul ad_copy) then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite hm3B_cmp by auto. unfold hm3B_nul at 1.
    destruct (eq_dec ad nullval); [contradiction | reflexivity]. }
  forward_if (temp HAC._t'15 (Vint (if orb (orb (hm3B_nul ad) (hm3B_nul ad_copy))
                                             (orb (orb (hm3B_nul pt) (hm3B_nul pt_copy)) (hm3B_nul dec)) then Int.one else Int.zero))).
  { forward. destruct (hm3B_nul ad || hm3B_nul ad_copy)%bool; [entailer! | contradiction H; reflexivity]. }
  { destruct (hm3B_nul ad || hm3B_nul ad_copy)%bool; [contradiction Int.one_not_zero |]. simpl orb.
    forward_if (temp HAC._t'16 (Vint (if orb (hm3B_nul pt) (hm3B_nul pt_copy) then Int.one else Int.zero))).
    { forward. entailer!. }
    { forward. entailer!. rewrite hm3B_cmp by auto. unfold hm3B_nul at 1.
      destruct (eq_dec pt nullval); [contradiction | reflexivity]. }
    forward_if (temp HAC._t'15 (Vint (if orb (orb (hm3B_nul pt) (hm3B_nul pt_copy)) (hm3B_nul dec) then Int.one else Int.zero))).
    { forward. destruct (hm3B_nul pt || hm3B_nul pt_copy)%bool; [entailer! | contradiction H0; reflexivity]. }
    { destruct (hm3B_nul pt || hm3B_nul pt_copy)%bool; [contradiction Int.one_not_zero |].
      forward. forward. entailer!. rewrite hm3B_cmp by auto. simpl orb.
      destruct (hm3B_nul dec); reflexivity. }
    entailer!. }
  set (b15 := (hm3B_nul ad || hm3B_nul ad_copy || (hm3B_nul pt || hm3B_nul pt_copy || hm3B_nul dec))%bool).
  forward_if (temp HAC._t'17 (Vint (if orb b15 (hm3B_nul ct) then Int.one else Int.zero))).
  { forward. destruct b15; [entailer! | contradiction H; reflexivity]. }
  { destruct b15; [contradiction Int.one_not_zero |].
    forward. entailer!. rewrite hm3B_cmp by auto. reflexivity. }
  forward_if (temp HAC._t'18 (Vint (if orb (orb b15 (hm3B_nul ct)) (hm3B_nul rct) then Int.one else Int.zero))).
  { forward. destruct (b15 || hm3B_nul ct)%bool; [entailer! | contradiction H; reflexivity]. }
  { destruct (b15 || hm3B_nul ct)%bool; [contradiction Int.one_not_zero |].
    forward. entailer!. rewrite hm3B_cmp by auto. reflexivity. }
  destruct (b15 || hm3B_nul ct || hm3B_nul rct)%bool eqn:E.
  - forward_if.
    + unfold hm3B_mres.
      forward_call (tarray tuchar adlen, ad, gv).
      forward_call (tarray tuchar adlen, ad_copy, gv).
      forward_call (tarray tuchar n, pt, gv).
      forward_call (tarray tuchar n, pt_copy, gv).
      forward_call (tarray tuchar (n + 16), ct, gv).
      forward_call (tarray tuchar (n + 16), rct, gv).
      forward_call (tarray tuchar n, dec, gv).
      forward.
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk).
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 24) (map Vubyte xn) vxn). cancel.
    + contradiction Int.one_not_zero.
  - subst b15. unfold hm3B_mres, hm3B_nul in *.
    destruct (eq_dec ad nullval); [discriminate |]. destruct (eq_dec ad_copy nullval); [discriminate |].
    destruct (eq_dec pt nullval); [discriminate |]. destruct (eq_dec pt_copy nullval); [discriminate |].
    destruct (eq_dec dec nullval); [discriminate |]. destruct (eq_dec ct nullval); [discriminate |].
    destruct (eq_dec rct nullval); [discriminate |]. simpl orb.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    + contradiction.
    + forward. entailer!.
    + unfold hm3_PB. Exists x key nonce xn adlen n ad ad_copy pt pt_copy ct rct dec.
      unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf. simpl app. entailer!.
Qed.
