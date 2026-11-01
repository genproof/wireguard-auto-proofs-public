
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.data_header.dh4_spec.
Require Import WgNoise.proof.harness.transport_len.htl5_defs.
Require WgNoise.harness.x_transport_len.code.

#[local] Existing Instance W_transport_len.
Local Open Scope Z_scope.

(* a malloc result: NULL, or a token and an uninitialised buffer of n bytes *)
Definition htl5E_mres (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.
Definition htl5E_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma htl5E_mres_valid (n: Z) (p: val) : htl5E_mres n p |-- valid_pointer p.
Proof.
  unfold htl5E_mres. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
      simpl. rewrite Z.max_r by lia. lia.
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

Lemma htl5E_mres_local (n: Z) (p: val) : htl5E_mres n p |-- !! is_pointer_or_null p.
Proof.
  unfold htl5E_mres. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

Lemma htl5E_cmp (p: val) : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if htl5E_nul p then Int.one else Int.zero).
Proof.
  intros Hp. unfold htl5E_nul. destruct (eq_dec p nullval) as [-> | Hn]; [reflexivity |].
  destruct p; try contradiction; simpl in Hp.
  - subst. contradiction Hn. reflexivity.
  - reflexivity.
Qed.

#[local] Hint Resolve htl5E_mres_valid : valid_pointer.
#[local] Hint Resolve htl5E_mres_local : saturate_local.

Lemma htl5_segE_ok {Espec: OracleKind} gv vk FR :
  semax htl5_Delta (htl5_PD gv vk FR) htl5_segE (overridePost (htl5_PE gv vk FR) (htl5_R gv)).
Proof.
  unfold htl5_PD. Intros key nonce tot pkt pk au.
  unfold htl5_Delta, htl5_segE, htl5_R. apply htl5_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  match goal with H: htl5_ranges _ _ _ |- _ => pose proof H as Hr; destruct H as (Hk & Hno & Htot) end.
  unfold htl5_lv, htl5_buf. simpl app.
  forward_call (tarray tuchar (tot - 32), gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros pto. fold (htl5E_mres (tot - 32) pto).
  forward_call (tarray tuchar (tot - 32), gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros rpt. fold (htl5E_mres (tot - 32) rpt).
  forward_if (temp TLC._t'20 (Vint (if orb (htl5E_nul pto) (htl5E_nul rpt) then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite htl5E_cmp by auto. unfold htl5E_nul at 1.
    destruct (eq_dec pto nullval); [contradiction | reflexivity]. }
  destruct (htl5E_nul pto || htl5E_nul rpt)%bool eqn:E.
  - forward_if.
    + assert_PROP (isptr pkt) as Pp by entailer!.
      forward_call (tarray tuchar tot, pkt, gv).
      { rewrite if_false by (intro; subst; contradiction).
        sep_apply (data_at_data_at_ Ews (tarray tuchar tot) (map Vubyte pk) pkt). cancel. }
      unfold htl5E_mres.
      forward_call (tarray tuchar (tot - 32), pto, gv).
      forward_call (tarray tuchar (tot - 32), rpt, gv).
      forward.
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk). cancel.
    + contradiction Int.one_not_zero.
  - unfold htl5E_mres, htl5E_nul in *.
    destruct (eq_dec pto nullval); [discriminate |]. destruct (eq_dec rpt nullval); [discriminate |].
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    + contradiction.
    + forward. entailer!.
    + unfold htl5_PE. Exists key nonce tot pkt pk au pto rpt.
      unfold htl5_lv, htl5_buf. simpl app. entailer!.
Qed.
