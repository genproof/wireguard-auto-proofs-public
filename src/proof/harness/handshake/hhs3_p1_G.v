(* law handshake: main's phase P1, segment G = statements 33..36: the two mallocs (NULL: free both, return 0), all_ok.
   (section P1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* a malloc result: NULL, or a token and an uninitialised object of type t (the world's compspecs) *)
Definition hhs3G_mres (t: type) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)%logic.
Definition hhs3G_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma hhs3G_mres_valid (t: type) (p: val) : sizeof t > 0 -> hhs3G_mres t p |-- valid_pointer p.
Proof.
  intros Ht. unfold hhs3G_mres. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
Qed.

Lemma hhs3G_mres_local (t: type) (p: val) : hhs3G_mres t p |-- !! is_pointer_or_null p.
Proof.
  unfold hhs3G_mres. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

Lemma hhs3G_cmp (p: val) : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if hhs3G_nul p then Int.one else Int.zero).
Proof.
  intros Hp. unfold hhs3G_nul. destruct (eq_dec p nullval) as [-> | Hn]; [reflexivity |].
  destruct p; try contradiction; simpl in Hp.
  - subst. contradiction Hn. reflexivity.
  - reflexivity.
Qed.

Lemma hhs3G_init_valid p : hhs3G_mres t_init p |-- valid_pointer p.
Proof. apply hhs3G_mres_valid. simpl. lia. Qed.
Lemma hhs3G_resp_valid p : hhs3G_mres t_resp p |-- valid_pointer p.
Proof. apply hhs3G_mres_valid. simpl. lia. Qed.

#[local] Instance hhs3G_cce_H : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

(* the harness's identity struct at the world's compspecs (for main's loads of .ok) *)
Lemma hhs3G_mid_conv sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_handshake sh t_mident (mident_val I) p.
Proof. apply equal_f, (@data_at_change_composite HCS W_handshake _ sh t_mident); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

#[local] Hint Resolve hhs3G_init_valid hhs3G_resp_valid : valid_pointer.
#[local] Hint Resolve hhs3G_mres_local : saturate_local.

(* the end of G: back to S1 (the identities at HCS, the messages at Noise.CS) *)
Ltac hhs3G_fin R S m1 m2 a0 f0 l0 :=
  rewrite <- !hhs3G_mid_conv; unfold hhs3_S1; Exists R S m1 m2 a0 f0 l0;
  unfold hhs3_globs, hhs3_setup_sep, hhs3_scr_tmp, hhs3_lvars, hhs3_cnt_temps, hhs3_tok; simpl app;
  rewrite <- hhs3_conv_init, <- hhs3_conv_resp; entailer!.

Lemma hhs3_p1_G_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p1_free_stmt x25519 ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p1_SE x25519 gv L FR) hhs3_p1_G
    (overridePost (hhs3_S1 x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH Hfree. apply hhs3_post_canon.
  unfold hhs3_p1_SE, hhs3_Delta, hhs3_R, hhs3_p1_G. simplify_func_tycontext. abbreviate_semax.
  Intros R S a0 f0 l0.
  unfold hhs3_p1_SEsep, hhs3_globs, hhs3_setup_sep, hhs3_p1_rest, hhs3_scr_tmp, hhs3_lvars, hhs3_cnt_temps. simpl app.
  forward_call (t_init, gv).
  Intros m1. fold (hhs3G_mres t_init m1).
  forward_call (t_resp, gv).
  Intros m2. fold (hhs3G_mres t_resp m2).
  forward_if (temp HC._t'20 (Vint (if orb (hhs3G_nul m1) (hhs3G_nul m2) then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite hhs3G_cmp by auto. unfold hhs3G_nul at 1.
    destruct (eq_dec m1 nullval); [contradiction | reflexivity]. }
  destruct (hhs3G_nul m1 || hhs3G_nul m2)%bool eqn:E.
  - forward_if.
    + unfold hhs3G_mres.
      forward_call (t_init, m1, gv).
      forward_call (t_resp, m2, gv).
      forward.
      assert (Hf := Hfree (proj1 HH) gv L FR R S H).
      unfold hhs3_p1_SEsep, hhs3_p1_frame, hhs3_globs, hhs3_setup_sep, hhs3_p1_rest, hhs3_scr_tmp in Hf.
      simpl app in Hf. simpl fold_right_sepcon in Hf. rewrite !sepcon_emp in Hf.
      sep_apply Hf. cancel.
    + contradiction Int.one_not_zero.
  - unfold hhs3G_mres, hhs3G_nul in *.
    destruct (eq_dec m1 nullval); [discriminate |]. destruct (eq_dec m2 nullval); [discriminate |].
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    + contradiction.
    + forward. entailer!.
    + Intros. rewrite !hhs3G_mid_conv.
      forward.
      match goal with |- context [temp HC._t'308 ?v] =>
        replace v with (Vint (if mi_ok (hhs3_IA x25519 R) then Int.one else Int.zero)) by reflexivity end.
      destruct (mi_ok (hhs3_IA x25519 R)) eqn:EA.
      * forward_if (temp HC._t'21 (Vint (if hhs3_ok1 x25519 R then Int.one else Int.zero))).
        ** forward.
           match goal with |- context [temp HC._t'309 ?v] =>
             replace v with (Vint (if mi_ok (hhs3_IB x25519 R) then Int.one else Int.zero)) by reflexivity end.
           forward. entailer!. unfold hhs3_ok1. rewrite EA. destruct (mi_ok (hhs3_IB x25519 R)); reflexivity.
        ** contradiction Int.one_not_zero.
        ** forward. hhs3G_fin R S m1 m2 a0 f0 l0.
      * forward_if (temp HC._t'21 (Vint (if hhs3_ok1 x25519 R then Int.one else Int.zero))).
        ** contradiction.
        ** forward. entailer!. unfold hhs3_ok1. rewrite EA. reflexivity.
        ** forward. hhs3G_fin R S m1 m2 a0 f0 l0.
Qed.

End Seg.
