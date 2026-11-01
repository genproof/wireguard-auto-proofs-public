(* law handshake, phase P3, segment D, part: NEG (!acc1: CHECK(ret == NULL && hs_same(&snap, &pa.handshake) && refcount == 1)).
*)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.

#[local] Instance hhs3_p3_D_neg_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Local Open Scope Z_scope.

Lemma hhs3_p3_D_neg_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hhs3_p3_D_neg_snap_refl sn : snap_eqb sn sn = true.
Proof.
  destruct sn as [[ep et ei] nx hd [st lic sid eph rs reph ss psk h ck ts ri]].
  unfold snap_eqb, entry_eqb, hs_eqb; cbn [sn_entry sn_next sn_hashed sn_hs e_peer e_type e_index
    hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  rewrite !if_true by auto. rewrite !Int.eq_true, Int64.eq_true, !hhs3_p3_D_neg_eqb_refl.
  destruct hd; reflexivity.
Qed.

Lemma hhs3_p3_D_neg_sfind1 {A: Type} a sh (v: A) : sfind [(a, sh, v)] a = Some (sh, v).
Proof. simpl. rewrite if_true by auto. reflexivity. Qed.

Lemma hhs3_p3_D_neg_cmp x25519 R L :
  hs_cmp_pre (hhs3_p3_snap x25519 R L) (hhs3_TB0 L) (l_pa L) (l_wb L) (hhs3_PA0 x25519 R L) (hhs3_EA L).
Proof.
  unfold hs_cmp_pre, hhs3_p3_snap, snap_of. cbn [sn_entry sn_hs sn_next].
  split; [| split; [| split; [| split; [| split]]]].
  - unfold t_entry, hhs3_TB0. cbn [t_D]. rewrite hhs3_p3_D_neg_sfind1. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - left. reflexivity.
Qed.

Local Open Scope logic.

(* the reference count of a peer, at the world's compspecs *)
Lemma hhs3_p3_D_neg_refs sh p r :
  peer_refs_rep sh p r = @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint r) p.
Proof.
  unfold peer_refs_rep.
  assert (Hc: cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p3_D_neg_CCE) t_peer = true) by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_handshake hhs3_p3_D_neg_CCE sh t_peer [StructField I._refcount]
                 (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep without its device field and its reference count *)
Definition hhs3_p3_D_neg_rest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hhs3_p3_D_neg_split sh p P :
  peer_rep sh p P =
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint (p_refs P)) p *
   hhs3_p3_D_neg_rest sh p P).
Proof.
  rewrite <- hhs3_p3_D_neg_refs. unfold peer_rep, hhs3_p3_D_neg_rest, peer_refs_rep.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Local Open Scope Z_scope.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_D_neg_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p3_D_N x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb)
    hhs3_p3_D_neg
    (overridePost (hhs3_p3_D_N x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p3_D_N, hhs3_Delta, hhs3_p3_D_neg.
  simplify_func_tycontext.
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  abbreviate_semax.
  Intros.
  assert (Hcmp := hhs3_p3_D_neg_cmp x25519 R L).
  assert (Er: p_refs (hhs3_PA0 x25519 R L) = Int.one) by reflexivity.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'73 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Tsh, l_snap L, hhs3_p3_snap x25519 R L, Tsh, l_pa L, hhs3_PA0 x25519 R L,
                    Tsh, l_itb L, hhs3_TB0 L, hhs3_EA L, Tsh, l_wb L, hhs3_DB x25519 R L).
      change (snap_of (hhs3_TB0 L) (hs_addr (l_pa L)) (hhs3_EA L) (p_hs (hhs3_PA0 x25519 R L)))
        with (hhs3_p3_snap x25519 R L).
      rewrite hhs3_p3_D_neg_snap_refl. forward. entailer!. }
    { exfalso. auto. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'75 (Vint Int.one) :: Q) (SEPx R))) end.
    { rewrite (hhs3_p3_D_neg_split Tsh (l_pa L) (hhs3_PA0 x25519 R L)). Intros.
      rewrite Er. forward. forward. entailer!.
      rewrite (hhs3_p3_D_neg_split Tsh (l_pa L) (hhs3_PA0 x25519 R L)), Er. entailer!. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!.
Qed.

End Part.
