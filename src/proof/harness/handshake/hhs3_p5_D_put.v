(* law handshake, phase P5, segment D, part put: POS ck1 + put (CHECK(ret == &pb && refcount == 2); wg_peer_put(ret)).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.

#[local] Instance hhs3_p5_D_put_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Local Open Scope logic.

(* the reference count of a peer, at the world's compspecs *)
Lemma hhs3_p5_D_put_refs sh p r :
  peer_refs_rep sh p r = @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint r) p.
Proof.
  unfold peer_refs_rep.
  assert (Hc: cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p5_D_put_CCE) t_peer = true) by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_handshake hhs3_p5_D_put_CCE sh t_peer [StructField I._refcount]
                 (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep without its device field and its reference count *)
Definition hhs3_p5_D_put_rest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hhs3_p5_D_put_open sh p P :
  peer_rep sh p P |--
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint (p_refs P)) p *
   hhs3_p5_D_put_rest sh p P).
Proof.
  rewrite <- hhs3_p5_D_put_refs. unfold peer_rep, hhs3_p5_D_put_rest, peer_refs_rep.
  Intros. apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma hhs3_p5_D_put_split sh p P :
  peer_rep sh p P =
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint (p_refs P)) p *
   hhs3_p5_D_put_rest sh p P).
Proof.
  rewrite <- hhs3_p5_D_put_refs. unfold peer_rep, hhs3_p5_D_put_rest, peer_refs_rep.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hhs3_p5_D_put_fold sh p P r :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint r) p *
  hhs3_p5_D_put_rest sh p P |-- peer_rep sh p (p_set_refs P r).
Proof.
  intros Hfc. rewrite <- hhs3_p5_D_put_refs. unfold peer_rep, hhs3_p5_D_put_rest, peer_refs_rep.
  cbn [p_set_refs p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma hhs3_p5_D_put_putpre sh p d r : p <> nullval ->
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p *
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint r) p |--
  (if eq_dec p nullval then emp
   else (peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p)).
Proof. intros Hp. rewrite if_false by exact Hp. rewrite hhs3_p5_D_put_refs. cancel. Qed.

Lemma hhs3_p5_D_put_putpost sh p d r : p <> nullval ->
  (if eq_dec p nullval then emp
   else (peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p)) |--
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p *
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint r) p.
Proof. intros Hp. rewrite if_false by exact Hp. rewrite hhs3_p5_D_put_refs. cancel. Qed.

Lemma hhs3_p5_D_put_vp sh d p : sepalg.nonidentity sh ->
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p * TT |-- valid_pointer p.
Proof.
  intros Hsh. apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; vm_compute; reflexivity.
Qed.

Lemma hhs3_p5_D_put_new x25519 R L M1 H1 M2 ST2 :
  p_refs (hhs3_p5_new x25519 R L M1 H1 M2 ST2) = Int.repr 2 /\
  p_device (hhs3_p5_new x25519 R L M1 H1 M2 ST2) = p_device (hhs3_PB1 x25519 R L M1 H1).
Proof. destruct ST2. split; reflexivity. Qed.

Local Open Scope Z_scope.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_D_put_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2 (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p5_D_P0 x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2)
    (Ssequence hhs3_p5_D_ck1 hhs3_p5_D_put)
    (overridePost (hhs3_p5_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p5_D_P0, hhs3_p5_D_Q, hhs3_p5_D_st, hhs3_Delta, hhs3_p5_D_ck1, hhs3_p5_D_put.
  simplify_func_tycontext.
  destruct (hhs3_p5_D_put_new x25519 R L M1 H1 M2 ST2) as [Er Ed].
  set (P := hhs3_p5_new x25519 R L M1 H1 M2 ST2) in *.
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  abbreviate_semax.
  Intros.
  rewrite (hhs3_p5_D_put_split Tsh (l_pb L) P). Intros.
  match goal with Hx: @field_compatible Noise.CS t_peer [] (l_pb L) |- _ => rename Hx into Hfc end.
  assert (Hpn: l_pb L <> nullval) by (intros E; rewrite E in Hfc; exact (field_compatible_isptr _ _ _ Hfc)).
  rewrite Er.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HC._t'141 (Vint Int.one) :: Q) (SEPx R))) end.
      * entailer!. apply denote_tc_test_eq_split;
          (eapply derives_trans; [| apply (hhs3_p5_D_put_vp Tsh (p_device P) (l_pb L)); auto]); cancel.
      * forward. forward. entailer!.
      * exfalso. auto.
      * forward_if.
        { forward_call tt. all: first [ match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
        forward. entailer!.
  + forward. apply ENTAIL_refl.
  + sep_apply (hhs3_p5_D_put_putpre Tsh (l_pb L) (p_device P) (Int.repr 2) Hpn).
    forward_call (gv, S, Tsh, l_pb L, Int.repr 2, p_device P).
    sep_apply (hhs3_p5_D_put_putpost Tsh (l_pb L) (p_device P) (rc_sub1 (Int.repr 2)) Hpn).
    rewrite if_false by exact Hpn.
    change (if Int.eq (rc_sub1 (Int.repr 2)) Int.zero then shim_release S else S) with S.
    change (rc_sub1 (Int.repr 2)) with Int.one.
    sep_apply (hhs3_p5_D_put_fold Tsh (l_pb L) P Int.one Hfc).
    entailer!.
Qed.

End Part.
