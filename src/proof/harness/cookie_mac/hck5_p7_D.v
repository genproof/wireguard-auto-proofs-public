(* law cookie_mac, phase P7, segment D: s86 = CHECK(bytes_eq(msg, copy, len) && skb.data == msg && skb.len == len): T2 -> S7 (v1 hck3_p7_D.v.old; its Qed trap fix).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_lemmas.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

#[local] Instance hck5_p7_D_cce : change_composite_env Cookie.CS W_cookie_mac.
Proof. make_cs_preserve Cookie.CS W_cookie_mac. Defined.

Lemma hck5_p7_D_skb sh p s :
  skb_rep sh p s = !! skb_ok s && @data_at W_cookie_mac sh t_skb (@skb_val s) p.
Proof.
  unfold skb_rep. f_equal.
  erewrite (@data_at_change_composite Cookie.CS W_cookie_mac _ sh t_skb _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  reflexivity.
Qed.

(* the two fields main loads (data, len), at the world, and the rest as an opaque wand (v1's Qed-trap fix) *)
Definition hck5_p7_D_fa (sh: share) (p: val) (s: skb) : mpred :=
  (@field_at W_cookie_mac sh t_skb (DOT HK._data) (sk_data s) p *
  @field_at W_cookie_mac sh t_skb (DOT HK._len) (Vint (sk_len s)) p)%logic.

Lemma hck5_p7_D_open sh p s :
  skb_rep sh p s |--
  !! skb_ok s && (@field_at W_cookie_mac sh t_skb (DOT HK._data) (sk_data s) p *
                  @field_at W_cookie_mac sh t_skb (DOT HK._len) (Vint (sk_len s)) p *
                  (hck5_p7_D_fa sh p s -* skb_rep sh p s))%logic.
Proof.
  rewrite hck5_p7_D_skb. Intros. apply andp_right; [apply prop_right; auto |].
  unfold_data_at (@data_at W_cookie_mac _ _ _ p).
  change (fst (skb_val s)) with (sk_data s). change (fst (snd (skb_val s))) with (Vint (sk_len s)).
  match goal with |- (?A * (?B * ?R))%logic |-- _ =>
    apply derives_trans with ((A * B) * R)%logic; [rewrite sepcon_assoc; apply derives_refl | ] end.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. unfold hck5_p7_D_fa. apply andp_right; [apply prop_right; auto |]. cancel.
Qed.

Lemma hck5_p7_D_close sh p s d l : d = sk_data s -> l = sk_len s ->
  (@field_at W_cookie_mac sh t_skb (DOT HK._data) d p *
   @field_at W_cookie_mac sh t_skb (DOT HK._len) (Vint l) p *
   (hck5_p7_D_fa sh p s -* skb_rep sh p s) |-- skb_rep sh p s)%logic.
Proof. intros -> ->. fold (hck5_p7_D_fa sh p s). apply modus_ponens_wand. Qed.

Section P7D.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_D_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_T2 x25519 gv L FR) hck5_p7_s86
    (overridePost (hck5_S7 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_T2, hck5_Delta, hck5_R, hck5_p7_s86. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck. Intros MSG1 C1 MSG2 corrupted chk rl r VR.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  pose proof H6 as (HM2 & HL2 & Hr & HVR & HB & HRL & HROT).
  sep_apply (hck5_p7_D_open Tsh (l_skb L) (hck5_skb Q m)). Intros.
  change (sk_data (hck5_skb Q m)) with m. change (sk_len (hck5_skb Q m)) with (Int.repr (q_n Q)).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { entailer!. }
  { forward_call (Ews, m, MSG2, Ews, c, MSG2).
    { rewrite HL2. entailer!. }
    { rewrite HL2. destruct H1 as [[? ?] _]. rep_lia. }
    rewrite hck5_p7_eqb_refl.
    forward_if (temp HK._t'77 (Vint Int.one)).
    { forward. unfold hbytes. forward.
      { entailer!.
        match goal with Hf: field_compatible (Tarray tuchar _ noattr) [] m |- _ => destruct Hf as [Hpm _] end. destruct m; try contradiction.
        apply denote_tc_test_eq_split;
          assert (0 < Zlength MSG2) by (rewrite HL2; destruct H1 as [[? ?] _]; rep_lia);
          repeat apply sepcon_valid_pointer1; apply data_at_valid_ptr; auto; simpl; rep_lia. }
      entailer!.
      match goal with Hf: field_compatible (Tarray tuchar _ noattr) [] m |- _ => destruct Hf as [Hpm _] end. destruct m; try contradiction. unfold sem_cmp_pp; simpl.
      rewrite if_true by auto. rewrite Ptrofs.eq_true. reflexivity. }
    { exfalso. revert H8. discriminate. }
    forward_if (temp HK._t'78 (Vint Int.one)).
    { forward. forward. entailer!.
      rewrite Int.unsigned_repr by (destruct H1 as [[? ?] _]; rep_lia). unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
    { exfalso. revert H8. discriminate. }
    forward_if. { exfalso. revert H8. simpl. discriminate. } forward. entailer!. }
  { forward. entailer!. }
  unfold POSTCONDITION, abbreviate.
  match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
  unfold hck5_S7. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists chk rl r VR.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  sep_apply (hck5_p7_D_close Tsh (l_skb L) (hck5_skb Q m) m (Int.repr (q_n Q)) eq_refl eq_refl).
  entailer!.
Qed.

End P7D.
