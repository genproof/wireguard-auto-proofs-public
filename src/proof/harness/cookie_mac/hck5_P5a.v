(* law cookie_mac: main's phase P5a, statements 52..58 of hck5_cut.v:
   ck_take (v1 P5's first statement) + NEW (v2): hs_take(&hs0, &p.handshake), pr_take(&ps0, &p), refs0 = p.refcount.refcount, dev_take(&da, &wa), dev_take(&db, &wb), shim_take(&ss).
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
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

#[local] Instance hck5_p5a_CCE : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.

Lemma hck5_p5a_refs_nest sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at Noise.CS sh t_peer [StructField I._refcount; StructField I._refcount] (Vint v) p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hck5_p5a_refs_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint v) p.
Proof.
  rewrite hck5_p5a_refs_nest.
  change (Tstruct HK._wg_peer noattr) with t_peer. change HK._refcount with I._refcount.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_cookie_mac _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

Lemma hck5_p5a_fold sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic = peer_rep sh p (p_set_cookie P C).
Proof.
  unfold hck5_prest, peer_rep. destruct P; simpl. apply pred_ext; Intros; entailer!.
Qed.

(* hck5_prest without the reference count *)
Definition hck5_p5a_prestR (sh: share) (p: val) (P: peer) : mpred :=
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hck5_p5a_fold_d sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic |-- hs_mem true sh p (p_set_cookie P C).
Proof. rewrite hck5_p5a_fold. apply derives_refl. Qed.

Lemma hck5_p5a_open sh p P :
  hck5_prest sh p P =
  (hck5_p5a_prestR sh p P *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint (p_refs P)) p)%logic.
Proof.
  rewrite <- hck5_p5a_refs_conv.
  unfold hck5_prest, hck5_p5a_prestR. apply pred_ext; Intros; entailer!.
Qed.

Lemma hck5_p5a_close sh p P :
  (hck5_p5a_prestR sh p P *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint (p_refs P)) p)%logic
  |-- hck5_prest sh p P.
Proof. rewrite hck5_p5a_open. apply derives_refl. Qed.

(* B whole: hck5_drest and the checker fold into device_rep of hck5_DBc *)
Lemma hck5_p5a_dev_fold x25519 R L CC :
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic =
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC).
Proof.
  unfold hck5_drest, device_rep, hck5_DBc. simpl.
  apply pred_ext; entailer!.
Qed.

Lemma hck5_p5a_dev_in x25519 R L CC :
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic |--
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC).
Proof. rewrite hck5_p5a_dev_fold. apply derives_refl. Qed.

Lemma hck5_p5a_dev_out x25519 R L CC :
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC) |--
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic.
Proof. rewrite hck5_p5a_dev_fold. apply derives_refl. Qed.

(* the entry of p's handshake in the pool: its peer is p *)
Lemma hck5_p5a_entry_peer (D: list (val * share * entry)) a p :
  In a (saddrs D) -> Forall (fun x => e_peer (snd x) = p) D ->
  match sfind D a with Some (_, E) => e_peer E = p | None => False end.
Proof.
  induction D as [| [[x sh] E] D IH]; simpl; [tauto |].
  intros HI HF. inversion HF as [| ? ? H1 H2]; clear HF.
  destruct (EqDec_val x a); [exact H1 |].
  apply IH; auto. destruct HI; [congruence | auto].
Qed.

Lemma hck5_p5a_entry_d T a p :
  In a (saddrs (t_D T)) -> Forall (fun x => e_peer (snd x) = p) (t_D T) ->
  e_peer (t_entry_d T a) = p.
Proof.
  intros HI HF. pose proof (hck5_p5a_entry_peer _ _ _ HI HF) as H.
  unfold t_entry_d, t_entry. destruct (sfind (t_D T) a) as [[? E]|]; [exact H | contradiction].
Qed.

Section P5a.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P5a_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S4 x25519 gv L FR) hck5_P5a
    (overridePost (hck5_S5a x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S4, hck5_Delta, hck5_R, hck5_P5a. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps0, hck5_globs, hck5_lvars. cbn [app].
  (* ck_take *)
  forward_call (Tsh, l_cs L, Tsh, cookie_addr (l_p L), C).
  pose proof H0 as (FCp & Hdev & Hpk & Hsid & Hslots & Hkptr & Hsad & Hsh & Hpeer & Hsnap & Hhead).
  assert_PROP (isptr (l_wa L) /\ isptr (l_wb L) /\ isptr (l_p L) /\ isptr (l_pta L) /\ isptr (l_ptb L) /\
               isptr (l_ita L) /\ isptr (l_itb L)) as Hptrs by entailer!.
  destruct Hptrs as (Pwa & Pwb & Pp & Ppta & Pptb & Pita & Pitb).
  Intros.
  (* hs_take(&hs0, &p.handshake): p whole *)
  sep_apply (hck5_p5a_fold_d Tsh (l_p L) (a_P A) C).
  assert (Hin: In (hs_addr (l_p L)) (saddrs (t_D (a_T A)))) by (rewrite Hsad; apply in_app_iff; right; left; auto).
  forward_call (Tsh, l_hs0 L, Tsh, l_p L, p_set_cookie (a_P A) C, true, Tsh, l_ita L, a_T A).
  { split.
    - rewrite (hck5_p5a_entry_d _ _ (l_p L) Hin Hpeer). intro E; rewrite E in Pp; contradiction.
    - simpl. rewrite Hsid. unfold id_addr. destruct (l_wa L); try contradiction. discriminate. }
  (* pr_take(&ps0, &p) *)
  change (hs_mem true Tsh (l_p L) (p_set_cookie (a_P A) C)) with (peer_rep Tsh (l_p L) (p_set_cookie (a_P A) C)).
  forward_call (Tsh, l_ps0 L, Tsh, l_p L, p_set_cookie (a_P A) C).
  { simpl. rewrite Hdev, Hpk.
    assert (Hnu: forall v, v = nullval \/ In v (map ke_addr (a_KE A)) -> v <> Vundef).
    { intros v [-> | Hv]; [discriminate |]. apply list_in_map_inv in Hv. destruct Hv as (e & -> & He).
      rewrite Forall_forall in Hkptr. specialize (Hkptr e He). intro E; rewrite E in Hkptr; contradiction. }
    inversion Hslots as [| ? ? S1 Hs1]; inversion Hs1 as [| ? ? S2 Hs2]; inversion Hs2 as [| ? ? S3 _].
    repeat (apply Forall_cons; [first [apply Hnu; assumption | intro E; rewrite E in Pwa; contradiction | discriminate] |]).
    constructor. }
  (* refs0 = p.refcount.refcount *)
  rewrite <- (hck5_p5a_fold Tsh (l_p L) (a_P A) C).
  rewrite (hck5_p5a_open Tsh (l_p L) (a_P A)). Intros.
  forward.
  sep_apply (hck5_p5a_close Tsh (l_p L) (a_P A)).
  (* dev_take(&da, &wa) *)
  change (ptable Tsh (l_pta L) (l_p L)) with (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)).
  forward_call (Tsh, l_da L, Tsh, l_wa L, hck5_DA x25519 R L, Tsh, l_p L).
  { unfold hck5_DA, setup_dev; simpl.
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction]. }
  change (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)) with (ptable Tsh (l_pta L) (l_p L)).
  (* dev_take(&db, &wb): B whole with the checker CC2 *)
  sep_apply (hck5_p5a_dev_in x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)).
  change (ptable Tsh (l_ptb L) nullval) with (ptable Tsh (d_ptab (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval).
  forward_call (Tsh, l_db L, Tsh, l_wb L, hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode), Tsh, nullval).
  { unfold hck5_DBc, hck5_CC2, hck5_CC1, hck5_DB, setup_dev; simpl.
    destruct (andb _ _); simpl;
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction]. }
  change (ptable Tsh (d_ptab (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval) with (ptable Tsh (l_ptb L) nullval).
  sep_apply (hck5_p5a_dev_out x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)).
  (* shim_take(&ss) *)
  forward_call (gv, Tsh, l_ss L, S, hck5_w0).
  unfold hck5_S5a. Exists R S A m c Q cmode C ck.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr3, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  entailer!.
Qed.

End P5a.
