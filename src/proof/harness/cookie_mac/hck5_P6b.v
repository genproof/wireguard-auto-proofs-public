(* law cookie_mac: main's phase P6b, statements 75..80 of hck5_cut.v:
   NEW (v2): hs_take(&hs0, ..), pr_take(&ps0, &p), dev_take(&da, &wa), dev_take(&db, &wb), skb_take(&sks, &skb), shim_take(&ss).
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

Lemma hck5_p6b_fold sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic = peer_rep sh p (p_set_cookie P C).
Proof.
  unfold hck5_prest, peer_rep. destruct P; simpl. apply pred_ext; Intros; entailer!.
Qed.

Lemma hck5_p6b_fold_d sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic |-- hs_mem true sh p (p_set_cookie P C).
Proof. rewrite hck5_p6b_fold. apply derives_refl. Qed.

(* B whole: hck5_drest and the checker fold into device_rep of hck5_DBc *)
Lemma hck5_p6b_dev_fold x25519 R L CC :
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic =
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC).
Proof.
  unfold hck5_drest, device_rep, hck5_DBc. simpl.
  apply pred_ext; entailer!.
Qed.

Lemma hck5_p6b_dev_in x25519 R L CC :
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic |--
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC).
Proof. rewrite hck5_p6b_dev_fold. apply derives_refl. Qed.

Lemma hck5_p6b_dev_out x25519 R L CC :
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC) |--
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic.
Proof. rewrite hck5_p6b_dev_fold. apply derives_refl. Qed.

(* the entry of p's handshake in the pool: its peer is p *)
Lemma hck5_p6b_entry_peer (D: list (val * share * entry)) a p :
  In a (saddrs D) -> Forall (fun x => e_peer (snd x) = p) D ->
  match sfind D a with Some (_, E) => e_peer E = p | None => False end.
Proof.
  induction D as [| [[x sh] E] D IH]; simpl; [tauto |].
  intros HI HF. inversion HF as [| ? ? H1 H2]; clear HF.
  destruct (EqDec_val x a); [exact H1 |].
  apply IH; auto. destruct HI; [congruence | auto].
Qed.

Lemma hck5_p6b_entry_d T a p :
  In a (saddrs (t_D T)) -> Forall (fun x => e_peer (snd x) = p) (t_D T) ->
  e_peer (t_entry_d T a) = p.
Proof.
  intros HI HF. pose proof (hck5_p6b_entry_peer _ _ _ HI HF) as H.
  unfold t_entry_d, t_entry. destruct (sfind (t_D T) a) as [[? E]|]; [exact H | contradiction].
Qed.

Section P6b.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P6b_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S6a x25519 gv L FR) hck5_P6b
    (overridePost (hck5_S6b x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S6a, hck5_Delta, hck5_R, hck5_P6b. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck.
  Intros MSG1 C1 MSG2 corrupted chk rl.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps0, hck5_globs, hck5_lvars. cbn [app].
  pose proof H0 as (FCp & Hdev & Hpk & Hsid & Hslots & Hkptr & Hsad & Hsh & Hpeer & Hsnap & Hhead).
  assert_PROP (isptr (l_wa L) /\ isptr (l_wb L) /\ isptr (l_p L) /\ isptr (l_pta L) /\ isptr (l_ptb L) /\
               isptr (l_ita L) /\ isptr (l_itb L)) as Hptrs by entailer!.
  destruct Hptrs as (Pwa & Pwb & Pp & Ppta & Pptb & Pita & Pitb).
  assert_PROP (isptr m) as Pm.
  { unfold hbytes. go_lower. saturate_local. apply prop_right.
    match goal with Hf: field_compatible _ _ m |- _ => exact (proj1 Hf) end. }
  (* hs_take(&hs0, &p.handshake): p whole *)
  sep_apply (hck5_p6b_fold_d Tsh (l_p L) (a_P A) C1).
  assert (Hin: In (hs_addr (l_p L)) (saddrs (t_D (a_T A)))) by (rewrite Hsad; apply in_app_iff; right; left; auto).
  forward_call (Tsh, l_hs0 L, Tsh, l_p L, p_set_cookie (a_P A) C1, true, Tsh, l_ita L, a_T A).
  { split.
    - rewrite (hck5_p6b_entry_d _ _ (l_p L) Hin Hpeer). intro E; rewrite E in Pp; contradiction.
    - simpl. rewrite Hsid. unfold id_addr. destruct (l_wa L); try contradiction. discriminate. }
  (* pr_take(&ps0, &p) *)
  change (hs_mem true Tsh (l_p L) (p_set_cookie (a_P A) C1)) with (peer_rep Tsh (l_p L) (p_set_cookie (a_P A) C1)).
  forward_call (Tsh, l_ps0 L, Tsh, l_p L, p_set_cookie (a_P A) C1).
  { simpl. rewrite Hdev, Hpk.
    assert (Hnu: forall v, v = nullval \/ In v (map ke_addr (a_KE A)) -> v <> Vundef).
    { intros v [-> | Hv]; [discriminate |]. apply list_in_map_inv in Hv. destruct Hv as (e & -> & He).
      rewrite Forall_forall in Hkptr. specialize (Hkptr e He). intro E; rewrite E in Hkptr; contradiction. }
    inversion Hslots as [| ? ? S1 Hs1]; inversion Hs1 as [| ? ? S2 Hs2]; inversion Hs2 as [| ? ? S3 _].
    repeat (apply Forall_cons; [first [apply Hnu; assumption | intro E; rewrite E in Pwa; contradiction | discriminate] |]).
    constructor. }
  rewrite <- (hck5_p6b_fold Tsh (l_p L) (a_P A) C1).
  (* dev_take(&da, &wa) *)
  change (ptable Tsh (l_pta L) (l_p L)) with (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)).
  forward_call (Tsh, l_da L, Tsh, l_wa L, hck5_DA x25519 R L, Tsh, l_p L).
  { unfold hck5_DA, setup_dev; simpl.
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction]. }
  change (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)) with (ptable Tsh (l_pta L) (l_p L)).
  (* dev_take(&db, &wb): B whole with the checker CC2 *)
  sep_apply (hck5_p6b_dev_in x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)).
  change (ptable Tsh (l_ptb L) nullval) with (ptable Tsh (d_ptab (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval).
  forward_call (Tsh, l_db L, Tsh, l_wb L, hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode), Tsh, nullval).
  { unfold hck5_DBc, hck5_CC2, hck5_CC1, hck5_DB, setup_dev; simpl.
    destruct (andb _ _); simpl;
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction]. }
  change (ptable Tsh (d_ptab (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval) with (ptable Tsh (l_ptb L) nullval).
  sep_apply (hck5_p6b_dev_out x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)).
  (* skb_take(&sks, &skb) *)
  forward_call (Tsh, l_sks L, Tsh, l_skb L, hck5_skb Q m).
  { match goal with E: sk_data _ = Vundef |- _ => simpl in E; rewrite E in Pm; contradiction end. }
  (* shim_take(&ss) *)
  forward_call (gv, Tsh, l_ss L, S, hck5_w0).
  unfold hck5_S6b. Exists R S A m c Q cmode C ck. Exists MSG1 C1 MSG2 corrupted chk rl.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  entailer!.
Qed.

End P6b.
