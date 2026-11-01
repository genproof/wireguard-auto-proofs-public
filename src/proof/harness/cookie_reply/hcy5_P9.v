(* law cookie_reply: phase P9 of main, statements
   53..56: mode, honest, the mode block (B's reply to P, optionally changed / any 64 bytes), cookie_img(img).

   (+ its children's files). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_BA1.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_BA2a.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_BA2b.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_BA3.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_BB.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* a node of the list is a valid pointer *)
Lemma hcy5_p9_node_valid NS : forall l a, In a (map hn_addr NS) -> hnodes_rep4 W l NS |-- valid_pointer a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

(* s50; s51: mode = nondet_u8() % 3; honest = 0 *)
Lemma hcy5_p9_s5354_ok {Espec: OracleKind} gv L FR R S m c rp Q rr CK CM NS PS T np CL KE :
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (PROPx [] (LOCALx (hcy5_p9_loc gv L m c rp Q np CL KE [])
      (SEPx (hcy5_p9_sep x25519 gv L FR R S m c rp Q rr CK NS PS T CL KE CM (hout Tsh 64 (l_img L))))))
    (Ssequence hcy5_p9_s53 hcy5_p9_s54)
    (normal_ret_assert (EX md: Z, !! (0 <= md < 3) &&
       hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])).
Proof.
  unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_s53, hcy5_p9_s54.
  simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; simpl app.
  forward_call tt. Intros b.
  forward.
  { entailer!. match goal with H: _ /\ Int.repr 3 = Int.mone |- _ => destruct H as [_ Hc]; discriminate end. }
  forward.
  Exists (b mod 3).
  assert (Hm: Int.mods (Int.repr b) (Int.repr 3) = Int.repr (b mod 3)).
  { unfold Int.mods. rewrite !Int.signed_repr by (unfold Byte.max_unsigned in *; rep_lia).
    rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Hm.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  entailer!. apply Z.mod_pos_bound. lia.
Qed.

(* t'46 = mode != 2 && np != NULL *)
Definition hcy5_p9_vc (md: Z) (np: val) : int :=
  if Z.eq_dec md 2 then Int.zero else if eq_dec np nullval then Int.zero else Int.one.

Lemma hcy5_p9_tc_ok {Espec: OracleKind} gv L FR R S m c rp Q rr CK CM NS PS T np CL KE md :
  0 <= md < 3 -> (np = nullval \/ In np (map hn_addr NS)) ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])
    hcy5_p9_tc
    (normal_ret_assert
       (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md []
          [temp HY._t'44 (Vint (hcy5_p9_vc md np))])).
Proof.
  intros Hmd Hnp.
  unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_tc,
    hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  simplify_func_tycontext. abbreviate_semax.
  forward_if.
  - forward.
    { destruct Hnp as [-> | Hin]; [entailer! |].
      entailer!. pull_left (hnodes_rep4 W (hcy5_head NS) NS).
      apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      repeat apply sepcon_valid_pointer1. apply hcy5_p9_node_valid; exact Hin. }
    entailer!. unfold hcy5_p9_vc. destruct (Z.eq_dec md 2); [contradiction |].
    destruct (eq_dec np nullval) as [-> | Hn]; [reflexivity |].
    destruct np; try contradiction; [simpl in PNnp; subst; contradiction Hn; reflexivity | reflexivity].
  - forward. entailer!.
Qed.

(* s52: the dispatch (the branches as hypotheses) *)
Lemma hcy5_p9_M_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE md :
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE -> 0 <= md < 3 ->
  (md <> 2 -> np <> nullval ->
   semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
     (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])
     hcy5_p9_BA (normal_ret_assert (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE))) ->
  (md = 2 ->
   semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
     (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])
     hcy5_p9_BB (normal_ret_assert (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE))) ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])
    hcy5_p9_s55 (normal_ret_assert (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE)).
Proof.
  intros Hinv Hmd HA HB.
  pose proof Hinv as (Hr & Hl & Hnpok & HT & Hcl & Hcn).
  assert (Hnp: np = nullval \/ In np (map hn_addr NS)).
  { destruct Hnpok as [-> | (N & a & P & HIn & HN & _)]; [left; auto | right].
    subst np. apply in_map. apply in_combine_l in HIn. exact HIn. }
  rewrite hcy5_p9_s55_eq.
  eapply hcy5_p9_seq; [apply (hcy5_p9_tc_ok gv L FR R S m c rp Q rr CK CM NS PS T np CL KE md Hmd Hnp) |].
  unfold hcy5_p9_PA at 1. unfold hcy5_p9_loc, hcy5_lvars, hcy5_p9_cc, hcy5_p9_c2; cbn [app].
  eapply semax_pre; [| apply semax_ifthenelse_PQR' with (v := Vint (hcy5_p9_vc md np))].
  - apply andp_left2, now_later.
  - reflexivity.
  - entailer!.
  - entailer!.
  - (* BA *)
    apply semax_extract_PROP; intro Ht.
    assert (H2np: md <> 2 /\ np <> nullval).
    { unfold hcy5_p9_vc in Ht. destruct (Z.eq_dec md 2); [inversion Ht |].
      destruct (eq_dec np nullval); [inversion Ht | auto]. }
    destruct H2np as [H2 Hn].
    eapply semax_pre; [| apply HA; auto].
    unfold hcy5_p9_PA, hcy5_p9_loc, hcy5_lvars; cbn [app]. entailer!.
  - apply semax_extract_PROP; intro Hf.
    eapply semax_pre; [| apply semax_ifthenelse_PQR' with (v := Vint (if Z.eq_dec md 2 then Int.one else Int.zero))].
    + apply andp_left2, now_later.
    + reflexivity.
    + entailer!.
    + entailer!.
      destruct (Z.eq_dec md 2) as [-> | Hne]; [reflexivity |].
      rewrite Int.eq_false; [reflexivity |]. intro Heq. apply Hne.
      apply (f_equal Int.signed) in Heq. rewrite !Int.signed_repr in Heq by rep_lia. exact Heq.
    + (* BB *)
      apply semax_extract_PROP; intro Ht.
      assert (H2: md = 2) by (destruct (Z.eq_dec md 2); [auto | inversion Ht]).
      eapply semax_pre; [| apply HB; auto].
      unfold hcy5_p9_PA, hcy5_p9_loc, hcy5_lvars; cbn [app]. entailer!.
    + (* nothing *)
      apply semax_extract_PROP; intro Hf2.
      assert (H2: md <> 2) by (destruct (Z.eq_dec md 2); [inversion Hf2 | auto]).
      assert (Hn: np = nullval).
      { unfold hcy5_p9_vc in Hf. destruct (Z.eq_dec md 2); [contradiction |].
        destruct (eq_dec np nullval); [auto | inversion Hf]. }
      eapply semax_pre; [| apply semax_skip].
      unfold hcy5_p9_Q1, hcy5_p9_loc, hcy5_p9_sep, hcy5_lvars.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs; cbn [app].
      assert_PROP (cm_ok CM).
      { unfold cmsg_rep. entailer!. }
      Exists S PS T CM false.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
      entailer!.
Qed.

(* s53: cookie_img(img, reply) *)
Lemma hcy5_p9_s56_ok {Espec: OracleKind} gv L FR R m c rp Q nonce rr CK CM NS np CL KE :
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE)
    hcy5_p9_s56 (normal_ret_assert (hcy5_S9 x25519 xaead_enc gv L FR)).
Proof.
  unfold hcy5_Delta, hcy5_p9_Q1, hcy5_S9, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_s56.
  simplify_func_tycontext.
  Intros S PS T CM' honest.
  abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  match goal with H: hcy5_p9_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (Hr & Hl & Hnp & HT & Hcl & Hcn) end.
  forward_call (Tsh, l_img L, Ews, rp, CM').
  Exists R S m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  entailer!.
Qed.

(* the branch BA from its four segments *)
Lemma hcy5_p9_BA_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE md :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE -> 0 <= md < 3 ->
  md <> 2 -> np <> nullval ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])
    hcy5_p9_BA (normal_ret_assert (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE)).
Proof.
  intros HH Hinv Hmd Hm2 Hnp.
  pose proof Hinv as (Hr & Hl & Hnpok & HT & Hcl & Hcn).
  destruct Hnpok as [-> | (N & a & P & HIn & HN & Hpub)]; [contradiction |].
  apply hcy5_p9_BA_split.
  eapply hcy5_p9_seq;
    [apply (hcy5_p9_BA1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S m c rp Q nonce rr CK CM
              NS PS T np CL KE md N a P HH Hinv HIn HN) |].
  Intros S1 T1 idx. unfold hcy5_p9_PA at 1.
  apply semax_extract_PROP; intro HT1. apply semax_extract_PROP; intro He. apply semax_extract_PROP; intro HL1.
  eapply hcy5_p9_seq;
    [apply (hcy5_p9_BA2a_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S1 m c rp Q rr CK
              NS PS T1 np CL KE md a idx CM HH HT1 He HL1) |].
  eapply hcy5_p9_seq;
    [apply (hcy5_p9_BA2b_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S1 m c rp Q nonce rr CK CM
              NS PS T1 np CL KE md N a P (hcy5_p9_rcv CM idx) HH Hr Hl HIn HN) |].
  apply (hcy5_p9_BA3_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S1 m c rp Q nonce rr CK CM
           NS PS T1 np CL KE md N a P idx HH); auto.
  - unfold hcy5_p9_inv. split; [auto |]. split; [auto |]. split; [right; exists N, a, P; auto |]. auto.
  - lia.
Qed.

Lemma hcy5_P9_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S8 x25519 xaead_enc gv L FR) hcy5_P9
    (overridePost (hcy5_S9 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. rewrite hcy5_p9_P9_eq. unfold hcy5_S8.
  Intros R S m c rp Q nonce rr CK CM. Intros NS PS T np CL KE. Intros.
  assert (Hinv: hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE) by (unfold hcy5_p9_inv; tauto).
  rewrite seq_assoc.
  eapply hcy5_p9_seq; [apply (hcy5_p9_s5354_ok gv L FR R S m c rp Q rr CK CM NS PS T np CL KE) |].
  Intros md. apply semax_extract_prop; intros Hmd.
  eapply hcy5_p9_seq.
  { apply (hcy5_p9_M_ok gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE md Hinv); auto.
    - intros. apply hcy5_p9_BA_ok; auto.
    - intros ->. apply hcy5_p9_BB_ok; auto. }
  eapply semax_post; [| | | | apply hcy5_p9_s56_ok].
  all: destruct (hcy5_R gv); simpl; intros; try (apply andp_left2; apply derives_refl); apply andp_left2; apply FF_left.
Qed.

End Phase.
