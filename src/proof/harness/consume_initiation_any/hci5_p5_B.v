(* law consume_initiation_any: segment B of phase P5 = statement 18, the replay boundary: if (mode != 0 && na != NULL && nondet_u8() % 4 == 0) { d = nondet_u8() % 3; bytes_copy(na->p->handshake.latest_timestamp, ts, 12); if (d != 0) ts_step(na->p->handshake.latest_timestamp, d == 2); }.
   States: hci5_defs.v (S4), hci5_p5_defs.v (Q17, Q18). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_ts.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p5B_lem.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Lemma hci5_p5B_hb_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hci5_p5B_close PS i a P t' : Zlength t' = 12 -> isptr a -> 0 <= i < Zlength PS ->
  (hbytes Ews t' (offset_val 328 a) * hci5_p5B_pr Ews a P * hci5_p5B_fr i PS
   |-- peers_rep (upd_Znth i PS (a, Ews, hci5_p5B_set P t')))%logic.
Proof.
  intros Hl Ha Hi. rewrite hci5_p5B_peers_upd by auto. unfold peer_item_rep.
  rewrite hci5_p5B_peer_split by auto. cancel.
Qed.

Lemma hci5_p5B_open PS i a P : 0 <= i < Zlength PS -> Znth i PS = ((a, Ews, P) : val * share * peer) -> isptr a ->
  Zlength (hs_ts (p_hs P)) = 12 ->
  (peers_rep PS |-- hbytes Ews (hs_ts (p_hs P)) (offset_val 328 a) * hci5_p5B_pr Ews a P * hci5_p5B_fr i PS)%logic.
Proof.
  intros Hi Hz Ha Hl. rewrite (hci5_p5B_peers_at PS i Hi), Hz. unfold peer_item_rep.
  rewrite <- (hci5_p5B_set_same P) at 1. rewrite hci5_p5B_peer_split by auto. cancel.
Qed.

Section P5B.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p5_B_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p5_Q17 x25519 gv L FR) (hci5_seql (hci5_l 18 1))
    (overridePost (hci5_p5_Q18 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH.
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [hci5_seql hci5_l firstn skipn hci5_stmts] in c in change c with c' end.
  unfold hci5_p5_Q17, hci5_Delta, hci5_R. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m M md.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p5_scr; cbn [app].
  pose proof H0 as Hinv. destruct Hinv as (Hpok & Hwf & Hch & Hnp & Hna & HT & Hsl).
  destruct Hna as [Hna | Hna].
  - (* na = NULL: nothing happens *)
    subst na. replace (hci5_p5_c md nullval) with false by (unfold hci5_p5_c; destruct (Int.eq md Int.zero); reflexivity).
    unfold hci5_p5_tsrep.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'13 (Vint Int.zero) :: Q) (SEPx R))) end.
    + forward. entailer!.
    + forward. entailer!.
    + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HC._t'14 (Vint Int.zero) :: Q) (SEPx R))) end.
      * contradiction.
      * forward. entailer!.
      * forward_if.
        -- contradiction.
        -- forward.
           unfold hci5_p5_Q18. Exists R S w NS PS T head nullval KE m M.
           unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
           entailer!.
  - apply in_map_iff in Hna. destruct Hna as (N & <- & HN).
    destruct (hci5_p5B_find NS PS N Hnp HN) as (i & Hi & Hai).
    destruct (Znth i PS) as [[a sh] P] eqn:Hz. cbn in Hai. subst a.
    assert (HinP: In (hn_p N, sh, P) PS) by (rewrite <- Hz; apply Znth_In; auto).
    assert (Hx: hci5_pok x25519 R L (hn_p N, sh, P)) by (rewrite Forall_forall in Hpok; auto).
    destruct Hx as (Hsh & _ & _ & Hhok & _). subst sh.
    pose proof (hci5_p5B_node_acc (hci5_head NS) NS N HN) as A1. unfold hci5_p5B_acc in A1. sep_apply A1. clear A1. Intros.
    assert_PROP (isptr (hn_addr N)) as Hpn by entailer!.
    destruct (Int.eq md Int.zero) eqn:Hmd.
    + replace (hci5_p5_c md (hn_addr N)) with false by (unfold hci5_p5_c; rewrite Hmd; reflexivity).
      apply Int.same_if_eq in Hmd. subst md. unfold hci5_p5_tsrep.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HC._t'13 (Vint Int.zero) :: Q) (SEPx R))) end.
      { first [contradiction | discriminate]. }
      { forward. entailer!. }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HC._t'14 (Vint Int.zero) :: Q) (SEPx R))) end.
      { first [contradiction | discriminate]. }
      { forward. entailer!. }
      forward_if; [first [contradiction | discriminate] |].
      forward.
      sep_apply (hci5_p5B_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
      unfold hci5_p5_Q18. Exists R S w NS PS T head (hn_addr N) KE m M.
      unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
      entailer!.
    + replace (hci5_p5_c md (hn_addr N)) with true
        by (unfold hci5_p5_c; rewrite Hmd; destruct (eq_dec (hn_addr N) nullval) as [E | _];
            [rewrite E in Hpn; contradiction | reflexivity]).
      unfold hci5_p5_tsrep. Intros t.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HC._t'13 (Vint Int.one) :: Q) (SEPx R))) end.
      { forward.
        { go_lower. simpl. change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
          apply denote_tc_test_eq_split; [|apply valid_pointer_null].
          apply derives_trans with (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) * TT)%logic; [cancel|].
          apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; vm_compute; reflexivity. }
        entailer!. destruct (hn_addr N); try contradiction; reflexivity. }
      { match goal with X: md = _ |- _ => rewrite X in Hmd; vm_compute in Hmd; discriminate end. }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (EX b: bool, PROPx P (LOCALx (temp HC._t'14 (Val.of_bool b) :: Q) (SEPx R))) end.
      { forward_call tt. Intros k. forward.
        { entailer!. match goal with X: _ /\ Int.repr 4 = Int.mone |- _ => destruct X as [_ X];
            apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end. }
        Exists (Int.eq (Int.mods (Int.repr k) (Int.repr 4)) (Int.repr 0)). entailer!.
        destruct (Int.eq (Int.mods _ _) _); reflexivity. }
      { first [contradiction | discriminate]. }
      Intros b.
      assert (HtsL: Zlength (hs_ts (p_hs P)) = 12) by (destruct Hhok as (_&_&_&_&_&_&_&X); exact X).
      assert_PROP (isptr (hn_p N)) as Hap.
      { unfold peers_rep. sep_apply (iter_sepcon_in_true peer_item_rep _ _ HinP). unfold peer_item_rep.
        sep_apply (hci5_p5B_peer_ok Ews (hn_p N) P). entailer!. }
      forward_if.
      * forward_call tt. Intros k2. forward.
        { entailer!. match goal with X: _ /\ Int.repr 3 = Int.mone |- _ => destruct X as [_ X];
            apply (f_equal Int.signed) in X; rewrite Int.signed_mone, Int.signed_repr in X by rep_lia; lia end. }
        forward.
        sep_apply (hci5_p5B_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
        sep_apply (hci5_p5B_open PS i (hn_p N) P Hi Hz Hap HtsL). Intros.
        sep_apply (hci5_p5B_hb_out Ews (hs_ts (p_hs P)) (offset_val 328 (hn_p N))). rewrite HtsL.
        replace (hout Ews 12 (offset_val 328 (hn_p N))) with (hout Ews (Zlength t) (offset_val 328 (hn_p N)))
          by (rewrite H2; reflexivity).
        forward_call (Ews, offset_val 328 (hn_p N), Tsh, l_ts L, t).
        { entailer!. rewrite H2. simpl. rewrite offset_offset_val. reflexivity. }
        forward_if.
        -- pose proof (hci5_p5B_node_acc (hci5_head NS) NS N HN) as A1. unfold hci5_p5B_acc in A1. sep_apply A1. clear A1. Intros.
           forward.
           sep_apply (hci5_p5B_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
           forward_call (Ews, offset_val 328 (hn_p N), t,
             (if Int.eq (Int.mods (Int.repr k2) (Int.repr 3)) (Int.repr 2) then Int.one else Int.zero)).
           { entailer!. simpl. rewrite offset_offset_val. f_equal.
             destruct (Int.eq (Int.mods (Int.repr k2) (Int.repr 3)) (Int.repr 2)); reflexivity. }
           Intros t'. rename H6 into Ht'.
           sep_apply (hci5_p5B_close PS i (hn_p N) P t' Ht' Hap Hi).
           sep_apply (hci5_p5B_hb_out Tsh t (l_ts L)). rewrite H2.
           assert (Hinv': hci5_inv x25519 R L NS (upd_Znth i PS (hn_p N, Ews, hci5_p5B_set P t')) KE T head (hn_addr N))
             by (eapply hci5_p5B_inv; eauto).
           unfold hci5_p5_Q18. Exists R S w NS (upd_Znth i PS (hn_p N, Ews, hci5_p5B_set P t')) T head (hn_addr N) KE m M.
           unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
           entailer!.
        -- forward.
           sep_apply (hci5_p5B_close PS i (hn_p N) P t H2 Hap Hi).
           sep_apply (hci5_p5B_hb_out Tsh t (l_ts L)). rewrite H2.
           assert (Hinv': hci5_inv x25519 R L NS (upd_Znth i PS (hn_p N, Ews, hci5_p5B_set P t)) KE T head (hn_addr N))
             by (eapply hci5_p5B_inv; eauto).
           unfold hci5_p5_Q18. Exists R S w NS (upd_Znth i PS (hn_p N, Ews, hci5_p5B_set P t)) T head (hn_addr N) KE m M.
           unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
           entailer!.
      * forward.
        sep_apply (hci5_p5B_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)) (hnodes_rep4 W (hci5_head NS) NS)).
        sep_apply (hci5_p5B_hb_out Tsh t (l_ts L)). rewrite H2.
        unfold hci5_p5_Q18. Exists R S w NS PS T head (hn_addr N) KE m M.
        unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
        entailer!.
Qed.

End P5B.
