(* law consume_initiation_any, phase P8, segment if: statement 34: if (target == NULL) CHECK(ret == NULL && hnodes_same_except(peers, NULL)) else ACC; the else branch ACC is the hypothesis HACC (proved by the segments A1, A2, A3).
   States and statements: hci5_p8_defs.v; (section P8).  The statement is
*)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_if_pure.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hci5_p8_if_vo sh wg D : device_rep sh wg D = vobjs W_consume_initiation_any [VDev sh wg D].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hci5_p8_if_snapped_addr T NS PS : length NS = length PS ->
  map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  revert PS; induction NS as [|N NS IH]; intros [|[[p sh] P] PS] Hl; try discriminate; [reflexivity |].
  simpl in Hl. injection Hl as Hl. specialize (IH PS Hl). unfold hnodes_snapped4 in *.
  cbn [combine map] in *. rewrite IH. reflexivity.
Qed.

Lemma hci5_p8_if_tgt_in x25519 aead_dec IB PS M now a P t ck2 h2 :
  hci5_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) -> In a (map peer_addr4 PS).
Proof.
  unfold hci5_tgt. intros Ht.
  destruct (mi_ok IB); [| discriminate].
  destruct (m_consume_init1_model _ _ _ _ _) as [[[[s k] ck1] h1]|]; [| discriminate].
  destruct (pk_find PS s) as [[a0 P0]|] eqn:Hf; [| discriminate].
  destruct (m_consume_init2_model _ _ _ _ _) as [[[t0 c0] g0]|]; [| discriminate].
  destruct (_ && _)%bool; [| discriminate]. inv Ht.
  destruct (hci5_model_pk_find _ _ _ _ Hf) as [sh Hin].
  change a with (peer_addr4 (a, sh, P)). apply in_map; exact Hin.
Qed.

Lemma hci5_p8_if_nfind: forall NS PS a, hnodes_peers4 NS PS -> In a (map peer_addr4 PS) ->
  In (hci5_nfind NS a) (map hn_addr NS).
Proof.
  unfold hnodes_peers4. induction NS as [|N NS IH]; intros PS a Hm Hin.
  - destruct PS; [contradiction | discriminate].
  - destruct PS as [|x PS]; [discriminate |]. simpl in Hm. injection Hm as H0 H1.
    simpl. match goal with |- context [if ?d then _ else _] => destruct d as [_|n] end; [left; reflexivity |].
    right. simpl in Hin. destruct Hin as [Hx | Hin]; [congruence |]. eapply IH; eauto.
Qed.

(* a node of the list: a pointer, valid *)
Lemma hci5_p8_if_node_ptr NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W_consume_initiation_any l NS |-- !! isptr a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end. exact Hp.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

Lemma hci5_p8_if_node_valid NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W_consume_initiation_any l NS |-- valid_pointer a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

Lemma hci5_p8_if_pn l NS : hnodes_rep4 W_consume_initiation_any l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    destruct H0 as [Hp _]. destruct (hn_addr N); simpl in *; try contradiction; auto.
Qed.

Lemma hci5_p8_if_ews x25519 R L NS PS KE T head na : hci5_inv x25519 R L NS PS KE T head na ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS.
Proof.
  intros (Hpok & _). eapply Forall_impl; [| exact Hpok]. intros [[p sh] P] Hk. simpl in Hk. tauto.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_if_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA0 x25519 aead_dec gv L FR) (hci5_seql hci5_p8_acc)
    (overridePost (hci5_p8_Q2 x25519 gv L FR) (hci5_R gv)) ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_Q1 x25519 aead_dec gv L FR) hci5_p8_s34
    (overridePost (hci5_p8_Q2 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros Hy HACC.
  revert HACC. generalize (hci5_R gv) as Rr. intros [r1 r2 r3 r4] HACC.
  unfold hci5_p8_Q1. Intros R S w NS PS T head na KE m M.
  assert (Hag: cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S =
               hci5_res x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S)).
  { apply hci5_agree; [reflexivity |].
    destruct H0 as (Hpok & _). eapply Forall_impl; [| exact Hpok].
    intros [[p sh] P] Hk. simpl in Hk |- *. split; [tauto |].
    intros Hz. destruct Hk as (_ & _ & _ & _ & _ & Hr & _). rewrite Hz in Hr. rewrite Int.unsigned_zero in Hr. lia. }
  rewrite Hag. unfold hci5_res.
  destruct (hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S)) as [[[[[a P] t] ck2] h2]|] eqn:Htg;
    cbv beta iota delta [hci5_tnode peers_after peer_result hci5_ci_rep];
    (let s := eval hnf in hci5_p8_s34 in match s with Sifthenelse ?b ?c1 _ =>
       change hci5_p8_s34 with (Sifthenelse b c1 (hci5_seql hci5_p8_acc)) end).
  - (* acceptance: target is a's node, not NULL; the else branch is the hypothesis *)
    unfold hci5_Delta. simplify_func_tycontext. abbreviate_semax.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_p8_scr; cbn [app].
    Intros key spub.
    assert (HinN: In (hci5_nfind NS a) (map hn_addr (hnodes_snapped4 T NS PS))).
    { destruct H0 as (_ & _ & _ & Hpeers & _).
      rewrite hci5_p8_if_snapped_addr by (apply hci5_p8_if_peers_len; exact Hpeers).
      eapply hci5_p8_if_nfind; [exact Hpeers |]. eapply hci5_p8_if_tgt_in; exact Htg. }
    assert_PROP (isptr (hci5_nfind NS a)) as Hpt.
    { sep_apply (hci5_p8_if_node_ptr _ (hci5_head NS) _ HinN). entailer!. }
    forward_if.
    { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (hci5_p8_if_node_valid _ (hci5_head NS) _ HinN). entailer!. }
    { exfalso. match goal with Hn: hci5_nfind NS a = nullval |- _ => rewrite Hn in Hpt; exact Hpt end. }
    eapply semax_pre; [| exact HACC].
    unfold hci5_p8_QA0. Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
    sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hci5_DB x25519 R L) head) (l_ds L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
    entailer!.
  - (* rejection: target NULL, ret NULL, nothing changed *)
    unfold hci5_Delta. simplify_func_tycontext. abbreviate_semax.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_p8_scr; cbn [app].
    assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
    destruct (hci5_p8_if_pre x25519 R L NS PS KE T head na (hci5_DB x25519 R L) H0 HwfT)
      as (Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9 & Hmp).
    clear HACC Hag.
    forward_if.
    2: { exfalso. auto. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if (temp HC._t'37 (Vint Int.one)).
      { assert_PROP (is_pointer_or_null (hci5_head NS)) as Hhd.
        { sep_apply (hci5_p8_if_pn (hci5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
        forward.
        rewrite (hci5_p8_if_vo Tsh (l_wb L) (hci5_DB x25519 R L)).
        forward_call (hci5_head NS, hnodes_snapped4 T NS PS, PS, hci5_p8_if_sns T PS, hci5_p8_if_rs PS,
                      hci5_p8_if_prs PS, nullval, Tsh, l_itb L, T, [VDev Tsh (l_wb L) (hci5_DB x25519 R L)]).
        { apply Forall_cons; [apply readable_share_top | apply Forall_nil]. }
        rewrite hci5_p8_if_same.
        forward.
        rewrite <- (hci5_p8_if_vo Tsh (l_wb L) (hci5_DB x25519 R L)).
        entailer!. }
      { exfalso. auto. }
      forward_if.
      { exfalso. apply Int.one_not_zero. assumption. }
      forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    unfold hci5_p8_Q2. Exists R S w NS (hnodes_snapped4 T NS PS) PS PS.
    Exists T head na KE (map (kent_snapped T) KE) m M.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
    assert (Hke: map ke_addr (map (kent_snapped T) KE) = map ke_addr KE).
    { rewrite map_map. apply map_ext. intros e. reflexivity. }
    pose proof (hci5_p8_if_ews x25519 R L NS PS KE T head na H0) as Hews.
    sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hci5_DB x25519 R L) head) (l_ds L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
    entailer!.
Qed.

End Seg.
