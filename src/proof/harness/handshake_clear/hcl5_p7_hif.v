(* law handshake_clear, phase P7: segment hif of the loop body.
   HIF = t'23 = nd->snap.hashed; if (t'23) { CHECK(table_has(&it, &nd->p->handshake.entry)); hashed++; } for the node k <> i: hashed counts node k iff its entry was in t_L T.
   States and statements: hcl5_p7_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_defs.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

Lemma hcl5_p7_hif_hb (s: hsnap) :
  (let (x, _) := let (_, y) := let (_, y) := hsnap_val s in y in y in x) = Val.of_bool (sn_hashed s).
Proof. reflexivity. Qed.

Lemma hcl5_p7_hif_p (q: val) (s: hsnap) (Q: peer) (nx: val) :
  (let (x, _) := hcl5_p7_nv q s Q nx in x) = q.
Proof. reflexivity. Qed.

Lemma hcl5_p7_hif_inrm (a b: val) (l: list val) : In a (vremove b l) <-> In a l /\ a <> b.
Proof.
  induction l as [|x l IH]; simpl; [tauto|].
  match goal with |- context [if ?d then _ else _] => destruct d as [E|E] end; simpl; rewrite IH; subst; split; intros; intuition (subst; congruence).
Qed.

Lemma hcl5_p7_hif_vin (a b: val) (l: list val) : a <> b -> vin a (vremove b l) = vin a l.
Proof.
  intros Hab. unfold vin.
  destruct (in_dec eq_dec a (vremove b l)) as [H|H], (in_dec eq_dec a l) as [H'|H']; auto;
    pose proof (hcl5_p7_hif_inrm a b l); tauto.
Qed.

Lemma hcl5_p7_hif_q (NS: list hnode4) (PS: list (val * share * peer)) KE T i k q Q :
  hcl5_T_ok PS KE T -> hnodes_peers4 NS PS -> NoDup (saddrs (t_D T)) ->
  0 <= i < Zlength NS -> 0 <= k < Zlength NS -> k <> i -> Znth k PS = (q, Ews, Q) ->
  In (hs_addr q) (saddrs (t_D T)) /\ q <> hn_p (Znth i NS) /\ hs_addr q <> hs_addr (hn_p (Znth i NS)).
Proof.
  intros [Hs _] Hp Hnd Hi Hk Hki Hq.
  assert (HL: Zlength NS = Zlength PS).
  { rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS). unfold hnodes_peers4 in Hp. congruence. }
  assert (Hpi: hn_p (Znth i NS) = peer_addr4 (Znth i PS)).
  { rewrite <- Znth_map by lia. unfold hnodes_peers4 in Hp. rewrite Hp, Znth_map by lia. reflexivity. }
  set (f := fun x => hs_addr (peer_addr4 x)).
  assert (Hnd2: NoDup (map f PS)). { rewrite Hs in Hnd. apply NoDup_app_remove_l in Hnd. exact Hnd. }
  assert (Hfk: hs_addr q = Znth k (map f PS)). { rewrite Znth_map by lia. unfold f. rewrite Hq. reflexivity. }
  assert (Hfi: hs_addr (hn_p (Znth i NS)) = Znth i (map f PS)). { rewrite Znth_map by lia. unfold f. rewrite Hpi. reflexivity. }
  assert (Hne: hs_addr q <> hs_addr (hn_p (Znth i NS))).
  { rewrite Hfk, Hfi. intro E. apply Hki. eapply NoDup_Znth_inj; eauto; rewrite Zlength_map; lia. }
  split; [|split; [intro E; apply Hne; rewrite E; reflexivity | exact Hne]].
  rewrite Hs. apply in_or_app. right. rewrite Hfk. apply Znth_In. rewrite Zlength_map. lia.
Qed.

Lemma hcl5_p7_hif_nh T p (PS: list (val * share * peer)) k q Q :
  0 <= k < Zlength PS -> Znth k PS = (q, Ews, Q) ->
  hcl5_nh T p (firstn (Z.to_nat (k + 1)) PS) =
  hcl5_nh T p (firstn (Z.to_nat k) PS) + (if andb (negb (veqb q p)) (vin (hs_addr q) (t_L T)) then 1 else 0).
Proof.
  intros Hk Hq. rewrite <- !sublist_firstn.
  rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia. rewrite Hq.
  unfold hcl5_nh. rewrite filter_app, Zlength_app. cbn [filter peer_addr4].
  destruct (andb _ _); reflexivity.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p7_hif_ok {Espec: OracleKind} gv L FR R S w NS PS T head KE i k nx q Q :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_p7_Q0 x25519 gv L FR R S w NS PS T head KE i k nx q Q) hcl5_p7_hif
    (overridePost (hcl5_p7_Q1 x25519 gv L FR R S w NS PS T head KE i k nx q Q) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_p7_Q0, hcl5_p7_Q1, hcl5_p7_Q, hcl5_Delta, hcl5_R, hcl5_p7_hif.
  simplify_func_tycontext. abbreviate_semax.
  unfold hcl5_p7_fix, hcl5_lvars; cbn [app]. Intros. unfold hcl5_p7_nv.
  forward.
  { rewrite hcl5_p7_hif_hb. entailer!. destruct (vin _ _); cbn; auto. }
  rewrite hcl5_p7_hif_hb.
  assert_PROP (itable_wf (t_remove T (hs_addr (hn_p (Znth i NS))))) as Hwf by (unfold itable; entailer!).
  assert_PROP (isptr q) as Hq by (entailer!; destruct q; simpl in *; tauto).
  fold (hcl5_p7_nv q (hs_snap_cur T q Q) Q nx).
  assert (H0c := H0). destruct H0c as (_ & _ & _ & Hp & HT & _).
  destruct Hwf as (_ & _ & Hnd & _).
  destruct (hcl5_p7_hif_q NS PS KE T i k q Q HT Hp Hnd H1 H2 H5 H4) as (Hin & Hqp & Hhq).
  assert (HLen: Zlength NS = Zlength PS).
  { rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS). unfold hnodes_peers4 in Hp. congruence. }
  forward_if.
  - destruct (vin (hs_addr q) (t_L T)) eqn:Ev; try (inv H6; fail).
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + entailer!.
    + forward. rewrite hcl5_p7_hif_p.
      forward_call (Tsh, l_it L, t_remove T (hs_addr (hn_p (Znth i NS))), hs_addr q).
      change (t_L (t_remove T (hs_addr (hn_p (Znth i NS))))) with (vremove (hs_addr (hn_p (Znth i NS))) (t_L T)).
      rewrite (hcl5_p7_hif_vin _ _ _ Hhq), Ev.
      forward_if True.
      * exfalso; apply Int.one_not_zero; exact H7.
      * forward. entailer!.
      * forward.
        entailer!.
    + forward.
      rewrite (hcl5_p7_hif_nh T _ PS k q Q) by (auto; lia).
      assert (Hv: veqb q (hn_p (Znth i NS)) = false)
        by (unfold veqb; destruct (eq_dec _ _); [contradiction|reflexivity]).
      rewrite Ev, Hv. change (if andb (negb false) true then 1 else 0) with 1.
      unfold hcl5_p7_fix, hcl5_lvars; cbn [app].
      entailer!.
  - destruct (vin (hs_addr q) (t_L T)) eqn:Ev; try (inv H6; fail).
    forward.
    rewrite (hcl5_p7_hif_nh T _ PS k q Q) by (auto; lia).
    rewrite Ev, andb_false_r. change (if false then 1 else 0) with 0. rewrite Z.add_0_r.
    unfold hcl5_p7_fix, hcl5_lvars; cbn [app].
    entailer!.
Qed.

End Seg.
