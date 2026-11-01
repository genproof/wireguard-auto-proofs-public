(* law handshake_receive: B8 branch R segment D, part HIF of the node
   loop: t = nd->snap.hashed; if (t) { CHECK(table_has(&itd, &nd->p->handshake.entry)); hashed++; } at a node
   k <> j.  States: hrx5_B8_R_D_defs.v. Port of handshake_clear's hcl5_p7_hif.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RDh_hb (s: hsnap) :
  (let (x, _) := let (_, y) := let (_, y) := hsnap_val s in y in y in x) = Val.of_bool (sn_hashed s).
Proof. reflexivity. Qed.

Lemma hrx5_B8RDh_p (q: val) (s: hsnap) (Q: peer) (nx: val) :
  (let (x, _) := hrx5_B8RD_nv q s Q nx in x) = q.
Proof. reflexivity. Qed.

Lemma hrx5_B8RDh_inrm (a b: val) (l: list val) : In a (vremove b l) <-> In a l /\ a <> b.
Proof.
  induction l as [|x l IH]; simpl; [tauto|].
  match goal with |- context [if ?d then _ else _] => destruct d as [E|E] end; simpl; rewrite IH; subst; split; intros; intuition (subst; congruence).
Qed.

Lemma hrx5_B8RDh_vin (a b: val) (l: list val) : a <> b -> vin a (vremove b l) = vin a l.
Proof.
  intros Hab. unfold vin.
  destruct (in_dec eq_dec a (vremove b l)) as [H|H], (in_dec eq_dec a l) as [H'|H']; auto;
    pose proof (hrx5_B8RDh_inrm a b l); tauto.
Qed.

Lemma hrx5_B8RDh_saddrs (PS: list (val * share * peer)) (D2: list (val * share * entry)) :
  Forall2 hrx5cr_hs_ok PS D2 -> saddrs D2 = map (fun x => hs_addr (peer_addr4 x)) PS.
Proof.
  induction 1 as [|[[p sp] P] [[x sx] E] PS' D2' H _ IH]; [reflexivity|].
  simpl in H |- *. destruct H as [-> _]. rewrite IH. reflexivity.
Qed.

Lemma hrx5_B8RDh_q (NS: list hnode4) (PS: list (val * share * peer)) (KE: list kent4) T j k q Q :
  hrx5cr_pool (map ke_addr KE) PS T -> hnodes_peers4 NS PS -> NoDup (saddrs (t_D T)) ->
  0 <= j < Zlength NS -> 0 <= k < Zlength NS -> k <> j -> Znth k PS = (q, Ews, Q) ->
  In (hs_addr q) (saddrs (t_D T)) /\ q <> hn_p (Znth j NS) /\ hs_addr q <> hs_addr (hn_p (Znth j NS)).
Proof.
  intros [_ Hs] Hp Hnd Hj Hk Hkj Hq.
  assert (HL: Zlength NS = Zlength PS).
  { rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS). unfold hnodes_peers4 in Hp. congruence. }
  assert (Hpj: hn_p (Znth j NS) = peer_addr4 (Znth j PS)).
  { rewrite <- Znth_map by lia. unfold hnodes_peers4 in Hp. rewrite Hp, Znth_map by lia. reflexivity. }
  apply hrx5_B8RDh_saddrs in Hs.
  set (f := fun x => hs_addr (peer_addr4 x)) in *.
  assert (Hsp: saddrs (t_D T) = saddrs (firstn (length (map ke_addr KE)) (t_D T)) ++ map f PS).
  { rewrite <- Hs. unfold saddrs. rewrite <- map_app, firstn_skipn. reflexivity. }
  assert (Hnd2: NoDup (map f PS)). { rewrite Hsp in Hnd. apply NoDup_app_remove_l in Hnd. exact Hnd. }
  assert (Hfk: hs_addr q = Znth k (map f PS)). { rewrite Znth_map by lia. unfold f. rewrite Hq. reflexivity. }
  assert (Hfj: hs_addr (hn_p (Znth j NS)) = Znth j (map f PS)). { rewrite Znth_map by lia. unfold f. rewrite Hpj. reflexivity. }
  assert (Hne: hs_addr q <> hs_addr (hn_p (Znth j NS))).
  { rewrite Hfk, Hfj. intro E. apply Hkj. eapply NoDup_Znth_inj; eauto; rewrite Zlength_map; lia. }
  split; [|split; [intro E; apply Hne; rewrite E; reflexivity | exact Hne]].
  rewrite Hsp. apply in_or_app. right. rewrite Hfk. apply Znth_In. rewrite Zlength_map. lia.
Qed.

Lemma hrx5_B8RDh_nh T p (PS: list (val * share * peer)) k q Q :
  0 <= k < Zlength PS -> Znth k PS = (q, Ews, Q) ->
  hrx5_B8R_nh T p (firstn (Z.to_nat (k + 1)) PS) =
  hrx5_B8R_nh T p (firstn (Z.to_nat k) PS) + (if andb (negb (veqb q p)) (vin (hs_addr q) (t_L T)) then 1 else 0).
Proof.
  intros Hk Hq. rewrite <- !sublist_firstn.
  rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia. rewrite Hq.
  unfold hrx5_B8R_nh. rewrite filter_app, Zlength_app. cbn [filter peer_addr4].
  destruct (andb _ _); reflexivity.
Qed.

Lemma hrx5_B8RDh_tf T Tf a q :
  (Tf = T \/ Tf = t_remove T (hs_addr a)) -> hs_addr q <> hs_addr a ->
  t_D Tf = t_D T /\ vin (hs_addr q) (t_L Tf) = vin (hs_addr q) (t_L T).
Proof.
  intros [-> | ->] Hne; [auto|]. split; [reflexivity|]. apply hrx5_B8RDh_vin; exact Hne.
Qed.

Section Seg.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variables (gv: globals) (L: hrx5_loc) (R: hrx5_run) (NS: list hnode4) (PS: list (val * share * peer))
  (KE: list kent4) (T: tstate) (head nk: val) (j: Z) (a tg: val) (Pf: peer) (Tf: tstate) (D: device) (FRM: mpred).
Variables (vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0
           vpath: val).

Lemma hrx5_B8RD_hif_ok (Rp: ret_assert) (k: Z) (nx q: val) (Q: peer) :
  hrx5_B8RD_hyp x25519 L R NS PS KE T head nk j a tg Tf ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B8RD_Q0 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc
       vimg vlen vkind vai var vhead0 vpath k nx q Q)
    hrx5_B8RD_hif
    (overridePost (hrx5_B8RD_Q1 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf
       vmi vmr vmc vimg vlen vkind vai var vhead0 vpath k nx q Q) Rp).
Proof.
  intros HY. destruct Rp as [rpn rpb rpc rpr].
  unfold hrx5_B8RD_Q0, hrx5_B8RD_Q1, hrx5_B8RD_Q, hrx5_Delta, hrx5_B8RD_hif.
  simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app]. Intros. unfold hrx5_B8RD_nv.
  forward.
  { rewrite hrx5_B8RDh_hb. entailer!. destruct (vin _ _); cbn; auto. }
  rewrite hrx5_B8RDh_hb.
  assert_PROP (itable_wf Tf) as Hwf by (unfold itable; entailer!).
  assert_PROP (isptr q) as Hqp0 by (entailer!; destruct q; simpl in *; tauto).
  fold (hrx5_B8RD_nv q (hs_snap_cur T q Q) Q nx).
  destruct HY as ((_ & _ & _ & _ & Hp & _ & Hpool) & Hj & Ha & _ & _ & HTf).
  destruct Hwf as (_ & _ & Hnd & _).
  assert (HD: t_D Tf = t_D T) by (destruct HTf as [-> | ->]; reflexivity).
  rewrite HD in Hnd.
  destruct (hrx5_B8RDh_q NS PS KE T j k q Q Hpool Hp Hnd Hj H H1 H0) as (Hin & Hqp & Hhq).
  rewrite Ha in Hqp, Hhq.
  destruct (hrx5_B8RDh_tf T Tf a q HTf Hhq) as [_ Hv].
  assert (HLen: Zlength NS = Zlength PS).
  { rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS). unfold hnodes_peers4 in Hp. congruence. }
  unfold hrx5_B8RD_nhk.
  forward_if.
  - destruct (vin (hs_addr q) (t_L T)) eqn:Ev; try (inv H2; fail).
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + entailer!.
    + forward. rewrite hrx5_B8RDh_p.
      forward_call (Tsh, l_itd L, Tf, hs_addr q).
      rewrite Hv.
      forward_if True.
      * exfalso; apply Int.one_not_zero; assumption.
      * forward. entailer!.
      * forward.
        entailer!.
    + forward.
      unfold hrx5_B8RD_nhk. rewrite (hrx5_B8RDh_nh T _ PS k q Q) by (auto; lia).
      assert (Hvq: veqb q a = false)
        by (unfold veqb; destruct (eq_dec _ _); [contradiction|reflexivity]).
      rewrite Ev, Hvq. change (if andb (negb false) true then 1 else 0) with 1.
      unfold hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app].
      entailer!.
  - destruct (vin (hs_addr q) (t_L T)) eqn:Ev; try (inv H2; fail).
    forward.
    unfold hrx5_B8RD_nhk. rewrite (hrx5_B8RDh_nh T _ PS k q Q) by (auto; lia).
    rewrite Ev, andb_false_r. change (if false then 1 else 0) with 0. rewrite Z.add_0_r.
    unfold hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app].
    entailer!.
Qed.

End Seg.
