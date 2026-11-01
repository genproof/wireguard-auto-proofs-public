(* law keypairs: pure: the facts of the others / kents the glue needs.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

(* reflexivity of the comparisons *)
Lemma hkc5o_bytes_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb; destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hkc5o_veqb_refl (x: val) : veqb x x = true.
Proof. unfold veqb; destruct (eq_dec x x); congruence. Qed.

Lemma hkc5o_entry_refl (E: entry) : entry_eqb E E = true.
Proof.
  unfold entry_eqb; destruct (eq_dec (e_peer E) (e_peer E)); [|congruence].
  rewrite !Int.eq_true; reflexivity.
Qed.

Lemma hkc5o_hs_refl (H: handshake) : hs_eqb H H = true.
Proof.
  unfold hs_eqb; destruct (eq_dec (hs_sid H) (hs_sid H)); [|congruence].
  rewrite !Int.eq_true, !Int64.eq_true, !hkc5o_bytes_refl; reflexivity.
Qed.

Lemma hkc5o_pr_refl (P: peer) : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite !hkc5o_veqb_refl, !Int64.eq_true, !hkc5o_bytes_refl, !Bool.eqb_reflx; reflexivity.
Qed.

Lemma hkc5o_int64s_refl (a: list int64) : int64s_eqb a a = true.
Proof. induction a; simpl; auto. rewrite Int64.eq_true, IHa; reflexivity. Qed.

Lemma hkc5o_kp_refl (K: keypair) : kp_eqb K K = true.
Proof.
  unfold kp_eqb, symkey_eqb.
  rewrite !Int64.eq_true, !Int.eq_true, !hkc5o_bytes_refl, !Bool.eqb_reflx, hkc5o_int64s_refl; reflexivity.
Qed.

(* an OD address: T's entry and membership are T0's *)
Lemma hkc5o_od_same (p: val) (OD: list (val * share * entry)) (OH: list val) (KS: list (val * keypair))
  (T T0: tstate) :
  hk5_pool p OD OH KS T ->
  Forall (fun x => match x with (a, sh, E) =>
     sfind (t_D T0) a = Some (sh, E) /\ vin a OH = vin a (t_L T0) end) OD ->
  forall a, In a (saddrs OD) ->
  t_entry_d T a = t_entry_d T0 a /\ vin a (t_L T) = vin a (t_L T0) /\ In a (saddrs (t_D T)).
Proof.
  intros Hpool HOD a Ha.
  destruct Hpool as (Hiff & _ & _ & _ & _ & HF & _).
  assert (Hin: In a (saddrs (t_D T))) by (apply Hiff; auto).
  unfold saddrs in Ha; apply in_map_iff in Ha as [[[a' sh] E] [Ha' Hi]]; simpl in Ha'; subst a'.
  rewrite Forall_forall in HF, HOD.
  specialize (HF _ Hi); specialize (HOD _ Hi); simpl in HF, HOD.
  destruct HF as [HF1 HF2], HOD as [HO1 HO2].
  unfold t_entry_d, t_entry; rewrite HF1, HO1.
  split; [reflexivity|]; split; [congruence|exact Hin].
Qed.

(* a peer of PS: the i-th or one of the rest *)
Lemma hkc5o_in_rest (PS: list (val * share * peer)) (i: Z) (x: val) :
  0 <= i < Zlength PS -> In x (map peer_addr4 PS) ->
  x = peer_addr4 (Znth i PS) \/ In x (map peer_addr4 (hkc5_rest PS i)).
Proof.
  intros Hi Hx.
  rewrite <- (sublist_same 0 (Zlength PS) PS) in Hx by auto.
  rewrite (sublist_split 0 i (Zlength PS)) in Hx by lia.
  rewrite (sublist_split i (i + 1) (Zlength PS)) in Hx by lia.
  rewrite sublist_len_1 in Hx by lia.
  unfold hkc5_rest. rewrite !map_app in *. simpl in Hx.
  apply in_app_or in Hx as [Hx | [Hx | Hx]]; auto; right; apply in_or_app; auto.
Qed.

Lemma hkc5o_rest_wf (PS: list (val * share * peer)) (i: Z) :
  peers_wf PS -> Forall (fun x => match x with (_, sh, _) => readable_share sh end) (hkc5_rest PS i).
Proof.
  intros Hwf. unfold hkc5_rest. apply Forall_app; split; apply Forall_sublist;
  eapply Forall_impl; try exact Hwf; intros [[? ?] ?]; auto.
Qed.

Lemma hkc5_oth_facts_ok : hkc5_oth_facts_stmt.
Proof.
  intros x25519 F V Y O Hfix Hinv Hoth.
  destruct Hinv as (Hrel & _ & Hdev & Hsid & _).
  destruct Hrel as (Hcore & _).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & Hpool).
  destruct Hoth as (Hnp & Hwf & Hnd & HF2 & Hks & Hndka & Hiff & Hndod & HOD & HPS & HKE & Hhead).
  pose proof (hkc5o_od_same _ _ _ _ _ _ Hpool HOD) as Hsame.
  assert (Hlen: Zlength (o_NS O) = Zlength (o_PS O)).
  { rewrite <- (Zlength_map _ _ hn_p), <- (Zlength_map _ _ peer_addr4). unfold hnodes_peers4 in Hnp.
    rewrite Hnp; reflexivity. }
  split; [exact Hlen|].
  split.
  { intros i Hi.
    pose proof (Forall2_Znth _ _ _ HF2 i ltac:(lia)) as HN.
    assert (HpN: hn_p (Znth i (o_NS O)) = peer_addr4 (Znth i (o_PS O))).
    { rewrite <- (Znth_map i hn_p) by lia; rewrite <- (Znth_map i peer_addr4) by lia. unfold hnodes_peers4 in Hnp. rewrite Hnp; reflexivity. }
    pose proof (Znth_In i (o_PS O) Hi) as HinPS.
    pose proof (hkc5o_in_rest (o_PS O) i) as Hrest.
    pose proof (hkc5o_rest_wf (o_PS O) i Hwf) as Hrwf.
    unfold hkc5_on_ok.
    destruct (Znth i (o_PS O)) as [[q sh] Q] eqn:Ex.
    simpl in HpN.
    rewrite Forall_forall in HPS. specialize (HPS _ HinPS). simpl in HPS.
    destruct HPS as (Hep & Het & HQdev & HQsid & HQslots & HQpk & HQrefs).
    destruct HN as (HNs & HNr & HNrest).
    assert (Hq: In (hs_addr q) (saddrs (v_OD V))).
    { apply Hiff; left. apply in_map. change q with (peer_addr4 (q, sh, Q)). apply in_map; auto. }
    destruct (Hsame _ Hq) as (Hent & Hvin & Hin).
    assert (Hsh: readable_share sh).
    { unfold peers_wf in Hwf; rewrite Forall_forall in Hwf; specialize (Hwf _ HinPS); simpl in Hwf; auto. }
    exists (hs_snap_cur (o_T0 O) q Q).
    unfold hs_snap_cur, snap_of; cbn [sn_entry sn_hashed sn_hs sn_next].
    rewrite Hent, Hvin.
    split; [exact HpN|]. split; [exact HNs|]. split; [exact HNr|]. split; [exact HNrest|].
    split; [exact Hsh|].
    split.
    { repeat constructor; cbn; auto. }
    split; [exact Hin|].
    split.
    { unfold hs_ptrs_nn, hs_own; cbn [sn_entry sn_hs]. rewrite Hep, HQsid.
      unfold vobjs_addrs; cbn [map concat vobj_addrs].
      apply Forall_cons; [right; left; reflexivity|].
      apply Forall_cons; [right; left; reflexivity|].
      assert (H2: vp_ok (q :: saddrs (t_D (y_T Y)) ++ map peer_addr4 (hkc5_rest (o_PS O) i) ++
                    [f_w F; id_addr (f_w F); cc_addr (f_w F)] ++ [f_p F] ++ []) (id_addr (f_w F))).
      { right; right; rewrite !in_app_iff; simpl; auto 10. }
      apply Forall_cons; [exact H2|]. apply Forall_cons; [exact H2|]. apply Forall_nil. }
    split.
    { unfold pr_ptrs. rewrite HQdev.
      assert (Hka: forall x, vp_ok (map ke_addr (o_KE O)) x ->
                 vp_ok (q :: vobjs_addrs (VItab Tsh (f_t F) (y_T Y) ::
                    VPeers (hkc5_rest (o_PS O) i) :: [VDev Tsh (f_w F) (hkp5_D x25519 F V); VPeer Tsh (f_p F) (y_P Y)])) x).
      { intros x [Hx | Hx]; [left; auto | right]. right. unfold vobjs_addrs; cbn [map concat vobj_addrs].
        right. apply in_or_app; left.
        destruct (Hsame x) as (_ & _ & Hx'); [apply Hiff; auto|]. exact Hx'. }
      assert (Hw: vp_ok (q :: vobjs_addrs (VItab Tsh (f_t F) (y_T Y) ::
                    VPeers (hkc5_rest (o_PS O) i) :: [VDev Tsh (f_w F) (hkp5_D x25519 F V); VPeer Tsh (f_p F) (y_P Y)]))
                    (f_w F)).
      { right. unfold vobjs_addrs; cbn [map concat vobj_addrs]. right.
        rewrite !app_nil_r. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. left; auto. }
      assert (Hpk: vp_ok (q :: vobjs_addrs (VItab Tsh (f_t F) (y_T Y) ::
                    VPeers (hkc5_rest (o_PS O) i) :: [VDev Tsh (f_w F) (hkp5_D x25519 F V); VPeer Tsh (f_p F) (y_P Y)]))
                    (p_pknext Q)).
      { destruct HQpk as [Hx | Hx]; [left; auto | right].
        unfold vobjs_addrs; cbn [map concat vobj_addrs]. rewrite !app_nil_r.
        destruct Hx as [Hx | Hx].
        - right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. rewrite <- Hx; left; auto.
        - destruct (Hrest _ Hi Hx) as [Hy | Hy]; [left; simpl in Hy; auto|].
          right. apply in_or_app; right. apply in_or_app; left. exact Hy. }
      rewrite Forall_forall in HQslots.
      assert (Hc: vp_ok (map ke_addr (o_KE O)) (p_cur Q)) by (apply HQslots; simpl; auto).
      assert (Hp: vp_ok (map ke_addr (o_KE O)) (p_prev Q)) by (apply HQslots; simpl; auto).
      assert (Hn: vp_ok (map ke_addr (o_KE O)) (p_next Q)) by (apply HQslots; simpl; auto).
      apply Hka in Hc; apply Hka in Hp; apply Hka in Hn.
      repeat (apply Forall_cons; [assumption|]); apply Forall_nil. }
    split.
    { unfold snap_eqb_nn; cbn [sn_entry sn_hashed sn_hs].
      rewrite hkc5o_entry_refl, Bool.eqb_reflx, hkc5o_hs_refl; reflexivity. }
    split; [apply hkc5o_pr_refl|].
    reflexivity. }
  split.
  { constructor; [|constructor]. cbn. eapply Forall_impl; [|exact Hwf]. intros [[? ?] ?]; auto. }
  assert (Hke: forall e, In e (o_KE O) ->
    In (ke_addr e) (saddrs (v_OD V))).
  { intros e He. apply Hiff; right. apply in_map; auto. }
  split.
  { rewrite Forall_forall; intros e He.
    rewrite Forall_forall in Hks, HKE.
    specialize (Hks _ He). specialize (HKE _ He).
    destruct (Hsame _ (Hke _ He)) as (Hent & Hvin & Hin).
    split; [exact Hin|].
    rewrite <- Hks. cbn [kent_snapped ke_snap ke_addr kent_ptrs_nn ks_E].
    split; [congruence|].
    rewrite Hent.
    assert (Hp: vp_ok (saddrs (t_D (y_T Y)) ++ vobjs_addrs [VPeers (o_PS O)]) (e_peer (t_entry_d (o_T0 O) (ke_addr e)))).
    { right. apply in_or_app; right. unfold vobjs_addrs; cbn. rewrite app_nil_r; exact HKE. }
    repeat (apply Forall_cons; [assumption|]); apply Forall_nil. }
  apply forallb_forall; intros e He.
  rewrite Forall_forall in Hks. specialize (Hks _ He).
  destruct (Hsame _ (Hke _ He)) as (Hent & Hvin & _).
  rewrite <- Hks. unfold kent_same_bn, kent_eqb_cur, kent_eqb_nn.
  cbn [kent_snapped ke_snap ke_addr ks_E ks_hashed ks_K].
  rewrite Hent, Hvin, hkc5o_entry_refl, Bool.eqb_reflx, hkc5o_kp_refl.
  destruct (vin (ke_addr e) (t_L (o_T0 O))); reflexivity.
Qed.
