(* law consume_initiation_any, phase P8, segment if: pure facts for
   hnodes_same_except4(peers, NULL) over the snapshot nodes hnodes_snapped4 T NS PS (rejection branch). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* the arguments sns / rs / prs of hnodes_same_except4 *)
Definition hci5_p8_if_sns (T: tstate) (PS: list (val * share * peer)) : list hsnap :=
  map (fun x => match x with (p, _, P) => hs_snap_cur T p P end) PS.
Definition hci5_p8_if_rs (PS: list (val * share * peer)) : list int :=
  map (fun x => match x with (_, _, P) => p_refs P end) PS.
Definition hci5_p8_if_prs (PS: list (val * share * peer)) : list peer :=
  map (fun x => match x with (_, _, P) => P end) PS.

Lemma hci5_p8_if_bytes_refl b : bytes_eqb b b = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec b b); congruence. Qed.

Lemma hci5_p8_if_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb; cbn.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hci5_p8_if_bytes_refl.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hci5_p8_if_veqb_refl v : veqb v v = true.
Proof. unfold veqb. rewrite if_true by reflexivity. reflexivity. Qed.

Lemma hci5_p8_if_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite ?hci5_p8_if_veqb_refl, ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hci5_p8_if_bytes_refl.
  reflexivity.
Qed.

Lemma hci5_p8_if_same T PS :
  hnodes_same4 T nullval (hci5_p8_if_sns T PS) (hci5_p8_if_rs PS) (hci5_p8_if_prs PS) PS = true.
Proof.
  induction PS as [|[[p sh] P] PS IH]; [reflexivity |].
  cbn [hci5_p8_if_sns hci5_p8_if_rs hci5_p8_if_prs map hnodes_same4].
  fold (hci5_p8_if_sns T PS) (hci5_p8_if_rs PS) (hci5_p8_if_prs PS). rewrite IH.
  destruct (eq_dec p nullval); [reflexivity |].
  rewrite hci5_p8_if_snap_refl, Int.eq_true, hci5_p8_if_pr_refl. reflexivity.
Qed.

(* the snapshot nodes *)
Lemma hci5_p8_if_snapped T NS PS : length NS = length PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hci5_p8_if_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hci5_p8_if_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hci5_p8_if_prs PS) /\
  length (hnodes_snapped4 T NS PS) = length PS.
Proof.
  revert PS; induction NS as [|N NS IH]; intros [|[[p sh] P] PS] Hl; try discriminate; [repeat split |].
  simpl in Hl. injection Hl as Hl. destruct (IH PS Hl) as (H1 & H2 & H3 & H4 & H5).
  unfold hnodes_snapped4 in *. cbn [combine map hci5_p8_if_sns hci5_p8_if_rs hci5_p8_if_prs length] in *.
  rewrite H1, H2, H3, H4, H5. cbn. repeat split.
Qed.

Lemma hci5_p8_if_peers_len NS PS : hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros H. unfold hnodes_peers4 in H.
  rewrite <- (length_map hn_p NS), H, length_map. reflexivity.
Qed.

(* the comparison's pointers, peer by peer *)
Lemma hci5_p8_if_cmp_of own T PS :
  Forall (fun x => match x with (p, _, P) =>
     In (hs_addr p) (saddrs (t_D T)) /\
     Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p P) (hs_snap_cur T p P) ++ pr_ptrs P P) end) PS ->
  hn4_cmp_ok own T (hci5_p8_if_sns T PS) (hci5_p8_if_prs PS) PS.
Proof.
  induction PS as [|[[p sh] P] PS IH]; intros HF; [exact I |].
  cbn [hci5_p8_if_sns hci5_p8_if_prs map hn4_cmp_ok].
  split; [exact (Forall_inv HF) | apply IH; exact (Forall_inv_tail HF)].
Qed.

(* the public-key chain: every peer's link is NULL or a peer of the list *)
Lemma hci5_p8_if_chain : forall PS head, pk_chain head PS ->
  Forall (fun x => match x with (_, _, P) => p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 PS) end) PS.
Proof.
  induction PS as [|[[a sh] P] PS IH]; intros head Hc; constructor.
  - destruct Hc as [_ Hc]. destruct PS as [|[[b sh'] P'] PS']; simpl in Hc.
    + left; exact Hc.
    + right. destruct Hc as [-> _]. simpl. right; left; reflexivity.
  - destruct Hc as [_ Hc]. specialize (IH _ Hc).
    eapply Forall_impl; [| exact IH]. intros [[b sh'] Q] [H|H]; [left; exact H | right; simpl; right; exact H].
Qed.

Lemma hci5_p8_if_succ_in : forall l a, succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [|x l IH]; intros a; cbn [succ_in]; [left; reflexivity |].
  destruct (eq_dec x a).
  - destruct l as [|y l]; cbn [hd]; [left; reflexivity | right; right; left; reflexivity].
  - destruct (IH a) as [H|H]; [left; exact H | right; right; exact H].
Qed.

(* hnodes_same_except4's PROP over the snapshot nodes, VO = [VDev Tsh wg D] *)
Lemma hci5_p8_if_pre x25519 R L NS PS KE T head na D :
  hci5_inv x25519 R L NS PS KE T head na -> itable_wf T ->
  hnodes_peers4 (hnodes_snapped4 T NS PS) PS /\ peers_wf PS /\
  Zlength (hci5_p8_if_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hci5_p8_if_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hci5_p8_if_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hci5_p8_if_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hci5_p8_if_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hci5_p8_if_prs PS) /\
  hn4_cmp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs [VDev Tsh (l_wb L) D]) T
    (hci5_p8_if_sns T PS) (hci5_p8_if_prs PS) PS /\
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  intros (Hpok & Hwf & Hch & Hnp & _ & (HTs & _ & HTe & _) & Hsl) HwT.
  pose proof (hci5_p8_if_peers_len _ _ Hnp) as Hlen.
  destruct (hci5_p8_if_snapped T NS PS Hlen) as (H1 & H2 & H3 & H4 & H5).
  assert (HZ: Zlength (hnodes_snapped4 T NS PS) = Zlength PS) by (rewrite !Zlength_correct, H5; reflexivity).
  rewrite HZ. unfold hci5_p8_if_sns, hci5_p8_if_rs, hci5_p8_if_prs; rewrite !Zlength_map.
  fold (hci5_p8_if_sns T PS) (hci5_p8_if_rs PS) (hci5_p8_if_prs PS).
  split; [unfold hnodes_peers4; rewrite H1; exact Hnp |].
  do 7 (split; [first [exact Hwf | reflexivity | assumption] |]).
  split; [| exact H1].
  apply hci5_p8_if_cmp_of. apply Forall_forall. intros [[p sh] P] Hin.
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hk. simpl in Hk.
  destruct Hk as (_ & Hdev & Hsid & _).
  pose proof (proj1 (Forall_forall _ _) HTe _ Hin) as He. simpl in He.
  pose proof (proj1 (Forall_forall _ _) Hsl _ Hin) as Hs. simpl in Hs.
  pose proof (proj1 (Forall_forall _ _) (hci5_p8_if_chain _ _ Hch) _ Hin) as Hc. simpl in Hc.
  assert (HinP: In p (map peer_addr4 PS)) by (change p with (peer_addr4 (p, sh, P)); apply in_map; exact Hin).
  assert (HinK: forall k, In k (map ke_addr KE) -> In k (saddrs (t_D T))).
  { intros k Hk. rewrite HTs. apply in_app_iff; left; exact Hk. }
  destruct HwT as (_ & Hincl & _ & _).
  split.
  { rewrite HTs. apply in_app_iff; right.
    change (hs_addr p) with ((fun x => hs_addr (peer_addr4 x)) (p, sh, P)). apply in_map; exact Hin. }
  inversion Hs as [|? ? Hcur Hs1]; subst. inversion Hs1 as [|? ? Hprev Hs2]; subst.
  inversion Hs2 as [|? ? Hnext _]; subst.
  unfold hs_ptrs, hs_ptrs_nn, pr_ptrs, hs_snap_cur, snap_of; cbn [sn_next sn_entry sn_hs app].
  unfold vobjs_addrs; cbn [map concat vobj_addrs app].
  assert (Hsucc: vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)])
                   (succ_in (t_L T) (hs_addr p))).
  { destruct (hci5_p8_if_succ_in (t_L T) (hs_addr p)) as [H|H]; [left; exact H |].
    right. apply in_app_iff; right; apply in_app_iff; left. apply Hincl; exact H. }
  assert (Hpeer: vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)])
                   (e_peer (t_entry_d T (hs_addr p)))).
  { right. rewrite He. apply in_app_iff; left; exact HinP. }
  assert (Hs_id: vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)])
                   (hs_sid (p_hs P))).
  { right. rewrite Hsid. apply in_app_iff; right; apply in_app_iff; right. simpl; auto. }
  assert (Hdv: vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)])
                   (p_device P)).
  { right. rewrite Hdev. apply in_app_iff; right; apply in_app_iff; right. simpl; auto. }
  assert (Hslot: forall k, k = nullval \/ In k (map ke_addr KE) ->
     vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)]) k).
  { intros k [Hk|Hk]; [left; exact Hk | right]. apply in_app_iff; right; apply in_app_iff; left. apply HinK; exact Hk. }
  assert (Hpk: vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)])
                   (p_pknext P)).
  { destruct Hc as [Hc|Hc]; [left; exact Hc | right; apply in_app_iff; left; exact Hc]. }
  repeat (apply Forall_cons; [first [assumption | apply Hslot; assumption] |]); apply Forall_nil.
Qed.
