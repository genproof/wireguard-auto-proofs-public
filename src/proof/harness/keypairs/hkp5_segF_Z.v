(* law keypairs, segment F piece Z: statements 38..40 of main
   (kents_free(kes); hnodes_free(others); return 0), hkp5_segF_defs.v: main's locals back to data_at_ (the stack
   frame), everything else into TT. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
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
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_defs.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The pool: the entries at a list of distinct addresses out, the rest TT  *)
(* ---------------------------------------------------------------------- *)

Lemma hk5Fz_sfind_sdel {A: Type} (D: list (val * share * A)) a k : a <> k -> sfind (sdel D k) a = sfind D a.
Proof.
  intros N. induction D as [|[[x sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|Nx]; simpl.
  - destruct (EqDec_val x a); [congruence | reflexivity].
  - destruct (EqDec_val x a); [reflexivity | exact IH].
Qed.

Definition hk5Fz_ent (D0: list (val * share * entry)) (a: val) : mpred :=
  EX sh: share, EX E: entry, EX n: val, EX h: bool, !! (sfind D0 a = Some (sh, E)) && entry_at sh a E n h.

Lemma hk5Fz_extract (LT: list val) (D0: list (val * share * entry)) : forall L D,
  NoDup L -> NoDup (saddrs D) ->
  (forall a, In a L -> In a (saddrs D) /\ sfind D a = sfind D0 a) ->
  iter_sepcon (pool_item_rep LT) D |-- iter_sepcon (hk5Fz_ent D0) L * TT.
Proof.
  induction L as [|a L IH]; intros D ND NDD HL.
  - simpl. rewrite emp_sepcon. apply TT_right.
  - inv ND. destruct (HL a (or_introl eq_refl)) as [Ia Ea].
    destruct (prot_rep3_sfind_in D a Ia) as (sh & E & Es).
    rewrite (prot_rep3_split D a sh E _ Es). simpl.
    unfold hk5Fz_ent at 1. Exists sh E (succ_in LT a) (vin a LT).
    rewrite prop_true_andp by congruence. rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
    apply IH; auto.
    + apply prot_rep3_sdel_nodup; auto.
    + intros b Ib. assert (Nb: b <> a) by (intros ->; contradiction).
      destruct (HL b (or_intror Ib)) as [Ib1 Eb]. rewrite hk5Fz_sfind_sdel by auto. split; [|auto].
      destruct (prot_rep3_sfind_in D b Ib1) as (sh' & E' & Es').
      apply (prot_rep3_saddrs_in _ _ sh' E'). apply prot_rep3_sfind_In.
      rewrite hk5Fz_sfind_sdel by auto. exact Es'.
Qed.

Lemma hk5Fz_kents (D0: list (val * share * entry)) (KE: list kent4) :
  (forall e, In e KE -> exists E, sfind D0 (ke_addr e) = Some (Ews, E)) ->
  iter_sepcon (hk5Fz_ent D0) (map ke_addr KE) |--
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  intros HK. rewrite <- (iter_sepcon_map KE (hk5Fz_ent D0) ke_addr).
  apply iter_sepcon_derives. intros e Ie. unfold hk5Fz_ent. Intros sh E n h.
  destruct (HK e Ie) as [E' HE]. rewrite HE in H. inv H.
  unfold entry_at. apply data_at_data_at_.
Qed.

#[local] Instance hk5Fz_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.
#[local] Instance hk5Fz_CCEH : change_composite_env HCS W_keypairs.
Proof. make_cs_preserve HCS W_keypairs. Defined.

Lemma hk5Fz_cs_peer sh p :
  @data_at_ Noise.CS sh t_peer p = @data_at_ W_keypairs sh (Tstruct KC._wg_peer noattr) p.
Proof.
  change (Tstruct KC._wg_peer noattr) with t_peer.
  rewrite (@data_at__change_composite Noise.CS W_keypairs hk5Fz_CCE sh t_peer) by reflexivity; reflexivity.
Qed.

Lemma hk5Fz_cs_peer_d sh p :
  @data_at_ Noise.CS sh t_peer p |-- @data_at_ W_keypairs sh t_peer p.
Proof. rewrite hk5Fz_cs_peer. apply derives_refl. Qed.

Lemma hk5Fz_peers (D0: list (val * share * entry)) : forall PS NS,
  hnodes_peers4 NS PS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  (forall x, In x PS -> exists E, sfind D0 (hs_addr (peer_addr4 x)) = Some (Ews, E)) ->
  iter_sepcon (hk5Fz_ent D0) (map (fun x => hs_addr (peer_addr4 x)) PS) * peers_rep PS |--
  iter_sepcon (fun N => @data_at_ W_keypairs Ews t_peer (hn_p N)) NS.
Proof.
  unfold hnodes_peers4.
  induction PS as [| [[q sh] Q] PS IH]; intros NS HN HF HE; destruct NS as [| N NS]; try discriminate HN.
  - simpl. unfold peers_rep. simpl. rewrite sepcon_emp. apply derives_refl.
  - simpl in HN. injection HN as Hq HN. inv HF.
    unfold peers_rep. simpl. unfold hk5Fz_ent at 1. Intros sh' E n h.
    destruct (HE (hn_p N, Ews, Q) (or_introl eq_refl)) as [E' HE']. cbn [peer_addr4] in HE'. rewrite HE' in H. inv H.
    sep_apply (prot_rep3_peer_whole Ews (hn_p N) Q E n h).
    sep_apply (hk5Fz_cs_peer_d Ews (hn_p N)).
    cancel. unfold peers_rep in IH. apply (IH NS); auto.
    intros x Ix. apply HE. right. exact Ix.
Qed.

Lemma hk5Fz_self (D0: list (val * share * entry)) p P E0 :
  sfind D0 (hs_addr p) = Some (Tsh, E0) ->
  hk5Fz_ent D0 (hs_addr p) * peer_rep Tsh p P |-- @data_at_ Noise.CS Tsh t_peer p.
Proof.
  intros HE. unfold hk5Fz_ent. Intros sh E n h. rewrite HE in H. inv H.
  sep_apply (prot_rep3_peer_whole Tsh p P E n h). apply derives_refl.
Qed.

(* the index table, P and the other peers: the table's struct, P's struct, the kents' entries and the other
   peers' structs out (as kents_free / hnodes_free take them), the rest of the pool (P's keypairs) into TT *)
Lemma hk5Fz_pool (tab p: val) (T: tstate) (P: peer) (PS: list (val * share * peer)) (NS: list hnode4)
    (KE: list kent4) E0 :
  sfind (t_D T) (hs_addr p) = Some (Tsh, E0) ->
  NoDup (hs_addr p :: map (fun x => hs_addr (peer_addr4 x)) PS ++ map ke_addr KE) ->
  (forall a, In a (hs_addr p :: map (fun x => hs_addr (peer_addr4 x)) PS ++ map ke_addr KE) ->
     In a (saddrs (t_D T))) ->
  (forall e, In e KE -> exists E, sfind (t_D T) (ke_addr e) = Some (Ews, E)) ->
  (forall x, In x PS -> exists E, sfind (t_D T) (hs_addr (peer_addr4 x)) = Some (Ews, E)) ->
  hnodes_peers4 NS PS -> Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  itable Tsh tab T * peer_rep Tsh p P * peers_rep PS |--
  @data_at_ Noise.CS Tsh t_itab tab * @data_at_ Noise.CS Tsh t_peer p *
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE *
  iter_sepcon (fun N => @data_at_ W_keypairs Ews t_peer (hn_p N)) NS * TT.
Proof.
  intros HP ND HIn HK HPS HN HF.
  unfold itable. Intros. destruct H as (_ & _ & NDD & _).
  sep_apply (hk5Fz_extract (t_L T) (t_D T) _ (t_D T) ND NDD (fun a Ia => conj (HIn a Ia) eq_refl)).
  cbn [iter_sepcon]. rewrite iter_sepcon_app.
  sep_apply (hk5Fz_self (t_D T) p P E0 HP).
  sep_apply (hk5Fz_kents (t_D T) KE HK).
  sep_apply (hk5Fz_peers (t_D T) PS NS HN HF HPS).
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_itab (hd nullval (t_L T)) tab).
  cancel.
Qed.

(* the pure side: the pool of hk5_rel and the other peers' facts *)
Lemma hk5Fz_facts p OD OH KS T (PS: list (val * share * peer)) (KE: list kent4) :
  hk5_pool p OD OH KS T ->
  (forall a, In a (saddrs OD) <-> In a (map hs_addr (map peer_addr4 PS)) \/ In a (map ke_addr KE)) ->
  NoDup (map hs_addr (map peer_addr4 PS) ++ map ke_addr KE) ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) OD ->
  exists E0, sfind (t_D T) (hs_addr p) = Some (Tsh, E0) /\
  NoDup (hs_addr p :: map (fun x => hs_addr (peer_addr4 x)) PS ++ map ke_addr KE) /\
  (forall a, In a (hs_addr p :: map (fun x => hs_addr (peer_addr4 x)) PS ++ map ke_addr KE) ->
     In a (saddrs (t_D T))) /\
  (forall e, In e KE -> exists E, sfind (t_D T) (ke_addr e) = Some (Ews, E)) /\
  (forall x, In x PS -> exists E, sfind (t_D T) (hs_addr (peer_addr4 x)) = Some (Ews, E)).
Proof.
  intros (Hiff & Hnp & HnOD & _ & (idx & Hidx) & HOD & _) HO ND HE.
  assert (KEY: forall a, In a (saddrs OD) -> exists E, sfind (t_D T) a = Some (Ews, E)).
  { intros a Ia. unfold saddrs in Ia. apply in_map_iff in Ia as ([[a' sh] E] & Ea & Ix). cbn in Ea. subst a'.
    rewrite Forall_forall in HOD, HE. specialize (HOD _ Ix). specialize (HE _ Ix). cbn in HOD, HE.
    subst sh. exists E. apply HOD. }
  rewrite <- (map_map peer_addr4 hs_addr).
  exists (mkEntry p IDX_HANDSHAKE idx). split; [exact Hidx|].
  split; [| split; [| split]].
  - constructor; [| exact ND]. intros I. apply HnOD. apply HO. apply in_app_or in I. exact I.
  - intros a [<-|I]; apply Hiff; [left; reflexivity|]. right; right. apply HO. apply in_app_or in I. exact I.
  - intros e Ie. apply KEY. apply HO. right. apply in_map. exact Ie.
  - intros x Ix. apply KEY. apply HO. left. rewrite map_map. apply (in_map (fun x => hs_addr (peer_addr4 x))). exact Ix.
Qed.

(* ---------------------------------------------------------------------- *)
(* The stack frame *)
(* ---------------------------------------------------------------------- *)

Section CloseNoise.
#[local] Existing Instance Noise.CS.
Lemma hk5Fz_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep, id_addr, cc_addr.
  Intros. Intros lk1 lk2.
  unfold_data_at (data_at_ sh t_dev wg).
  rewrite (field_at_data_at sh t_dev [StructField I._static_identity]).
  rewrite (field_at_data_at sh t_dev [StructField I._cookie_checker]).
  rewrite !field_address_offset by auto with field_compatible.
  rewrite <- !sepcon_assoc.
  repeat apply sepcon_derives; first [exact (field_at_field_at_ _ _ _ _ _) | exact (data_at_data_at_ _ _ _ _)].
Qed.
End CloseNoise.

Lemma hk5Fz_cs_dev sh p :
  @data_at_ Noise.CS sh t_dev p = @data_at_ W_keypairs sh (Tstruct KC._wg_device noattr) p.
Proof.
  change (Tstruct KC._wg_device noattr) with t_dev.
  rewrite (@data_at__change_composite Noise.CS W_keypairs hk5Fz_CCE sh t_dev) by reflexivity; reflexivity.
Qed.
Lemma hk5Fz_cs_itab sh p :
  @data_at_ Noise.CS sh t_itab p = @data_at_ W_keypairs sh (Tstruct KC._index_hashtable noattr) p.
Proof.
  change (Tstruct KC._index_hashtable noattr) with t_itab.
  rewrite (@data_at__change_composite Noise.CS W_keypairs hk5Fz_CCE sh t_itab) by reflexivity; reflexivity.
Qed.
Lemma hk5Fz_cs_ptab sh p :
  @data_at_ Noise.CS sh t_ptab p = @data_at_ W_keypairs sh (Tstruct KC._pubkey_hashtable noattr) p.
Proof.
  change (Tstruct KC._pubkey_hashtable noattr) with t_ptab.
  rewrite (@data_at__change_composite Noise.CS W_keypairs hk5Fz_CCE sh t_ptab) by reflexivity; reflexivity.
Qed.
Lemma hk5Fz_cs_snap sh p :
  @data_at_ HCS sh t_hsnap p = @data_at_ W_keypairs sh (Tstruct KC._hs_snap noattr) p.
Proof.
  change (Tstruct KC._hs_snap noattr) with t_hsnap.
  rewrite (@data_at__change_composite HCS W_keypairs hk5Fz_CCEH sh t_hsnap) by reflexivity; reflexivity.
Qed.

Lemma hk5Fz_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hkp5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

Lemma hk5Fz_hn_pn l NS : hnodes_rep4 W_keypairs l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hk5Fz_ke_pn l KE : kents_rep W_keypairs l KE |-- !! is_pointer_or_null l.
Proof.
  destruct KE as [| e KE]; cbn [kents_rep].
  - entailer!.
  - Intros nx. subst l. unfold kent_cell. Intros. entailer!.
    match goal with X: field_compatible _ _ (ke_addr e) |- _ => destruct X as [Hp _] end.
    destruct (ke_addr e); try contradiction; simpl; auto.
Qed.

Lemma hkp5_segF_Z_core {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) (FR: mpred) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_oth_ok F V O ->
  NoDup (map hs_addr (map peer_addr4 (o_PS O)) ++ map ke_addr (o_KE O)) ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (o_PS O) ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (v_OD V) ->
  semax (hkp5_Delta (hkp5_G_F x25519)) (hkp5F_S x25519 F V steps O FR hkp5F_P2) hkp5F_sZ
    (overridePost FF (hkp5_R (f_gv F))).
Proof.
  intros MF HX HO Hnd HsP HsD.
  unfold hkp5F_S, hkp5_R. apply hk5Fz_post_canon.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct O as [hd NS PS kd KE T0].
  destruct Y as [S wn kc P KS T HH now next_id id_known hsn].
  destruct H as (LR & LP & _).
  destruct H0 as ((Hcore & _) & _).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & Hpool).
  destruct HO as (Hnp & _ & _ & _ & _ & _ & Hiff & _).
  cbn [f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second o_hd o_NS o_PS o_kd o_KE o_T0
       y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn] in *.
  destruct (hk5Fz_facts p (v_OD V) (v_OH V) KS T PS KE Hpool Hiff Hnd HsD) as (E0 & F1 & F2 & F3 & F4 & F5).
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars, hkp5_othR, hkp5_oth_rep.
  cbn [app fold_right_sepcon f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second o_hd o_NS o_PS o_kd
       o_KE o_T0 y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  unfold hkp5_Delta, hkp5F_sZ. abbreviate_semax.
  rewrite sepcon_emp.
  sep_apply (hk5Fz_pool t p T P PS NS KE E0 F1 F2 F3 F4 F5 Hnp HsP).
  Intros.
  assert_PROP (is_pointer_or_null kd) as Pkd by (sep_apply (hk5Fz_ke_pn kd KE); entailer!).
  assert_PROP (is_pointer_or_null hd) as Phd by (sep_apply (hk5Fz_hn_pn hd NS); entailer!).
  forward.
  forward_call (gv, kd, KE).
  forward.
  forward_call (gv, hd, NS).
  forward.
  sep_apply (hk5Fz_dev Tsh w (hkp5_D x25519 {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw;
    f_pub := pub; f_snap := snap; f_opub := opub; f_first := first; f_second := second |} V)).
  unfold ptable. sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab (v_head V) pt).
  unfold hbytes, hout. rewrite LR, LP.
  sep_apply (@data_at_data_at_ HCS Tsh (tarray tuchar 32) (bytes (v_RAW V)) raw).
  sep_apply (@data_at_data_at_ HCS Tsh (tarray tuchar 32) (bytes (v_PUB V)) pub).
  rewrite hk5Fz_cs_dev, hk5Fz_cs_itab, hk5Fz_cs_ptab, hk5Fz_cs_peer, hk5Fz_cs_snap.
  rewrite !(prot_rep3_data_at__cs HCS W_keypairs).
  cancel.
Qed.

Lemma hkp5_segF_Z_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) (FR: mpred) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_F x25519)) (hkp5F_S x25519 F V steps O FR hkp5F_P2) hkp5F_sZ
    (overridePost FF (hkp5_R (f_gv F))).
Proof.
  intros MF HX HO. pose proof HO as HO'.
  destruct HO' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & HsP & HsD).
  apply hkp5_segF_Z_core; auto.
Qed.
