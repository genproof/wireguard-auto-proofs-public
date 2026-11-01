(* law keypairs: operation 2 of the loop body (hkp5_sOp2). *)
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
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp2_rel.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Pure facts (adapted from v1's hkp4_segOp2)                              *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_segOp2_nin (a: val) (L: list val) : ~ In a (vremove a L).
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [exact IH|]. simpl. intros [Hx|Hin]; [congruence | exact (IH Hin)].
Qed.

Lemma hkp5_segOp2_vin (a: val) (L: list val) : vin a (vremove a L) = false.
Proof.
  unfold vin. destruct (in_dec eq_dec a (vremove a L)) as [Hin|]; [|reflexivity].
  exfalso. exact (hkp5_segOp2_nin a L Hin).
Qed.

Lemma hkp5_segOp2_eqb l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hkp5_segOp2_zf T T' a E H :
  zeroed_from (snap_of T a E H) (snap_of T' a E (hs_zero H)) = true.
Proof.
  unfold zeroed_from, snap_of, hs_zero.
  cbn [sn_hs sn_entry hs_state hs_rindex hs_eph hs_reph hs_hash hs_ck hs_lic hs_sid hs_rstatic hs_ss hs_psk hs_ts].
  rewrite !hkp5_segOp2_eqb, !Int.eq_true, Int64.eq_true, !if_true by reflexivity.
  reflexivity.
Qed.

Lemma hkp5_segOp2_head {A: Type} (l: list (val * A)) m v : hk5_head (aupd l m v) = hk5_head l.
Proof. destruct l as [|[x w] l]; simpl; [reflexivity|]. destruct (EqDec_val x m); reflexivity. Qed.

Lemma hkp5_segOp2_afind {A: Type} (l: list (val * A)) m : In m (map fst l) -> exists v, afind l m = Some v.
Proof.
  induction l as [|[x w] l IH]; simpl; [contradiction|]. intros Hin.
  destruct (EqDec_val x m); [eauto|]. destruct Hin as [Hx|Hin]; [congruence | auto].
Qed.

Lemma hkp5_segOp2_inv1_head ML m : hk5_head (hk5o2_inv1 ML m) = hk5_head ML.
Proof.
  unfold hk5o2_inv1. destruct (eq_dec m nullval); [reflexivity|].
  destruct (afind ML m); [apply hkp5_segOp2_head | reflexivity].
Qed.

Lemma hkp5_segOp2_inv1_len ML m : Zlength (hk5o2_inv1 ML m) = Zlength ML.
Proof.
  rewrite <- (Zlength_map _ _ fst (hk5o2_inv1 ML m)), <- (Zlength_map _ _ fst ML).
  rewrite hk5o2_map_fst_inv1. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The live list: one node out, updated, back                              *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_segOp2_focus ML m M M' :
  afind ML m = Some M ->
  hk5_mklist ML |-- EX nx: val, (hk5_node m M nx * (hk5_node m M' nx -* hk5_mklist (aupd ML m M'))).
Proof.
  induction ML as [|[x X] ML IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x m) as [<-|Hx].
  - inv Hf. Exists (hk5_head ML). cancel. apply wand_sepcon_adjoint. cbn [hk5_mklist]. cancel.
  - sep_apply (IH Hf). Intros nx. Exists nx. cbn [hk5_mklist]. rewrite hkp5_segOp2_head.
    rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint.
    rewrite sepcon_assoc, (sepcon_comm (hk5_node x X _)), <- sepcon_assoc.
    sep_apply (wand_frame_elim (hk5_node m M' nx) (hk5_mklist (aupd ML m M'))). cancel.
Qed.

Lemma hkp5_segOp2_ptrs ML : hk5_mklist ML |-- !! Forall isptr (map fst ML).
Proof.
  induction ML as [|[m M] ML IH]; cbn [hk5_mklist map fst]; [entailer!|].
  sep_apply IH. unfold hk5_node. Intros. entailer!.
Qed.

Lemma hkp5_segOp2_ptr (ML: list (val * hk5_mk)) m :
  Forall isptr (map fst ML) -> m = nullval \/ In m (map fst ML) -> is_pointer_or_null m.
Proof.
  intros HF [-> | Hin]; [simpl; auto|]. rewrite Forall_forall in HF. specialize (HF _ Hin).
  destruct m; try contradiction; exact I.
Qed.

Lemma hkp5_segOp2_node_store m M nx :
  hk5_node m M nx =
  (!! (Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32) &&
   (@data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m * @malloc_token W_keypairs Ews t_mk5 m)).
Proof. reflexivity. Qed.

Lemma hkp5_segOp2_node_fold m M nx v : v = hk5_mk_val M nx ->
  Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  (@data_at W_keypairs Ews t_mk5 v m * @malloc_token W_keypairs Ews t_mk5 m) |-- hk5_node m M nx.
Proof. intros -> L1 L2. unfold hk5_node. apply andp_right; [apply prop_right; auto | apply derives_refl]. Qed.

(* ---------------------------------------------------------------------- *)
(* The handshake's entry (in the pool) and last_sent_handshake, at W_keypairs, rooted at p *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hkp5_segOp2_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkp5_segOp2_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = (f (a, sh, E) * iter_sepcon f (sdel D a)).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hkp5_segOp2_hscs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_segOp2_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_segOp2_pcs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_segOp2_CCE) t_peer = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_segOp2_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_keypairs (Tstruct KC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_keypairs hkp5_segOp2_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hkp5_segOp2_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_keypairs (Tstruct KC._wg_peer noattr) [StructField KC._handshake] p = hs_addr p.
Proof. intros H. apply hkp5_segOp2_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hkp5_segOp2_entry sh E nx hd p : @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s (entry_val E nx hd) (hs_addr p) =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
    (entry_val E nx hd) p.
Proof.
  intros FC.
  change [StructField KC._entry; StructField KC._handshake] with ([StructField KC._entry] ++ [StructField KC._handshake]).
  rewrite (@field_at_app W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._entry] [StructField KC._handshake]
             (entry_val E nx hd) (entry_val E nx hd) p (JMeq_refl _)).
  rewrite hkp5_segOp2_hsaddr by exact FC.
  transitivity (@field_at Noise.CS sh t_hs (DOT I._entry) (entry_val E nx hd) (hs_addr p)).
  2: { exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_keypairs hkp5_segOp2_CCE sh t_hs
           [StructField I._entry] (entry_val E nx hd) (entry_val E nx hd) (JMeq_refl _) hkp5_segOp2_hscs)). }
  assert (FC1: @field_compatible Noise.CS t_peer (DOT I._handshake) p) by auto with field_compatible.
  assert (FC2: @field_compatible Noise.CS t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: @field_compatible Noise.CS t_hs (DOT I._entry) (hs_addr p)) by auto with field_compatible.
  rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hkp5_segOp2_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
   @field_at W_keypairs she (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
     (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) p *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hkp5_segOp2_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hkp5_segOp2_entry by exact FC.
  apply pred_ext; entailer!.
Qed.

Lemma hkp5_segOp2_lsh sh p l :
  @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong l) p =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._last_sent_handshake] (Vlong l) p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W_keypairs hkp5_segOp2_CCE sh t_peer
           [StructField I._last_sent_handshake] (Vlong l) (Vlong l) (JMeq_refl _) hkp5_segOp2_pcs)).
Qed.

(* peer_rep without last_sent_handshake *)
Definition hkp5_segOp2_prest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hkp5_segOp2_peer sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._last_sent_handshake] (Vlong (p_lsh P)) p *
    hkp5_segOp2_prest sh p P)).
Proof.
  rewrite <- hkp5_segOp2_lsh. unfold peer_rep, hkp5_segOp2_prest.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hkp5_segOp2_peer_fold sh p P : @field_compatible Noise.CS t_peer [] p ->
  (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._last_sent_handshake] (Vlong (p_lsh P)) p *
   hkp5_segOp2_prest sh p P) |-- peer_rep sh p P.
Proof.
  intros Hfc. rewrite hkp5_segOp2_peer. apply andp_right; [apply prop_right; exact Hfc | apply derives_refl].
Qed.

Lemma hkp5_segOp2_lsh_eq now :
  Int64.eq (reset_lsh now) (Int64.sub now (Int64.mul (Int64.repr 6) (Int64.repr (Int.signed (Int.repr 1000000000)))))
  = true.
Proof.
  unfold reset_lsh.
  replace (Int64.mul (Int64.repr 6) (Int64.repr (Int.signed (Int.repr 1000000000))))
    with (Int64.repr (6 * NSEC_PER_SEC)) by reflexivity.
  apply Int64.eq_true.
Qed.

Ltac hkp5_segOp2_false :=
  first [ match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end
        | match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end
        | match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end
        | match goal with Hc: Int.repr (Z.b2z _) = Int.zero |- _ =>
            rewrite ?hkp5_segOp2_lsh_eq, ?Int64.eq_true, ?Int.eq_true in Hc; exact (Int.one_not_zero Hc) end ].

Lemma hkp5_segOp2_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op2) (hkp5_PL0 x25519 F V steps FR i 2) hkp5_sOp2
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  intros HF HX.
  destruct HF as (HMpre & HMslots & HMperm & HMput & HMputh & HMget).
  unfold hkp5_PL0, hkp5_sOp2.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ww kc P KS T HH now next_id id_known hsn].
  cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn] in *.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second
       y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  pose proof H1 as Hinv.
  destruct H1 as (Hrel & Hwarn & Hdev & Hsid & Hrefs & Hfr & Hal & Hid & Hnow & Hhsm).
  cbn [y_P y_H y_KS y_T y_S y_w y_kc y_now y_next_id y_id_known y_hsn f_w f_p] in
    Hrel, Hwarn, Hdev, Hsid, Hrefs, Hfr, Hal, Hid, Hnow, Hhsm.
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
    f_snap := snap; f_opub := opub; f_first := first; f_second := second |}) in *.
  match goal with |- context [loop1_ret_assert _ ?R] => destruct R as [Rn Rb Rc Rr] end.
  unfold loop1_ret_assert.
  unfold hkp5_Delta.
  abbreviate_semax.
  pose proof Hrel as (Hcore & HNDsl & Hp & Hc & Hn).
  destruct (HMpre _ _ _ _ _ _ _ Hcore) as (Hkpool & Hhpool & Hnk & Hslotkp & Hinj).
  pose proof (HMslots _ _ _ _ _ _ _ Hrel) as Hslots.
  pose proof Hcore as (_ & _ & _ & _ & _ & Hsl & _ & _ & Hpool).
  pose proof Hpool as (_ & _ & _ & _ & (idx & Hhs) & _).
  set (E := mkEntry p IDX_HANDSHAKE idx) in *.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfcp by (unfold peer_rep; entailer!).
  assert_PROP (isptr w) as Pw by (unfold device_rep; entailer!).
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  assert (Pp: isptr p) by (destruct Hfcp; auto).
  assert (HtE: t_entry T (hs_addr p) = Some E) by (unfold t_entry; rewrite Hhs; reflexivity).
  forward_call (Tsh, snap, Tsh, p, P, Tsh, t, T, E).
  { split; [unfold E; cbn [e_peer]; destruct p; try contradiction; discriminate |].
    rewrite Hsid. unfold id_addr. destruct w; try contradiction; discriminate. }
  change (itable Tsh t T) with (itable Tsh (d_itab (hkp5_D x25519 F0 V)) T).
  forward_call (gv, S, ww, KS, T, Tsh, p, P, Tsh, w, hkp5_D x25519 F0 V, Tsh).
  rewrite H4.
  assert (EP1: fst (fst (expire_model P (hs_addr p) KS T now)) =
               p_set_lsh (p_set_hs P (hs_zero (p_hs P))) (reset_lsh now)) by reflexivity.
  assert (ET1: snd (expire_model P (hs_addr p) KS T now) = t_remove T (hs_addr p)) by reflexivity.
  assert_PROP (itable_wf (snd (expire_model P (hs_addr p) KS T now))) as Hwf1 by (unfold itable; entailer!).
  pose proof (hk5o2_rel p (v_OD V) (v_OH V) HH P KS T now ltac:(rewrite <- ET1; exact Hwf1) Hrel) as Hrel1.
  rewrite EP1, ET1 in *.
  set (KS1 := snd (fst (expire_model P (hs_addr p) KS T now))) in *.
  set (P1 := p_set_lsh (p_set_hs P (hs_zero (p_hs P))) (reset_lsh now)) in *.
  set (T1 := t_remove T (hs_addr p)) in *.
  change (d_itab (hkp5_D x25519 F0 V)) with t.
  set (sn := snap_of T (hs_addr p) E (p_hs P)).
  assert (Hhs1: sfind (t_D T1) (hs_addr p) = Some (Tsh, E)) by exact Hhs.
  assert (HtE1: t_entry T1 (hs_addr p) = Some E) by (unfold t_entry; rewrite Hhs1; reflexivity).
  assert (Hvin1: vin (hs_addr p) (t_L T1) = false) by (unfold T1, t_remove; cbn [t_L]; apply hkp5_segOp2_vin).
  assert (ZF: zeroed_from sn (snap_of T1 (hs_addr p) E (p_hs P1)) = true) by apply hkp5_segOp2_zf.
  assert (Hcmp: hk5_cmp_pre sn T1 p w P1 E).
  { unfold hk5_cmp_pre. split; [exact HtE1 |].
    split; [reflexivity |]. split; [reflexivity |]. split; [exact Hsid | exact Hsid]. }
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, snap, sn, Tsh, p, P1, Tsh, t, T1, E, Tsh, w, hkp5_D x25519 F0 V).
    rewrite ZF.
    forward_if (temp KC._t'47 (Vint Int.one)).
    { pose proof (hkp5_segOp2_open Tsh t T1 p Tsh E Hfcp Hwf1 Hhs1) as OP. rewrite Hvin1 in OP.
      rewrite OP. Intros.
      forward. forward.
      sep_apply (derives_refl' _ _ (eq_sym OP)). entailer!. }
    { exfalso. hkp5_segOp2_false. }
    forward_if.
    { exfalso. hkp5_segOp2_false. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  rewrite (hkp5_segOp2_peer Tsh p P1). Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    { exfalso. hkp5_segOp2_false. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hkp5_segOp2_peer_fold Tsh p P1 Hfcp).
  sep_apply (@data_at_data_at_ HCS Ews t_hsnap (hsnap_val hsn) (gv KC._hsm)).
  forward_call (Ews, gv KC._hsm, Tsh, p, P1, Tsh, t, T1, E).
  { split; [unfold E; cbn [e_peer]; destruct p; try contradiction; discriminate |].
    unfold P1. cbn [p_hs p_set_lsh p_set_hs hs_zero hs_sid]. rewrite Hsid. unfold id_addr.
    destruct w; try contradiction; discriminate. }
  set (hsn1 := snap_of T1 (hs_addr p) E (p_hs P1)).
  rewrite (hkp5_segOp2_peer Tsh p P1). Intros.
  forward. forward.
  sep_apply (hkp5_segOp2_peer_fold Tsh p P1 Hfcp).
  match goal with |- context [data_at Ews (Tstruct KC._pr_snap noattr) ?v (gv KC._prm)] =>
    replace v with (hk5_prsnap_val P1) by reflexivity end.
  assert_PROP (Forall isptr (map fst (h5_ML HH))) as Hptrs
    by (sep_apply (hkp5_segOp2_ptrs (h5_ML HH)); entailer!).
  assert (Hsl3: h5_sn HH = nullval \/ In (h5_sn HH) (map fst (h5_ML HH)))
    by (rewrite Forall_forall in Hsl; apply Hsl; simpl; auto).
  assert (Hsl2: h5_sc HH = nullval \/ In (h5_sc HH) (map fst (h5_ML HH)))
    by (rewrite Forall_forall in Hsl; apply Hsl; simpl; auto).
  forward.
  { entailer!. exact (hkp5_segOp2_ptr _ _ Hptrs Hsl3). }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (hk5_mklist (h5_ML HH)) in R in
    match R' with ?f _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (f (hk5_mklist (hk5o2_inv1 (h5_ML HH) (h5_sn HH))))))) end end.
  { destruct Hsl3 as [Hn0 | Hin].
    - rewrite Hn0. entailer!.
    - destruct (hkp5_segOp2_afind _ _ Hin) as [M HfM].
      sep_apply (hkp5_segOp2_focus (h5_ML HH) (h5_sn HH) M M HfM). Intros nx.
      rewrite (hkp5_segOp2_node_store (h5_sn HH) M nx). Intros.
      entailer!. }
  { destruct Hsl3 as [Hn0 | Hin]; [contradiction |].
    destruct (hkp5_segOp2_afind _ _ Hin) as [M HfM].
    sep_apply (hkp5_segOp2_focus (h5_ML HH) (h5_sn HH) M (m5_invalidate_send M) HfM). Intros nx.
    rewrite (hkp5_segOp2_node_store (h5_sn HH) M nx). Intros.
    forward. forward.
    match goal with |- context [@data_at ?cs Ews ?ty ?v (h5_sn HH)] =>
      assert (Hv: v = hk5_mk_val (m5_invalidate_send M) nx) by reflexivity;
      sep_apply (hkp5_segOp2_node_fold (h5_sn HH) (m5_invalidate_send M) nx v Hv ltac:(assumption) ltac:(assumption)) end.
    sep_apply (wand_frame_elim (hk5_node (h5_sn HH) (m5_invalidate_send M) nx)
                 (hk5_mklist (aupd (h5_ML HH) (h5_sn HH) (m5_invalidate_send M)))).
    unfold hk5o2_inv1. rewrite if_false by assumption. rewrite HfM.
    entailer!. }
  { forward. unfold hk5o2_inv1. rewrite if_true by assumption. entailer!. }
  set (ML1 := hk5o2_inv1 (h5_ML HH) (h5_sn HH)) in *.
  assert (Hsl2': h5_sc HH = nullval \/ In (h5_sc HH) (map fst ML1))
    by (unfold ML1; rewrite hk5o2_map_fst_inv1; exact Hsl2).
  forward.
  { entailer!. exact (hkp5_segOp2_ptr _ _ Hptrs Hsl2). }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern (hk5_mklist ML1) in R in
    match R' with ?f _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (f (hk5_mklist (hk5o2_inv1 ML1 (h5_sc HH))))))) end end.
  { destruct Hsl2' as [Hn0 | Hin].
    - rewrite Hn0. entailer!.
    - destruct (hkp5_segOp2_afind _ _ Hin) as [M HfM].
      sep_apply (hkp5_segOp2_focus ML1 (h5_sc HH) M M HfM). Intros nx.
      rewrite (hkp5_segOp2_node_store (h5_sc HH) M nx). Intros.
      entailer!. }
  { destruct Hsl2' as [Hn0 | Hin]; [contradiction |].
    destruct (hkp5_segOp2_afind _ _ Hin) as [M HfM].
    sep_apply (hkp5_segOp2_focus ML1 (h5_sc HH) M (m5_invalidate_send M) HfM). Intros nx.
    rewrite (hkp5_segOp2_node_store (h5_sc HH) M nx). Intros.
    forward. forward.
    match goal with |- context [@data_at ?cs Ews ?ty ?v (h5_sc HH)] =>
      assert (Hv: v = hk5_mk_val (m5_invalidate_send M) nx) by reflexivity;
      sep_apply (hkp5_segOp2_node_fold (h5_sc HH) (m5_invalidate_send M) nx v Hv ltac:(assumption) ltac:(assumption)) end.
    sep_apply (wand_frame_elim (hk5_node (h5_sc HH) (m5_invalidate_send M) nx)
                 (hk5_mklist (aupd ML1 (h5_sc HH) (m5_invalidate_send M)))).
    unfold hk5o2_inv1 at 1. rewrite if_false by assumption. rewrite HfM.
    entailer!. }
  { forward. unfold hk5o2_inv1 at 1. rewrite if_true by assumption. entailer!. }
  set (H1 := h5_set_ML HH (hk5o2_inv1 ML1 (h5_sc HH))) in *.
  set (Y' := mkKY5 S ww kc P1 KS1 T1 H1 now next_id id_known hsn1).
  assert (Hinv': hkp5_inv F0 V Y').
  { unfold hkp5_inv, Y'. cbn [y_P y_H y_KS y_T y_S y_w y_kc y_now y_next_id y_id_known y_hsn].
    refine (conj Hrel1 (conj Hwarn (conj _ (conj _ (conj Hrefs (conj Hfr (conj _ (conj Hid (conj Hnow _))))))))).
    - unfold P1, F0. cbn [p_device p_set_lsh p_set_hs f_w]. exact Hdev.
    - unfold P1, F0. cbn [p_hs p_set_lsh p_set_hs hs_zero hs_sid f_w]. exact Hsid.
    - unfold H1, h5_set_ML. cbn [h5_frees h5_ML]. unfold ML1. rewrite !hkp5_segOp2_inv1_len. exact Hal.
    - split; [| unfold P1; exact (proj2 Hhsm)].
      unfold hk5_hsm_ok, hsn1, snap_of. cbn [sn_entry sn_hashed sn_hs]. split; [exact HtE1 | split; reflexivity]. }
  assert (Hhead: hk5_head (h5_ML H1) = hk5_head (h5_ML HH)).
  { unfold H1, h5_set_ML. cbn [h5_ML]. unfold ML1. rewrite !hkp5_segOp2_inv1_head. reflexivity. }
  unfold hkp5_Icont, hkp5_St. Exists Y'.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  unfold Y'. cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second
       y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  fold Y'. rewrite Hhead.
  change (h5_ML H1) with (hk5o2_inv1 ML1 (h5_sc HH)).
  change (h5_sp H1) with (h5_sp HH). change (h5_sc H1) with (h5_sc HH). change (h5_sn H1) with (h5_sn HH).
  change (h5_frees H1) with (h5_frees HH). change (h5_warn H1) with (h5_warn HH).
  sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val sn) snap).
  subst F0. cbn [f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second].
  entailer!.
Qed.
