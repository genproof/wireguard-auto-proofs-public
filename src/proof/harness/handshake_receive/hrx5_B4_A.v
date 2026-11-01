(* law handshake_receive, phase B4, segment A: statements 21..24 (tw, fwd, hnodes_snap, kents_snap): hrx5_S3 -> hrx5_B4_S3b. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

(* ---- helpers (port of consume_initiation_any hci5_P6 / consume_response_any hcr5_q2_lem) ---- *)
Lemma hrx5_B4_A_ptrs PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  induction PS as [| [[a sh] P] PS IH]; unfold peers_rep in *; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_item_rep at 1, peer_rep. entailer!.
    constructor; [cbn; destruct H0; assumption | assumption].
Qed.

Lemma hrx5_B4_A_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hrx5_B4_A_img_split sh bs p :
  4 <= Zlength bs -> @field_compatible HCS (tarray tuchar (Zlength bs)) [] p ->
  hbytes sh bs p = hbytes sh (sublist 0 4 bs) p * hbytes sh (sublist 4 (Zlength bs) bs) (offset_val 4 p).
Proof.
  intros Lb FC. unfold hbytes. rewrite !Zlength_sublist by lia.
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) 4) by (try lia; unfold bytes; rewrite Zlength_map; lia).
  rewrite field_address0_offset by auto with field_compatible.
  unfold bytes. rewrite !sublist_map. simpl nested_field_type. simpl nested_field_offset.
  replace (0 + 1 * 4) with 4 by lia. replace (4 - 0) with 4 by lia. reflexivity.
Qed.

Lemma hrx5_B4_A_sfind_nodup {A: Type} (D: list (val * share * A)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; simpl; [tauto |]. intros Hnd Hin.
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin]; [congruence |].
    exfalso. apply Hni. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto.
  - destruct Hin as [Heq | Hin]; [congruence | auto].
Qed.

Lemma hrx5_B4_A_entry_d T a sh E :
  NoDup (saddrs (t_D T)) -> In (a, sh, E) (t_D T) -> t_entry_d T a = E.
Proof.
  intros Hnd Hin. unfold t_entry_d, t_entry. rewrite (hrx5_B4_A_sfind_nodup _ _ _ _ Hnd Hin). reflexivity.
Qed.

Lemma hrx5_B4_A_in_saddrs {A: Type} (D: list (val * share * A)) a sh E : In (a, sh, E) D -> In a (saddrs D).
Proof. intros Hin. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto. Qed.

Lemma hrx5_B4_A_F2_in {A B: Type} (Rr: A -> B -> Prop) l1 l2 x :
  Forall2 Rr l1 l2 -> In x l1 -> exists y, In y l2 /\ Rr x y.
Proof.
  intros HF; induction HF as [| a b l1' l2' Hab HF IH]; simpl; [tauto |].
  intros [-> | Hin]; [exists b; auto |]. destruct (IH Hin) as (y & Hy & Hr). exists y; auto.
Qed.

Lemma hrx5_B4_A_snap_pre x25519 R L NS PS KE T head nk :
  hrx5_inv x25519 R L NS PS KE T head nk -> itable_wf T ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> isptr (l_wd L) ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
            hs_sid (p_hs P) <> Vundef /\
            Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS.
Proof.
  intros (Hpok & _ & _ & _ & _ & _ & _ & Hhs) (_ & _ & Hnd & _) Hptr Hwd.
  apply Forall_forall. intros [[p sh] P] Hin.
  rewrite Forall_forall in Hpok, Hptr.
  pose proof (Hptr _ Hin) as Hp. cbn in Hp.
  destruct (Hpok _ Hin) as (_ & Hdev & Hsid & _ & _ & _ & _ & Hpk & Hc & Hpr & Hn).
  destruct (hrx5_B4_A_F2_in _ _ _ _ Hhs Hin) as ([[a she] E] & Hy & Hr).
  cbn in Hr. destruct Hr as (-> & -> & Hpe & _).
  apply skipn_In in Hy.
  split; [| split; [| split]].
  - eapply hrx5_B4_A_in_saddrs; exact Hy.
  - rewrite (hrx5_B4_A_entry_d _ _ _ _ Hnd Hy), Hpe. destruct p; try contradiction; discriminate.
  - rewrite Hsid. unfold id_addr. destruct (l_wd L); try contradiction; discriminate.
  - rewrite Hdev, Hc, Hpr, Hn. repeat constructor; try discriminate.
    + destruct (l_wd L); try contradiction; discriminate.
    + destruct (p_pknext P); try contradiction; discriminate.
Qed.

Lemma hrx5_B4_A_ksnap_pre x25519 R L NS PS KE T head nk :
  hrx5_inv x25519 R L NS PS KE T head nk -> itable_wf T ->
  Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE.
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hke & _) (_ & _ & Hnd & _) Hptr.
  rewrite Forall_forall in Hptr.
  apply Forall_forall. intros e He.
  assert (HinK: In (ke_addr e) (map ke_addr KE)) by (apply in_map, He).
  destruct (hrx5_B4_A_F2_in _ _ _ _ Hke HinK) as ([[a she] E] & Hy & Hr).
  cbn in Hr. destruct Hr as (-> & -> & Hpe & _).
  apply firstn_In in Hy. split.
  - eapply hrx5_B4_A_in_saddrs; exact Hy.
  - rewrite (hrx5_B4_A_entry_d _ _ _ _ Hnd Hy).
    apply in_map_iff in Hpe. destruct Hpe as (x & Hx & Hx'). rewrite <- Hx.
    specialize (Hptr _ Hx'). destruct x as [[q sh] Q]. cbn in *. destruct q; try contradiction; discriminate.
Qed.

Lemma hrx5_B4_A_eq64 n k : 0 <= n <= Int64.max_unsigned -> 0 <= k <= Int64.max_unsigned ->
  Int64.eq (Int64.repr n) (Int64.repr k) = (n =? k).
Proof.
  intros. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq n k); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto.
Qed.

Lemma hrx5_B4_A_fwd msg : hrx5_fwd msg =
  let n := Zlength msg in let tw0 := if 4 <=? n then hrx5_tw msg else Int.zero in
  orb (orb (andb (Int.eq tw0 Int.one) (n =? 148)) (andb (Int.eq tw0 (Int.repr 2)) (n =? 92)))
      (andb (Int.eq tw0 (Int.repr 3)) (n =? 64)).
Proof. unfold hrx5_fwd. cbv zeta. destruct (4 <=? Zlength msg); reflexivity. Qed.

Lemma hrx5_B4_A_khead T KE : hrx5_khead (map (kent_snapped T) KE) = hrx5_khead KE.
Proof. destruct KE; reflexivity. Qed.

Lemma hrx5_B4_A_head T NS PS : hnodes_peers4 NS PS -> hrx5_head (hnodes_snapped4 T NS PS) = hrx5_head NS.
Proof.
  intros Hp. destruct NS as [| N NS]; [reflexivity |].
  destruct PS as [| x PS]; [unfold hnodes_peers4 in Hp; discriminate Hp |].
  destruct x as [[p sh] P]; reflexivity.
Qed.

Lemma hrx5_B4_A_ok : hrx5_B4_A_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH.
  unfold hrx5_S3, hrx5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w NS. Intros PS T head nk KE st. Intros i kc lul q proto ip4. Intros ip6 port o dp img.
  unfold hrx5_B4_A.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app].
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength (obj_bytes o))) [] img) as FCi.
  { unfold img_rep, hbytes. entailer!. }
  assert (Hn: 0 <= Zlength (obj_bytes o) <= Int64.max_unsigned).
  { pose proof (Zlength_nonneg (obj_bytes o)). clear - H4 H5.
    unfold malloc_compatible in H4; destruct dp as [| | | | | b0 ofs0]; try contradiction; destruct H4.
    pose proof (Ptrofs.unsigned_range ofs0); rep_lia. }
  freeze [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39] FA.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx _))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp HRM._t'71 (Vint (if Z.leb 4 (Zlength (obj_bytes o)) then hrx5_tw (obj_bytes o)
      else Int.zero)) :: Q) (SEPx [FRZL FA; img_rep img (obj_bytes o)])))
  end.
  - rewrite !Int64.unsigned_repr in H5 by rep_lia.
    unfold img_rep. rewrite (hrx5_B4_A_img_split Ews (obj_bytes o) img) by (auto; lia). Intros.
    forward_call (Ews, img, sublist 0 4 (obj_bytes o)).
    { rewrite Zlength_sublist by lia; reflexivity. }
    forward.
    rewrite (proj2 (Z.leb_le 4 _)) by lia.
    gather_SEP (hbytes Ews (sublist 0 4 _) _) (hbytes Ews (sublist 4 _ _) _).
    rewrite <- (hrx5_B4_A_img_split Ews (obj_bytes o) img) by (auto; lia).
    entailer!. unfold img_rep. cancel.
  - forward.
    rewrite !Int64.unsigned_repr in H5 by rep_lia.
    rewrite (proj2 (Z.leb_gt 4 _)) by lia.
    entailer!.
  - idtac.
  forward.
  set (n := Zlength (obj_bytes o)) in *.
  set (tw0 := if 4 <=? n then hrx5_tw (obj_bytes o) else Int.zero).
  set (b1 := andb (Int.eq tw0 Int.one) (n =? 148)).
  set (b2 := andb (Int.eq tw0 (Int.repr 2)) (n =? 92)).
  set (b3 := andb (Int.eq tw0 (Int.repr 3)) (n =? 64)).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp HRM._t'73 (Vint (if b1 then Int.one else Int.zero)) :: Q) (SEPx SS)))
  end.
  { forward. entailer!. unfold b1. rewrite H5. change (Int.eq (Int.repr 1) Int.one) with true. cbn [andb Int64.cmpu].
    rewrite hrx5_B4_A_eq64 by rep_lia. destruct (n =? 148); reflexivity. }
  { forward. entailer!. unfold b1. rewrite Int.eq_false by auto. reflexivity. }
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp HRM._t'74 (Vint (if orb b1 b2 then Int.one else Int.zero)) :: Q) (SEPx SS)))
  end.
  { forward. entailer!. destruct b1; [reflexivity | contradiction H5; reflexivity]. }
  { forward_if.
    { forward. forward. entailer!.
      unfold b2. rewrite H6. change (Int.eq (Int.repr 2) (Int.repr 2)) with true. cbn [andb Int64.cmpu].
      rewrite hrx5_B4_A_eq64 by rep_lia. clearbody b1. destruct b1; [discriminate H5 |]. cbn [orb].
      destruct (n =? 92); reflexivity. }
    { forward. entailer!. unfold b2. rewrite Int.eq_false by auto. clearbody b1. destruct b1; [discriminate H5 |].
      reflexivity. } }
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp HRM._t'75 (Vint (if orb (orb b1 b2) b3 then Int.one else Int.zero)) :: Q) (SEPx SS)))
  end.
  { forward. entailer!. destruct (orb b1 b2); [reflexivity | contradiction H5; reflexivity]. }
  { forward_if.
    { forward. forward. entailer!.
      unfold b3. rewrite H6. change (Int.eq (Int.repr 3) (Int.repr 3)) with true. cbn [andb Int64.cmpu].
      rewrite hrx5_B4_A_eq64 by rep_lia. destruct (orb b1 b2); [discriminate H5 |]. cbn [orb].
      destruct (n =? 64); reflexivity. }
    { forward. entailer!. unfold b3. rewrite Int.eq_false by auto. destruct (orb b1 b2); [discriminate H5 |].
      reflexivity. } }
  forward.
  thaw FA.
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS) as Hptr by (sep_apply (hrx5_B4_A_ptrs PS); entailer!).
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  assert_PROP (isptr (l_wd L)) as Hwd by entailer!.
  pose proof H0 as (_ & Hwf & _ & _ & Hnp & _ & _).
  assert_PROP (is_pointer_or_null (hrx5_head NS)) as Hpn by (sep_apply (hrx5_B4_A_pn (hrx5_head NS) NS); entailer!).
  forward.
  forward_call (hrx5_head NS, NS, PS, Tsh, l_itd L, T).
  { apply (hrx5_B4_A_snap_pre x25519 R L NS PS KE T head nk H0 HwfT Hptr Hwd). }
  forward_call (hrx5_khead KE, KE, Tsh, l_itd L, T).
  { first [apply (hrx5_B4_A_ksnap_pre x25519 R L NS PS KE T head nk H0 HwfT Hptr) | split; [auto | apply (hrx5_B4_A_ksnap_pre x25519 R L NS PS KE T head nk H0 HwfT Hptr)]]. }
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_B4_S3b x25519 gv L FR) end.
  unfold hrx5_B4_S3b, hrx5_B4_Q.
  Exists R sec birth S w NS. Exists PS T head nk KE st. Exists i kc lul q proto ip4. Exists ip6 port o dp img.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app].
  rewrite (hrx5_B4_A_fwd (obj_bytes o)). cbv zeta.
  unfold b1, b2, b3, tw0, n in *.
  rewrite (hrx5_B4_A_head T NS PS Hnp), hrx5_B4_A_khead.
  entailer!.
Qed.
