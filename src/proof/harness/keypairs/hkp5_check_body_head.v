(* law keypairs: the segment HEAD (five checks).
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

(* ---------------------------------------------------------------------- *)
(* Pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hkc5h_bytes_eqb_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hkc5h_veqb_refl (v: val) : veqb v v = true.
Proof. unfold veqb. destruct (eq_dec v v); congruence. Qed.

Lemma hkc5h_entry_eqb_refl (E: entry) : entry_eqb E E = true.
Proof.
  unfold entry_eqb. destruct (eq_dec (e_peer E) (e_peer E)); [|congruence].
  rewrite !Int.eq_true. reflexivity.
Qed.

Lemma hkc5h_hs_eqb_refl (H: handshake) : hs_eqb H H = true.
Proof.
  unfold hs_eqb. destruct (eq_dec (hs_sid H) (hs_sid H)); [|congruence].
  rewrite !Int.eq_true, !Int64.eq_true, !hkc5h_bytes_eqb_refl. reflexivity.
Qed.

Lemma hkc5h_dev_eqb_refl D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hkc5h_veqb_refl, !hkc5h_bytes_eqb_refl, !Int64.eq_true, !Bool.eqb_reflx.
  reflexivity.
Qed.

(* P's pool entry *)
Lemma hkc5h_pool F V Y : hkp5_inv F V Y ->
  In (hs_addr (f_p F)) (saddrs (t_D (y_T Y))) /\
  exists idx, sfind (t_D (y_T Y)) (hs_addr (f_p F)) = Some (Tsh, mkEntry (f_p F) IDX_HANDSHAKE idx).
Proof.
  intros (Hrel & _).
  destruct Hrel as (Hcore & _).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & Hpool).
  destruct Hpool as (Hin & _ & _ & _ & Hs & _).
  split; [apply (proj2 (Hin _)); left; reflexivity | exact Hs].
Qed.

(* hs_same_but_next(&hsm, &p->handshake) *)
Lemma hkc5h_hsm F V Y : hkp5_inv F V Y ->
  snap_eqb_nn (y_hsn Y) (hs_snap_cur (y_T Y) (f_p F) (y_P Y)) = true.
Proof.
  intros Hinv.
  destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (He & Hh & Hs) & _).
  unfold snap_eqb_nn, hs_snap_cur, snap_of, t_entry_d. rewrite He. cbn [sn_entry sn_hashed sn_hs].
  rewrite Hh, Hs, hkc5h_entry_eqb_refl, Bool.eqb_reflx, hkc5h_hs_eqb_refl. reflexivity.
Qed.

Lemma hkc5h_hs_ptrs F V Y D : hkp5_inv F V Y ->
  Forall (vp_ok (hs_own (f_p F) (y_T Y) [VDev Tsh (f_w F) D]))
    (hs_ptrs_nn (y_hsn Y) (hs_snap_cur (y_T Y) (f_p F) (y_P Y))).
Proof.
  intros Hinv.
  destruct (hkc5h_pool F V Y Hinv) as (_ & idx & Hsf).
  destruct Hinv as (_ & _ & _ & Hsid & _ & _ & _ & _ & _ & (He & Hh & Hs) & _).
  unfold hs_ptrs_nn, hs_snap_cur, snap_of, t_entry_d. rewrite He. cbn [sn_entry sn_hashed sn_hs].
  unfold t_entry in He. rewrite Hsf in He. injection He as He. rewrite <- He. cbn [e_peer].
  rewrite Hs, Hsid.
  assert (Hp: vp_ok (hs_own (f_p F) (y_T Y) [VDev Tsh (f_w F) D]) (f_p F)) by (right; left; reflexivity).
  assert (Hi: vp_ok (hs_own (f_p F) (y_T Y) [VDev Tsh (f_w F) D]) (id_addr (f_w F))).
  { right. right. apply in_or_app. right. cbn. auto. }
  repeat (apply Forall_cons; [assumption|]); apply Forall_nil.
Qed.

(* dev_same(&dsm, w) *)
Lemma hkc5h_dev_ptrs x25519 F V Y O : hkp5_oth_ok F V O ->
  Forall (vp_ok ([f_w F; d_ptab (hkp5_D x25519 F V)] ++
                 vobjs_addrs [VItab Tsh (f_t F) (y_T Y); VPeer Tsh (f_p F) (y_P Y); VPeers (o_PS O)]))
    (dev_ptrs (hkp5_D x25519 F V) (v_head V) (hkp5_D x25519 F V) (v_head V)).
Proof.
  intros Hok. destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
  set (L := [f_w F; d_ptab (hkp5_D x25519 F V)] ++
            vobjs_addrs [VItab Tsh (f_t F) (y_T Y); VPeer Tsh (f_p F) (y_P Y); VPeers (o_PS O)]).
  assert (EL: L = [f_w F; f_pt F] ++ (f_t F :: saddrs (t_D (y_T Y))) ++ [f_p F] ++ map peer_addr4 (o_PS O) ++ [])
    by reflexivity.
  assert (Hn: vp_ok L nullval) by (left; reflexivity).
  assert (Hw: vp_ok L (f_w F)) by (right; rewrite EL; left; reflexivity).
  assert (Hpt: vp_ok L (f_pt F)) by (right; rewrite EL; right; left; reflexivity).
  assert (Ht: vp_ok L (f_t F)) by (right; rewrite EL; right; right; left; reflexivity).
  assert (Hv: vp_ok L (v_head V)).
  { rewrite EL. right. rewrite !in_app_iff.
    destruct Hh as [-> | Hh]; [do 2 right; left; left; reflexivity | do 3 right; left; exact Hh]. }
  unfold dev_ptrs, hkp5_D, setup_dev. cbn [d_dev d_cc cc_dev d_ptab d_itab].
  repeat (apply Forall_cons; [assumption|]); apply Forall_nil.
Qed.

Lemma hkc5h_vok_peers PS : peers_wf PS -> vobj_ok (VPeers PS).
Proof.
  intros H. cbn. eapply Forall_impl; [| exact H]. intros [[a sh] P] Hw. apply writable_readable, Hw.
Qed.

(* ---------------------------------------------------------------------- *)
(* Accessors (ported from handshake_clear's hcl5_p7_chk_lem.v)             *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hkc5h_cceN : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Definition hkc5h_acc (Q P: mpred) : Prop := (P |-- Q * (Q -* P))%logic.

Lemma hkc5h_mp (Q P: mpred) : (Q * (Q -* P) |-- P)%logic.
Proof. apply wand_frame_elim. Qed.

Lemma hkc5h_acc_refl Q : hkc5h_acc Q Q.
Proof.
  unfold hkc5h_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon.
  apply derives_refl.
Qed.

Lemma hkc5h_acc_eq Q A : Q = A -> hkc5h_acc Q A.
Proof. intros ->. apply hkc5h_acc_refl. Qed.

Lemma hkc5h_acc_l Q A F : hkc5h_acc Q A -> hkc5h_acc Q (A * F)%logic.
Proof.
  unfold hkc5h_acc. intros H. apply derives_trans with (Q * (Q -* A) * F)%logic.
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)%logic), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)%logic),
    (sepcon_comm (Q -* A)%logic Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hkc5h_acc_r Q A F : hkc5h_acc Q A -> hkc5h_acc Q (F * A)%logic.
Proof. intros H. rewrite sepcon_comm. apply hkc5h_acc_l, H. Qed.

Lemma hkc5h_acc_prop Q (c: Prop) A : (c -> hkc5h_acc Q A) -> hkc5h_acc Q (!! c && A)%logic.
Proof.
  unfold hkc5h_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm.
  apply modus_ponens_wand.
Qed.

(* P's reference count at W_keypairs *)
Lemma hkc5h_peer_refs sh p P :
  hkc5h_acc (field_at sh (Tstruct KC._wg_peer noattr) [StructField KC._refcount] (Vint (p_refs P)) p)
    (peer_rep sh p P).
Proof.
  unfold peer_rep. apply hkc5h_acc_prop; intros _.
  do 4 apply hkc5h_acc_l. apply hkc5h_acc_r. apply hkc5h_acc_eq.
  rewrite (@field_at_change_composite Noise.CS W_keypairs _ sh t_peer [StructField I._refcount]
    (Vint (p_refs P)) (Vint (p_refs P)) (JMeq_refl _)) by prove_cs_preserve_type.
  reflexivity.
Qed.

Lemma hkc5h_vo1 sh wg D : vobjs W_keypairs [VDev sh wg D] = device_rep sh wg D.
Proof. unfold vobjs. cbn. apply sepcon_emp. Qed.

Lemma hkc5h_vo3 sh t T p P PS :
  vobjs W_keypairs [VItab sh t T; VPeer sh p P; VPeers PS] =
  (itable sh t T * peer_rep sh p P * peers_rep PS)%logic.
Proof. unfold vobjs. cbn. rewrite sepcon_emp, sepcon_assoc. reflexivity. Qed.

(* the SEP items are in the compspecs of the specs that consume them: no conversion *)
Local Ltac change_compspecs cs ::= idtac.

Ltac hkc5h_false :=
  exfalso;
  first [ match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end
        | match goal with Hc: Int.zero <> Int.zero |- _ => apply Hc; reflexivity end
        | match goal with Hc: Int.one <> Int.one |- _ => apply Hc; reflexivity end
        | match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end ].

Lemma hkc5_head_ok : hkc5_head_stmt.
Proof.
  intros Espec x25519 F V Y O R.
  unfold hkc5_S. destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hkc5_head, hkc5_Delta, hkc5_G.
  abbreviate_semax.
  Intros.
  rename H into Hfix, H0 into Hinv, H1 into Hok.
  pose proof (hkc5h_hsm F V Y Hinv) as Ehsm.
  pose proof (hkc5h_hs_ptrs F V Y (hkp5_D x25519 F V) Hinv) as Phs.
  pose proof (hkc5h_pool F V Y Hinv) as (Hin & _).
  pose proof (hkc5h_dev_ptrs x25519 F V Y O Hok) as Pdev.
  pose proof Hinv as (_ & Hwarn & Hdev & _ & Hrefs & _ & _ & _ & _ & _ & Hpkn).
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_othR, hkp5_oth_rep, hkc5_lv.
  cbn [app fold_right_sepcon].
  unfold shim_state4.
  repeat flatten_sepcon_in_SEP.
  freeze [4;5;6;7;8;9;10;11;12;13;14;15;16;22;24;25;26;27;28;30;31;33] FR.
  assert_PROP (@field_compatible Noise.CS t_peer [] (f_p F)) as Hfcp by (unfold peer_rep; Intros; entailer!).
  assert (Pp: isptr (f_p F)) by (destruct Hfcp; auto).
  (* 1: hs_same_but_next(&hsm, &p->handshake) *)
  replace (peer_rep Tsh (f_p F) (y_P Y)) with (hs_mem true Tsh (f_p F) (y_P Y)) by reflexivity.
  rewrite <- hkc5h_vo1.
  forward_call (Ews, f_gv F KC._hsm, y_hsn Y, Tsh, f_p F, y_P Y, true, Tsh, f_t F, y_T Y,
                [VDev Tsh (f_w F) (hkp5_D x25519 F V)]).
  { repeat constructor. cbn. apply readable_share_top. }
  rewrite Ehsm.
  replace (hs_mem true Tsh (f_p F) (y_P Y)) with (peer_rep Tsh (f_p F) (y_P Y)) by reflexivity.
  rewrite hkc5h_vo1.
  forward_if (temp KC._t'2 (Vint Int.zero)).
  { hkc5h_false. }
  { (* 2: rest_same(&prm, p) *)
    forward_call (Ews, f_gv F KC._prm, Tsh, f_p F, y_P Y, Tsh, f_w F, hkp5_D x25519 F V).
    forward.
    entailer!. }
  forward_if (temp KC._t'4 (Vint Int.zero)).
  { hkc5h_false. }
  { (* 3: p->refcount.refcount != prefs *)
    pose proof (hkc5h_peer_refs Tsh (f_p F) (y_P Y)) as A; unfold hkc5h_acc in A; sep_apply A; clear A.
    Intros.
    forward.
    sep_apply (hkc5h_mp (field_at Tsh (Tstruct KC._wg_peer noattr) [StructField KC._refcount]
                           (Vint (p_refs (y_P Y))) (f_p F))).
    forward.
    forward.
    entailer!.
    rewrite Hrefs, Int.eq_true. reflexivity. }
  gather_SEP (itable _ _ _) (peer_rep _ _ _) (peers_rep _).
  rewrite <- hkc5h_vo3.
  change (ptable Tsh (f_pt F) (v_head V)) with (ptable Tsh (d_ptab (hkp5_D x25519 F V)) (v_head V)).
  forward_if (temp KC._t'5 (Vint Int.zero)).
  { hkc5h_false. }
  { (* 4: dev_same(&dsm, w) *)
    forward_call (Ews, f_gv F KC._dsm, hkp5_D x25519 F V, v_head V, Tsh, f_w F, hkp5_D x25519 F V, Tsh,
                  v_head V, [VItab Tsh (f_t F) (y_T Y); VPeer Tsh (f_p F) (y_P Y); VPeers (o_PS O)]).
    { destruct Hok as (_ & Hwf & _).
      repeat apply Forall_cons; try apply Forall_nil; cbn; try apply readable_share_top.
      apply hkc5h_vok_peers, Hwf. }
    rewrite hkc5h_dev_eqb_refl.
    forward.
    entailer!. }
  forward_if (temp KC._t'7 (Vint Int.zero)).
  { hkc5h_false. }
  { (* 5: warn_same() *)
    forward_call (f_gv F, v_w0 V, h5_warn (y_H Y), y_w Y).
    forward.
    entailer!. }
  forward_if.
  { hkc5h_false. }
  rewrite hkc5h_vo3. thaw FR.
  change (ptable Tsh (d_ptab (hkp5_D x25519 F V)) (v_head V)) with (ptable Tsh (f_pt F) (v_head V)).
  forward.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_othR, hkp5_oth_rep, hkc5_lv.
  cbn [app fold_right_sepcon].
  unfold shim_state4.
  entailer!.
Qed.
