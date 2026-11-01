(* law handshake_receive, phase B8 branch I, segment I2: opening
   QI's SEP list into the sixteen fields the CHECK of I2 reads (the pool entry of the handshake, the peer's five
   handshake fields, the node snapshot's ten fields) and a wand back to it; valid pointers and pure facts of single
   SEP items.  Port of consume_initiation_any's hci5_p8_A3_s11_open.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope Z_scope.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The fields the CHECK reads (the block lemmas' state without its frame)  *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8I_I2_Ce (hv pe nxt: val) (hb: bool) (ty ix: int) : list mpred :=
  [@field_at W Ews t_hs (DOT HM._entry) (pe, (nxt, (Val.of_bool hb, (Vint ty, Vint ix)))) hv].
Definition hrx5_B8I_I2_Cp (hv sid: val) (eph rs ss psk: list byte) : list mpred :=
  [@field_at W Ews t_hs (DOT HM._static_identity) sid hv;
   hbytes Ews eph (@field_address W t_hs (DOT HM._ephemeral_private) hv);
   hbytes Ews rs (@field_address W t_hs (DOT HM._remote_static) hv);
   hbytes Ews ss (@field_address W t_hs (DOT HM._precomputed_static_static) hv);
   hbytes Ews psk (@field_address W t_hs (DOT HM._preshared_key) hv)].
Definition hrx5_B8I_I2_Cs (sv pe nxt: val) (hb: bool) (ty ix: int) (sid: val) (eph rs ss psk: list byte)
  : list mpred :=
  [@field_at W Ews t_hsnap (DOT HM._peer) pe sv;
   @field_at W Ews t_hsnap (DOT HM._next) nxt sv;
   @field_at W Ews t_hsnap (DOT HM._hashed) (Val.of_bool hb) sv;
   @field_at W Ews t_hsnap (DOT HM._type) (Vint ty) sv;
   @field_at W Ews t_hsnap (DOT HM._index) (Vint ix) sv;
   @field_at W Ews t_hsnap (DOT HM._static_identity) sid sv;
   hbytes Ews eph (@field_address W t_hsnap (DOT HM._ephemeral_private) sv);
   hbytes Ews rs (@field_address W t_hsnap (DOT HM._remote_static) sv);
   hbytes Ews ss (@field_address W t_hsnap (DOT HM._precomputed_static_static) sv);
   hbytes Ews psk (@field_address W t_hsnap (DOT HM._preshared_key) sv)].
Definition hrx5_B8I_I2_C (hv sv pe nxt: val) (hb: bool) (ty ix: int) (sid: val) (eph rs ss psk: list byte)
  : list mpred :=
  hrx5_B8I_I2_Ce hv pe nxt hb ty ix ++ hrx5_B8I_I2_Cp hv sid eph rs ss psk ++
  hrx5_B8I_I2_Cs sv pe nxt hb ty ix sid eph rs ss psk.

(* ---------------------------------------------------------------------- *)
(* Generic                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_I2_dcs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.

Lemma hrx5_B8I_I2_hb sh n A p : Zlength A = n ->
  @data_at W sh (tarray tuchar n) (bytes A) p = hbytes sh A p.
Proof. intros <-. unfold hbytes. apply hrx5_B8I_I2_dcs. Qed.

(* opening a predicate X = core * rest, keeping a wand to put it back *)
Lemma hrx5_B8I_I2_wopen (X C R: mpred) (Pp: Prop) : X = !! Pp && (C * R) -> X |-- !! Pp && (C * (C -* X)).
Proof.
  intros HX. rewrite HX at 1. Intros. apply andp_right; [apply prop_right; auto |].
  apply sepcon_derives; [apply derives_refl |]. rewrite <- wand_sepcon_adjoint. rewrite HX.
  apply andp_right; [apply prop_right; auto |]. rewrite sepcon_comm. apply derives_refl.
Qed.

(* three abstract openings combined *)
Lemma hrx5_B8I_I2_comb (A B D Rst C1 C2 C3 Y: mpred) :
  (A |-- C1 * (C1 -* A)) -> (D |-- C3 * (C3 -* D)) -> (B |-- C2 * (C2 -* B)) ->
  (A * (B * (D * Rst)) |-- Y) ->
  A * (B * (D * Rst)) |-- (C1 * (C3 * C2)) * ((C1 * (C3 * C2)) -* Y).
Proof.
  intros HA HD HB HY.
  sep_apply HA. sep_apply HD. sep_apply HB.
  cancel. rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  sep_apply (modus_ponens_wand C1 A). sep_apply (modus_ponens_wand C3 D). sep_apply (modus_ponens_wand C2 B).
  cancel.
Qed.

Lemma hrx5_B8I_I2_mp (Cl: list mpred) (Y: mpred) :
  fold_right_sepcon (Cl ++ [fold_right_sepcon Cl -* Y]) |-- Y.
Proof. rewrite fold_right_sepcon_app. cbn [fold_right_sepcon]. rewrite sepcon_emp. apply modus_ponens_wand. Qed.

(* valid pointers: from one item of a SEP list *)
Lemma hrx5_B8I_I2_in_vp (Rl: list mpred) (A: mpred) (x: val) :
  In A Rl -> (A * TT |-- valid_pointer x) -> fold_right_sepcon Rl |-- valid_pointer x.
Proof.
  intros HIn HA. apply in_split in HIn. destruct HIn as (l1 & l2 & ->).
  rewrite fold_right_sepcon_app. simpl. eapply derives_trans; [| exact HA].
  rewrite <- sepcon_assoc, (sepcon_comm (fold_right_sepcon l1) A), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* pure facts of single SEP items *)
Lemma hrx5_B8I_I2_sep_prop (Q: list localdef) (Rl: list mpred) (A: mpred) (Pp: Prop) :
  In A Rl -> (A |-- !! Pp) -> PROPx [] (LOCALx Q (SEPx Rl)) |-- !! Pp.
Proof.
  intros HIn HA.
  assert (H1: fold_right_sepcon Rl |-- !! Pp).
  { apply in_split in HIn. destruct HIn as (l1 & l2 & ->). rewrite fold_right_sepcon_app. simpl.
    sep_apply HA. entailer!. }
  intros rho. unfold PROPx, LOCALx, SEPx. simpl. apply andp_left2. apply andp_left2. exact H1.
Qed.

Lemma hrx5_B8I_I2_prop_intro (Ps: list Prop) (Q: list localdef) (Rl: list mpred) :
  fold_right and True Ps -> PROPx [] (LOCALx Q (SEPx Rl)) |-- PROPx Ps (LOCALx Q (SEPx Rl)).
Proof.
  intros HP rho. unfold PROPx. simpl. apply andp_derives; [| apply derives_refl].
  apply prop_derives. intros _. exact HP.
Qed.

(* ---------------------------------------------------------------------- *)
(* The node: its snapshot's fields                                         *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_I2_snap_split shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
  @data_at W shs t_hsnap
    (a, (b, (c, (d, (e, (f, (g, (h, (l1, (l2, (l3, (l4, (l5, (l6, (l7, (l8, ri)))))))))))))))) s =
  field_at shs t_hsnap (DOT HM._peer) a s * field_at shs t_hsnap (DOT HM._next) b s *
  field_at shs t_hsnap (DOT HM._hashed) c s * spacer shs 17 20 s *
  field_at shs t_hsnap (DOT HM._type) d s * field_at shs t_hsnap (DOT HM._index) e s *
  field_at shs t_hsnap (DOT HM._state) f s * field_at shs t_hsnap (DOT HM._last_initiation_consumption) g s *
  field_at shs t_hsnap (DOT HM._static_identity) h s *
  data_at shs (tarray tuchar 32) l1 (field_address t_hsnap (DOT HM._ephemeral_private) s) *
  data_at shs (tarray tuchar 32) l2 (field_address t_hsnap (DOT HM._remote_static) s) *
  data_at shs (tarray tuchar 32) l3 (field_address t_hsnap (DOT HM._remote_ephemeral) s) *
  data_at shs (tarray tuchar 32) l4 (field_address t_hsnap (DOT HM._precomputed_static_static) s) *
  data_at shs (tarray tuchar 32) l5 (field_address t_hsnap (DOT HM._preshared_key) s) *
  data_at shs (tarray tuchar 32) l6 (field_address t_hsnap (DOT HM._hash) s) *
  data_at shs (tarray tuchar 32) l7 (field_address t_hsnap (DOT HM._chaining_key) s) *
  data_at shs (tarray tuchar 12) l8 (field_address t_hsnap (DOT HM._latest_timestamp) s) *
  field_at shs t_hsnap (DOT HM._remote_index) ri s.
Proof.
  match goal with |- @data_at _ _ _ ?v _ = _ => set (V := v) end.
  unfold data_at.
  rewrite (@field_at_Tstruct W shs t_hsnap [] HH._hs_snap noattr V V s eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at shs t_hsnap (DOT HM._ephemeral_private)),
    (field_at_data_at shs t_hsnap (DOT HM._remote_static)),
    (field_at_data_at shs t_hsnap (DOT HM._remote_ephemeral)),
    (field_at_data_at shs t_hsnap (DOT HM._precomputed_static_static)),
    (field_at_data_at shs t_hsnap (DOT HM._preshared_key)),
    (field_at_data_at shs t_hsnap (DOT HM._hash)),
    (field_at_data_at shs t_hsnap (DOT HM._chaining_key)),
    (field_at_data_at shs t_hsnap (DOT HM._latest_timestamp)).
  simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

(* the rest of the snapshot, besides the ten fields the CHECK reads *)
Definition hrx5_B8I_I2_srest (s: val) (H: handshake) : mpred :=
  spacer Ews 17 20 s *
  field_at Ews t_hsnap (DOT HM._state) (Vint (hs_state H)) s *
  field_at Ews t_hsnap (DOT HM._last_initiation_consumption) (Vlong (hs_lic H)) s *
  data_at Ews (tarray tuchar 32) (bytes (hs_reph H)) (field_address t_hsnap (DOT HM._remote_ephemeral) s) *
  data_at Ews (tarray tuchar 32) (bytes (hs_hash H)) (field_address t_hsnap (DOT HM._hash) s) *
  data_at Ews (tarray tuchar 32) (bytes (hs_ck H)) (field_address t_hsnap (DOT HM._chaining_key) s) *
  data_at Ews (tarray tuchar 12) (bytes (hs_ts H)) (field_address t_hsnap (DOT HM._latest_timestamp) s) *
  field_at Ews t_hsnap (DOT HM._remote_index) (Vint (hs_rindex H)) s.

Lemma hrx5_B8I_I2_hsnap_eq sn :
  hsnap_val sn =
  (e_peer (sn_entry sn), (sn_next sn, (Val.of_bool (sn_hashed sn), (Vint (e_type (sn_entry sn)),
  (Vint (e_index (sn_entry sn)),
  (Vint (hs_state (sn_hs sn)), (Vlong (hs_lic (sn_hs sn)), (hs_sid (sn_hs sn), (bytes (hs_eph (sn_hs sn)),
  (bytes (hs_rstatic (sn_hs sn)), (bytes (hs_reph (sn_hs sn)), (bytes (hs_ss (sn_hs sn)),
  (bytes (hs_psk (sn_hs sn)), (bytes (hs_hash (sn_hs sn)), (bytes (hs_ck (sn_hs sn)), (bytes (hs_ts (sn_hs sn)),
  Vint (hs_rindex (sn_hs sn)))))))))))))))))).
Proof. reflexivity. Qed.

Lemma hrx5_B8I_I2_snap_eq s sn : hs_ok (sn_hs sn) ->
  @data_at W Ews t_hsnap (hsnap_val sn) s =
  !! (@field_compatible W t_hsnap [] s) &&
  (fold_right_sepcon (hrx5_B8I_I2_Cs s (e_peer (sn_entry sn)) (sn_next sn) (sn_hashed sn) (e_type (sn_entry sn))
     (e_index (sn_entry sn)) (hs_sid (sn_hs sn)) (hs_eph (sn_hs sn)) (hs_rstatic (sn_hs sn)) (hs_ss (sn_hs sn))
     (hs_psk (sn_hs sn))) *
   hrx5_B8I_I2_srest s (sn_hs sn)).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  rewrite hrx5_B8I_I2_hsnap_eq, hrx5_B8I_I2_snap_split. unfold hrx5_B8I_I2_Cs, hrx5_B8I_I2_srest.
  cbn [fold_right_sepcon].
  rewrite (hrx5_B8I_I2_hb Ews 32 (hs_eph (sn_hs sn))), (hrx5_B8I_I2_hb Ews 32 (hs_rstatic (sn_hs sn))),
    (hrx5_B8I_I2_hb Ews 32 (hs_ss (sn_hs sn))), (hrx5_B8I_I2_hb Ews 32 (hs_psk (sn_hs sn))) by auto.
  apply pred_ext.
  - assert_PROP (@field_compatible W t_hsnap (DOT HM._peer) s) as Hf by entailer!.
    apply andp_right; [apply prop_right; destruct Hf as (A1 & A2 & A3 & A4 & _); repeat split; auto | cancel].
  - Intros. cancel.
Qed.

(* the snapshot's fields from the node list, the rest in the wand *)
Lemma hrx5_B8I_I2_acc_node l NSx N sn : In N NSx -> hn_snap N = hsnap_val sn -> hs_ok (sn_hs sn) ->
  hrx5_B8I_acc
    (fold_right_sepcon (hrx5_B8I_I2_Cs (offset_val 8 (hn_addr N)) (e_peer (sn_entry sn)) (sn_next sn)
       (sn_hashed sn) (e_type (sn_entry sn)) (e_index (sn_entry sn)) (hs_sid (sn_hs sn)) (hs_eph (sn_hs sn))
       (hs_rstatic (sn_hs sn)) (hs_ss (sn_hs sn)) (hs_psk (sn_hs sn))))
    (hnodes_rep4 W l NSx).
Proof.
  intros Hin Hs Hok. apply (hrx5_B8I_nodes_acc _ N NSx l Hin). intros nx.
  eapply hrx5_B8I_acc_trans; [| apply hrx5_B8I_nfld_snap].
  apply hrx5_B8I_acc_pure with (c := @field_compatible CKS t_hnode4 [] (hn_addr N)).
  { eapply derives_trans; [apply field_at_local_facts |]. apply prop_derives.
    intros ((A1 & A2 & A3 & A4 & _) & _); repeat split; auto. }
  intros FC. rewrite (hrx5_B8I_snap_at _ _ FC), Hs, (hrx5_B8I_I2_snap_eq _ sn Hok).
  apply hrx5_B8I_acc_prop; intros _. apply hrx5_B8I_acc_l, hrx5_B8I_acc_refl.
Qed.

Lemma hrx5_B8I_I2_fcs_prop l NSx N : In N NSx ->
  hnodes_rep4 W l NSx |-- !! @field_compatible W t_hsnap [] (offset_val 8 (hn_addr N)).
Proof.
  intros Hin.
  eapply derives_trans; [apply (hrx5_B8I_nodes_acc _ N NSx l Hin (fun nx => hrx5_B8I_nfld_snap N nx)) |].
  assert_PROP (@field_compatible CKS t_hnode4 [StructField HM._snap] (hn_addr N)) as FC1 by entailer!.
  assert (FC: @field_compatible CKS t_hnode4 [] (hn_addr N))
    by (destruct FC1 as (A1 & A2 & A3 & A4 & _); repeat split; auto).
  rewrite (hrx5_B8I_snap_at _ _ FC). entailer!.
Qed.

Lemma hrx5_B8I_I2_cnodeY l NSx T a P N (Y: mpred) :
  In N NSx -> hn_snap N = hsnap_val (hs_snap_cur T a P) -> hs_ok (p_hs P) ->
  (hnodes_rep4 W l NSx |-- Y) ->
  hnodes_rep4 W l NSx |--
  fold_right_sepcon (hrx5_B8I_I2_Cs (offset_val 8 (hn_addr N)) (e_peer (t_entry_d T (hs_addr a)))
    (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a)))
    (e_index (t_entry_d T (hs_addr a))) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P))
    (hs_psk (p_hs P))) *
  (fold_right_sepcon (hrx5_B8I_I2_Cs (offset_val 8 (hn_addr N)) (e_peer (t_entry_d T (hs_addr a)))
    (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a)))
    (e_index (t_entry_d T (hs_addr a))) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P))
    (hs_psk (p_hs P))) -* Y).
Proof.
  intros Hin Hs Hok HY.
  pose proof (hrx5_B8I_I2_acc_node l NSx N (hs_snap_cur T a P) Hin Hs Hok) as HA.
  unfold hrx5_B8I_acc in HA. cbn [hs_snap_cur snap_of sn_entry sn_next sn_hashed sn_hs] in HA.
  sep_apply HA. cancel.
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

(* ---------------------------------------------------------------------- *)
(* The accepted peer: the five handshake fields the CHECK reads, the rest  *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8I_I2_prest (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  @field_at Noise.CS Ews t_peer [StructField I._device] (p_device P) p *
  @field_at Noise.CS Ews t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  kps_rep Ews (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  @field_at Noise.CS Ews t_hs [StructField I._state] (Vint (hs_state H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
  (EX lk: val, @field_at Noise.CS Ews t_hs [StructField I._lock] lk h) *
  spacer Ews 36 40 h * spacer Ews 300 304 h *
  @field_at Noise.CS Ews t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep Ews (cookie_addr p) (p_cookie P) *
  @field_at Noise.CS Ews t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  @field_at Noise.CS Ews t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  @field_at Noise.CS Ews t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer Ews 9 16 p * spacer Ews 476 480 p.

Ltac hrx5_B8I_I2_hsf_tac :=
  intros Hl; match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W _ sh t gfs v v (JMeq_refl v)) by reflexivity end;
  rewrite field_at_data_at; rewrite <- (hrx5_B8I_I2_hb _ _ _ _ Hl); reflexivity.

Lemma hrx5_B8I_I2_f_eph sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._ephemeral_private) (bytes A) h =
  hbytes sh A (@field_address W t_hs (DOT HM._ephemeral_private) h).
Proof. hrx5_B8I_I2_hsf_tac. Qed.
Lemma hrx5_B8I_I2_f_rs sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._remote_static) (bytes A) h =
  hbytes sh A (@field_address W t_hs (DOT HM._remote_static) h).
Proof. hrx5_B8I_I2_hsf_tac. Qed.
Lemma hrx5_B8I_I2_f_ss sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._precomputed_static_static) (bytes A) h =
  hbytes sh A (@field_address W t_hs (DOT HM._precomputed_static_static) h).
Proof. hrx5_B8I_I2_hsf_tac. Qed.
Lemma hrx5_B8I_I2_f_psk sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._preshared_key) (bytes A) h =
  hbytes sh A (@field_address W t_hs (DOT HM._preshared_key) h).
Proof. hrx5_B8I_I2_hsf_tac. Qed.
Lemma hrx5_B8I_I2_f_sid sh v h :
  @field_at Noise.CS sh t_hs (DOT I._static_identity) v h =
  @field_at W sh t_hs (DOT HM._static_identity) v h.
Proof.
  rewrite (@field_at_change_composite Noise.CS W _ sh t_hs _ v v (JMeq_refl v)) by reflexivity.
  reflexivity.
Qed.

Lemma hrx5_B8I_I2_peer_eq p P :
  peer_rep Ews p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  (fold_right_sepcon (hrx5_B8I_I2_Cp (hs_addr p) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P))
     (hs_ss (p_hs P)) (hs_psk (p_hs P))) * hrx5_B8I_I2_prest p P).
Proof.
  unfold peer_rep, hs_rep, hrx5_B8I_I2_Cp, hrx5_B8I_I2_prest. cbn [fold_right_sepcon].
  apply pred_ext.
  - Intros. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hrx5_B8I_I2_f_eph Ews _ _ L1), (hrx5_B8I_I2_f_rs Ews _ _ L2), (hrx5_B8I_I2_f_ss Ews _ _ L4),
      (hrx5_B8I_I2_f_psk Ews _ _ L5), hrx5_B8I_I2_f_sid.
    Intros lk. entailer!. Exists lk. cancel.
  - Intros. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hrx5_B8I_I2_f_eph Ews _ _ L1), (hrx5_B8I_I2_f_rs Ews _ _ L2), (hrx5_B8I_I2_f_ss Ews _ _ L4),
      (hrx5_B8I_I2_f_psk Ews _ _ L5), hrx5_B8I_I2_f_sid.
    Intros lk. entailer!. Exists lk. cancel.
Qed.

Lemma hrx5_B8I_I2_peer_putF a P M now t ck2 h2 :
  peer_rep Ews a (hrx5_B8I_put P M now t ck2 h2) =
  !! (@field_compatible Noise.CS t_peer [] a /\ hs_ok (p_hs (hrx5_B8I_put P M now t ck2 h2))) &&
  (fold_right_sepcon (hrx5_B8I_I2_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P))
     (hs_ss (p_hs P)) (hs_psk (p_hs P))) * hrx5_B8I_I2_prest a (hrx5_B8I_put P M now t ck2 h2)).
Proof. rewrite hrx5_B8I_I2_peer_eq. reflexivity. Qed.

Lemma hrx5_B8I_I2_cpeerY PS a P M now t ck2 h2 (Y: mpred) : sfind PS a = Some (Ews, P) ->
  (peers_rep (supd PS a (hrx5_B8I_put P M now t ck2 h2)) |-- Y) ->
  peers_rep (supd PS a (hrx5_B8I_put P M now t ck2 h2)) |--
  fold_right_sepcon (hrx5_B8I_I2_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P))
    (hs_ss (p_hs P)) (hs_psk (p_hs P))) *
  (fold_right_sepcon (hrx5_B8I_I2_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P))
    (hs_ss (p_hs P)) (hs_psk (p_hs P))) -* Y).
Proof.
  intros Hsf HY. rewrite (hrx5_B8I_peers PS a Ews P _ Hsf).
  sep_apply (hrx5_B8I_I2_wopen _ _ _ _ (hrx5_B8I_I2_peer_putF a P M now t ck2 h2)). Intros.
  cancel.
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  rewrite (hrx5_B8I_peers PS a Ews P _ Hsf).
  match goal with |- context [(?C -* peer_rep ?a1 ?a2 ?a3)] => sep_apply (modus_ponens_wand C (peer_rep a1 a2 a3)) end.
  cancel.
Qed.

Lemma hrx5_B8I_I2_vp_peers PS a P Q R : sfind PS a = Some (Ews, P) ->
  peers_rep (supd PS a Q) * R |-- valid_pointer a.
Proof.
  intros Hf. rewrite (hrx5_B8I_peers PS a Ews P Q Hf).
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply hrx5_B8I_vp_peer. apply readable_nonidentity. auto.
Qed.

Lemma hrx5_B8I_I2_fc_prop PS a P Q : sfind PS a = Some (Ews, P) ->
  peers_rep (supd PS a Q) |-- !! @field_compatible Noise.CS t_peer [] a.
Proof.
  intros Hf. rewrite (hrx5_B8I_peers PS a Ews P Q Hf). unfold peer_rep at 1. Intros.
  apply prop_right. auto.
Qed.

Lemma hrx5_B8I_I2_fch p :
  @field_compatible Noise.CS t_peer [] p -> @field_compatible W t_hs [] (hs_addr p).
Proof.
  intros FC0. assert (FC: @field_compatible W t_peer [] p)
    by (apply (@field_compatible_change_composite Noise.CS W _ t_peer); auto).
  assert (FC1: @field_compatible W t_peer (DOT I._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

(* ---------------------------------------------------------------------- *)
(* The pool entry of the handshake (links from the table T)                *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_I2_citableY tab T x (Y: mpred) :
  In x (saddrs (t_D T)) -> Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  @field_compatible Noise.CS t_hs [] x ->
  (itable Tsh tab T |-- Y) ->
  itable Tsh tab T |--
  fold_right_sepcon (hrx5_B8I_I2_Ce x (e_peer (t_entry_d T x)) (succ_in (t_L T) x) (vin x (t_L T))
    (e_type (t_entry_d T x)) (e_index (t_entry_d T x))) *
  (fold_right_sepcon (hrx5_B8I_I2_Ce x (e_peer (t_entry_d T x)) (succ_in (t_L T) x) (vin x (t_L T))
    (e_type (t_entry_d T x)) (e_index (t_entry_d T x))) -* Y).
Proof.
  intros Hin Hsh Hfc HY. unfold hrx5_B8I_I2_Ce. cbn [fold_right_sepcon]. rewrite sepcon_emp.
  sep_apply (hrx5_B8I_entry tab T x Hin Hsh Hfc).
  cancel. rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8I_I2_itable_wf sht tab T : itable sht tab T |-- !! itable_wf T.
Proof. unfold itable. Intros. apply prop_right. auto. Qed.

Lemma hrx5_B8I_I2_succ_in : forall (L: list val) x, succ_in L x = nullval \/ In (succ_in L x) L.
Proof.
  induction L as [|y L IH]; intros x; simpl; [left; reflexivity |].
  destruct (EqDec_val y x); [destruct L; simpl; auto | destruct (IH x); auto].
Qed.

(* the list's members are valid pointers (pool entries) *)
Lemma hrx5_B8I_I2_itable_vp sht tab T y : In y (t_L T) -> itable sht tab T |-- valid_pointer y.
Proof.
  intros Hy. unfold itable. apply derives_extract_prop; intros Hwf. pose proof Hwf as (_ & Hincl & _ & Hws).
  destruct (hrx5_B8I_in_saddrs (t_D T) y (Hincl _ Hy)) as (sh & E & HinE & _).
  rewrite Forall_forall in Hws. specialize (Hws _ HinE). simpl in Hws.
  apply sepcon_valid_pointer2.
  eapply derives_trans; [apply (iter_sepcon_in_true (pool_item_rep (t_L T)) (t_D T) _ HinE) |].
  apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable; auto | vm_compute; reflexivity].
Qed.

Lemma hrx5_B8I_I2_itable_ptr sht tab T y : In y (t_L T) -> itable sht tab T |-- !! isptr y.
Proof.
  intros Hy. unfold itable. apply derives_extract_prop; intros Hwf. pose proof Hwf as (_ & Hincl & _ & Hws).
  destruct (hrx5_B8I_in_saddrs (t_D T) y (Hincl _ Hy)) as (sh & E & HinE & _).
  eapply derives_trans; [apply sepcon_derives; [apply TT_right |
    apply (iter_sepcon_in_true (pool_item_rep (t_L T)) (t_D T) _ HinE)] |].
  unfold pool_item_rep, entry_at. entailer!. match goal with H: field_compatible _ _ y |- _ => destruct H; auto end.
Qed.

(* ---------------------------------------------------------------------- *)
(* The device                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_I2_dev_ptr sh wg D : device_rep sh wg D |-- !! isptr wg.
Proof. unfold device_rep. Intros. apply prop_right. destruct H as [Hp _]. exact Hp. Qed.

Lemma hrx5_B8I_I2_vp_dev wg D R : device_rep Tsh wg D * R |-- valid_pointer (id_addr wg).
Proof.
  apply sepcon_valid_pointer1. apply hrx5_B8I_vp_sid.
  apply readable_nonidentity. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* QI's SEP list: the three components opened together                     *)
(* ---------------------------------------------------------------------- *)

Section QL.
Variable x25519: list byte -> list byte -> list byte.
Variables (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head: val) (KE: list kent4) (kc: int64) (q: int) (proto: Z)
  (ip4 ip6 port: list byte) (M: init_msg) (dp img: val) (a: val) (P: peer) (t ck2 h2: list byte)
  (key spub: list val) (sec1: list byte) (birth1: int64) (S1: shim) (lul1: int64).

(* QI's SEP list (hrx5_B8I_QI) *)
Definition hrx5_B8I_I2_QL : list mpred :=
  let s := hrx5_skb dp (OInit M) proto ip4 ip6 port in
  hrx5_B8I_world x25519 gv L R sec1 birth1 T head (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) S1 w
    kc lul1 (hrx5_B8I_log a (l_skb L) (sk_len s)) ++
  hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
  hrx5_cglobs gv FR ++
  [qlen_rep gv q; skb_rep Tsh (l_skb L) s; @malloc_token W Ews t_init dp; init_rep Ews dp M;
   img_rep img (init_bytes M)] ++
  hrx5_B8I_scr x25519 L R sec1 birth1 head S w s ck2 h2 key spub t.

(* the rest of it, besides the table, the nodes and the peers *)
Definition hrx5_B8I_I2_QR : list mpred :=
  let s := hrx5_skb dp (OInit M) proto ip4 ip6 port in
  [device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec1 birth1); ptable Tsh (l_ptd L) head;
   shim_state4 gv S1 w; noise_globals gv kc; lul_rep gv lul1; rxlog_rep gv (hrx5_B8I_log a (l_skb L) (sk_len s));
   @data_at HCS Tsh t_mident (mident_val (hrx5_ID x25519 R)) (l_id L);
   @data_at HCS Tsh t_mident (mident_val (hrx5_IK x25519 R)) (l_ik L);
   hbytes Tsh (rr_rawd R) (l_rawd L); hbytes Tsh (rr_rawk R) (l_rawk L);
   hbytes Tsh (hrx5_mk1 x25519 R) (l_mk1 L); hbytes Tsh (hrx5_ssk x25519 R) (l_ssk L);
   @data_at W Tsh (tptr t_hnode4) (hrx5_head (hnodes_snapped4 T NS PS)) (l_peers L);
   kents_rep W (hrx5_khead (map (kent_snapped T) KE)) (map (kent_snapped T) KE)] ++
  hrx5_cglobs gv FR ++
  [qlen_rep gv q; skb_rep Tsh (l_skb L) s; @malloc_token W Ews t_init dp; init_rep Ews dp M;
   img_rep img (init_bytes M)] ++
  hrx5_B8I_scr x25519 L R sec1 birth1 head S w s ck2 h2 key spub t.

Lemma hrx5_B8I_I2_QL_eq :
  fold_right_sepcon hrx5_B8I_I2_QL =
  itable Tsh (l_itd L) T * (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) *
  (peers_rep (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) * fold_right_sepcon hrx5_B8I_I2_QR)).
Proof.
  unfold hrx5_B8I_I2_QL, hrx5_B8I_I2_QR, hrx5_B8I_world, hrx5_rest. cbv zeta.
  rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon].
  apply pred_ext; cancel.
Qed.

(* QI's SEP gives the sixteen fields and a wand back to (anything below) it *)
Lemma hrx5_B8I_I2_open N (Y: mpred) :
  In (hs_addr a) (saddrs (t_D T)) -> Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  sfind PS a = Some (Ews, P) -> @field_compatible Noise.CS t_hs [] (hs_addr a) ->
  In N (hnodes_snapped4 T NS PS) ->
  hn_addr N = hrx5_nfind NS a -> hn_snap N = hsnap_val (hs_snap_cur T a P) -> hs_ok (p_hs P) ->
  (fold_right_sepcon hrx5_B8I_I2_QL |-- Y) ->
  fold_right_sepcon hrx5_B8I_I2_QL |--
  fold_right_sepcon (hrx5_B8I_I2_C (hs_addr a) (offset_val 8 (hrx5_nfind NS a)) (e_peer (t_entry_d T (hs_addr a)))
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a)))
      (e_index (t_entry_d T (hs_addr a))) (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P))
      (hs_psk (p_hs P)) ++
    [fold_right_sepcon (hrx5_B8I_I2_C (hs_addr a) (offset_val 8 (hrx5_nfind NS a))
      (e_peer (t_entry_d T (hs_addr a))) (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))
      (e_type (t_entry_d T (hs_addr a))) (e_index (t_entry_d T (hs_addr a))) (hs_sid (p_hs P)) (hs_eph (p_hs P))
      (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))) -* Y]).
Proof.
  intros Hin Hsh Hsf Hfc HN HNa HNs Hok HY.
  rewrite fold_right_sepcon_app. cbn [fold_right_sepcon]. rewrite sepcon_emp.
  unfold hrx5_B8I_I2_C. rewrite !fold_right_sepcon_app.
  rewrite hrx5_B8I_I2_QL_eq in *. rewrite <- HNa.
  apply hrx5_B8I_I2_comb;
    [ apply (hrx5_B8I_I2_citableY _ T (hs_addr a) _ Hin Hsh Hfc (derives_refl _))
    | apply (hrx5_B8I_I2_cpeerY PS a P M (s_boot S) t ck2 h2 _ Hsf (derives_refl _))
    | apply (hrx5_B8I_I2_cnodeY _ _ T a P N _ HN HNs Hok (derives_refl _))
    | exact HY ].
Qed.

End QL.

Ltac hrx5_B8I_I2_in :=
  cbn [hrx5_B8I_I2_QL hrx5_B8I_world hrx5_rest hrx5_cglobs hrx5_B8I_scr app In];
  repeat (first [left; reflexivity | right]).

(* the valid pointers of the block lemmas, through the wand *)
Lemma hrx5_B8I_I2_hv x25519 gv L FR R S w NS PS T head KE kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub
  sec1 birth1 S1 lul1 (Cl: list mpred) :
  sfind PS a = Some (Ews, P) -> hs_sid (p_hs P) = id_addr (l_wd L) -> e_peer (t_entry_d T (hs_addr a)) = a ->
  forall x, In x [e_peer (t_entry_d T (hs_addr a)); succ_in (t_L T) (hs_addr a); hs_sid (p_hs P)] ->
  fold_right_sepcon (Cl ++ [fold_right_sepcon Cl -*
    fold_right_sepcon (hrx5_B8I_I2_QL x25519 gv L FR R S w NS PS T head KE kc q proto ip4 ip6 port M dp img a P
      t ck2 h2 key spub sec1 birth1 S1 lul1)])
  |-- valid_pointer x.
Proof.
  intros Hsf Hsid Hep x Hx. eapply derives_trans; [apply hrx5_B8I_I2_mp |].
  destruct Hx as [<- | [<- | [<- | []]]].
  - rewrite Hep.
    apply (hrx5_B8I_I2_in_vp _ (peers_rep (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2))));
      [hrx5_B8I_I2_in |].
    apply (hrx5_B8I_I2_vp_peers PS a P _ TT Hsf).
  - destruct (hrx5_B8I_I2_succ_in (t_L T) (hs_addr a)) as [E | E]; [rewrite E; apply valid_pointer_null |].
    apply (hrx5_B8I_I2_in_vp _ (itable Tsh (l_itd L) T)); [hrx5_B8I_I2_in |].
    apply sepcon_valid_pointer1. apply hrx5_B8I_I2_itable_vp; exact E.
  - apply (hrx5_B8I_I2_in_vp _ (device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec1 birth1))); [hrx5_B8I_I2_in |].
    rewrite Hsid. apply hrx5_B8I_I2_vp_dev.
Qed.
