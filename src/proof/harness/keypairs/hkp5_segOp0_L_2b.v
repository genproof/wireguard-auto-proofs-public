(* law keypairs, segment Op0 branch L, piece 2b: statements 15..21 (if (!id_known) {next_id = kp->internal_id; id_known = 1}; k->id; next_id++;
   k->next = live; live = k; k->hashed / k->index from snap).

   States: hkp5_segOp0_L_defs.v; "Op0 branch L". *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Export WgNoise.proof.harness.keypairs.hkp5_segOp0_L_defs.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require WgNoise.proof.harness.common.hc3_body_snap.
Require WgNoise.harness.x_handshake.code.

Module HB := WgNoise.proof.harness.common.hc3_body_snap.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---- helpers (prefix hkp5_o0L2b_; port of v1's hkp4_o0L2b_) ---- *)

#[local] Instance hkp5_o0L2b_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkp5_o0L2b_kpcs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0L2b_CCE) t_kp = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0L2b_wand_gen (A B C R: mpred) : (B |-- A * R)%logic -> (R * A |-- C)%logic -> (B |-- A * (A -* C))%logic.
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. exact H2.
Qed.

Ltac hkp5_o0L2b_remove A t :=
  match t with
  | sepcon ?X A => X
  | sepcon ?X ?Y => let X' := hkp5_o0L2b_remove A X in constr:(sepcon X' Y)
  end.

Lemma hkp5_o0L2b_id_cs kp v :
  @field_at Noise.CS Ews t_kp [StructField prot_repr3.I._internal_id] (Vlong v) kp =
  @field_at W_keypairs Ews (Tstruct KC._noise_keypair noattr) [StructField KC._internal_id] (Vlong v) kp.
Proof.
  exact (f_equal (fun f => f kp) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0L2b_CCE Ews t_kp
           [StructField prot_repr3.I._internal_id] (Vlong v) (Vlong v) (JMeq_refl _) hkp5_o0L2b_kpcs)).
Qed.

Definition hkp5_o0L2b_idf (kp: val) (v: int64) : mpred :=
  @field_at W_keypairs Ews (Tstruct KC._noise_keypair noattr) [StructField KC._internal_id] (Vlong v) kp.

Lemma hkp5_o0L2b_kp1_open kp K :
  keypair_rep W_keypairs kp K |--
  hkp5_o0L2b_idf kp (kp_id K) * (hkp5_o0L2b_idf kp (kp_id K) -* keypair_rep W_keypairs kp K).
Proof.
  unfold keypair_rep at 1. apply derives_extract_prop; intros HP.
  unfold hkp5_o0L2b_idf. rewrite hkp5_o0L2b_id_cs.
  match goal with |- ?B |-- sepcon ?A (wand _ ?C) =>
    let R := hkp5_o0L2b_remove A B in
    apply (hkp5_o0L2b_wand_gen A B C R) end.
  - cancel.
  - unfold keypair_rep. rewrite hkp5_o0L2b_id_cs.
    apply andp_right; [apply prop_right; exact HP |]. cancel.
Qed.

Lemma hkp5_o0L2b_kp_open KS kp K : In (kp, K) KS ->
  keypairs_rep W_keypairs KS |--
  hkp5_o0L2b_idf kp (kp_id K) * (hkp5_o0L2b_idf kp (kp_id K) -* keypairs_rep W_keypairs KS).
Proof.
  intros Hin. apply in_split in Hin as (l1 & l2 & ->).
  unfold keypairs_rep. rewrite VST.msl.iter_sepcon.iter_sepcon_app. cbn [VST.msl.iter_sepcon.iter_sepcon].
  unfold keypair_item_rep at 2.
  sep_apply (hkp5_o0L2b_kp1_open kp K).
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  apply -> wand_sepcon_adjoint.
  rewrite (sepcon_comm _ (hkp5_o0L2b_idf kp (kp_id K))), <- sepcon_assoc.
  sep_apply (wand_frame_elim (hkp5_o0L2b_idf kp (kp_id K)) (keypair_rep W_keypairs kp K)).
  change (keypair_item_rep W_keypairs (kp, K)) with (keypair_rep W_keypairs kp K). cancel.
Qed.

Definition hkp5_o0L2b_snf (s: val) (b: bool) (idx: int) : mpred :=
  (@field_at W_keypairs Tsh (Tstruct KC._hs_snap noattr) [StructField KC._hashed] (Val.of_bool b) s *
   @field_at W_keypairs Tsh (Tstruct KC._hs_snap noattr) [StructField KC._index] (Vint idx) s)%logic.

Definition hkp5_o0L2b_CCEk : change_composite_env CSkh W_keypairs.
Proof. make_cs_preserve CSkh W_keypairs. Defined.

Lemma hkp5_o0L2b_snapcsk : cs_preserve_type CSkh W_keypairs (@coeq _ _ hkp5_o0L2b_CCEk) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0L2b_hashed_cs s v :
  @field_at CSkh Tsh t_hsnap (DOT WgNoise.harness.x_handshake.code._hashed) v s =
  @field_at W_keypairs Tsh (Tstruct KC._hs_snap noattr) [StructField KC._hashed] v s.
Proof.
  exact (f_equal (fun f => f s) (@field_at_change_composite CSkh W_keypairs hkp5_o0L2b_CCEk Tsh t_hsnap
           (DOT WgNoise.harness.x_handshake.code._hashed) v v (JMeq_refl _) hkp5_o0L2b_snapcsk)).
Qed.

Lemma hkp5_o0L2b_index_cs s v :
  @field_at CSkh Tsh t_hsnap (DOT WgNoise.harness.x_handshake.code._index) v s =
  @field_at W_keypairs Tsh (Tstruct KC._hs_snap noattr) [StructField KC._index] v s.
Proof.
  exact (f_equal (fun f => f s) (@field_at_change_composite CSkh W_keypairs hkp5_o0L2b_CCEk Tsh t_hsnap
           (DOT WgNoise.harness.x_handshake.code._index) v v (JMeq_refl _) hkp5_o0L2b_snapcsk)).
Qed.

Lemma hkp5_o0L2b_snap_open sn s :
  @data_at HCS Tsh t_hsnap (hsnap_val sn) s |--
  hkp5_o0L2b_snf s (sn_hashed sn) (e_index (sn_entry sn)) *
  (hkp5_o0L2b_snf s (sn_hashed sn) (e_index (sn_entry sn)) -* @data_at HCS Tsh t_hsnap (hsnap_val sn) s).
Proof.
  unfold hsnap_val at 1. rewrite HB.hc3b_snap_take_snap_eq.
  rewrite hkp5_o0L2b_hashed_cs, hkp5_o0L2b_index_cs.
  unfold hkp5_o0L2b_snf.
  match goal with |- ?B |-- sepcon (sepcon ?A1 ?A2) (wand _ ?C) =>
    let R1 := hkp5_o0L2b_remove A1 B in
    let R := hkp5_o0L2b_remove A2 R1 in
    apply (hkp5_o0L2b_wand_gen (sepcon A1 A2) B C R) end.
  - cancel.
  - unfold hsnap_val. rewrite HB.hc3b_snap_take_snap_eq.
    rewrite hkp5_o0L2b_hashed_cs, hkp5_o0L2b_index_cs. cancel.
Qed.

Lemma hkp5_o0L2b_head_pn ML : hk5_mklist ML |-- !! is_pointer_or_null (hk5_head ML).
Proof.
  destruct ML as [|[m M] ML]; cbn [hk5_head hk5_mklist].
  - apply prop_right. simpl; auto.
  - unfold hk5_node. Intros. entailer!.
Qed.

Lemma hkp5_o0L2b_node_fold k M nx : Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5 (hk5_mk_val M nx) k * malloc_token Ews t_mk5 k |-- hk5_node k M nx.
Proof. intros L1 L2. unfold hk5_node. apply andp_right; [apply prop_right; auto | apply derives_refl]. Qed.

Lemma hkp5_o0L_2b_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> 
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0L_1b x25519 F V steps FR i O) hkp5_o0L_s2b
    (overridePost (hkp5_o0L_2 x25519 F V steps FR i O) R).
Proof.
  intros HF HX HO.
  unfold hkp5_o0L_facts in HO. cbv zeta in HO.
  destruct HO as (Hr & Hkc & Hhs & Hdev & Hrefs & Hpsnap & Hslot & HK & HE & Hvin & Hal & Hfl & Hrel3 & Hwarn
                  & Hfr & Hal2 & Hl1 & Hl2).
  unfold hkp5_o0L_1b, hkp5_o0L_2, hkp5_Delta.
  unfold hkp5_o0L_H1, h5_set_ML.
  unfold hkp5_o0L_props, hkp5_o0_props, hkp5_o0L_locals1, hkp5_o0L_locals2, hkp5_o0_locals, hkp5_o0L_SEP,
    hkp5_o0L_fs, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars, hkp5_o0L_kv1.
  cbv zeta.
  cbn [app h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  set (res := o5_res (f_p F) O) in *.
  set (HH := y_H (o_Y O)) in *.
  set (M := hkp5_o0L_mk F O) in *.
  set (sn := o5_sn (f_p F) O) in *.
  Intros.
  assert (Hnid: y_id_known (o_Y O) = true -> y_next_id (o_Y O) = Int64.add (y_kc (o_Y O)) Int64.one)
    by (match goal with Hi: hkp5_inv0 _ _ _ |- _ => destruct Hi as (_ & _ & _ & _ & _ & _ & _ & Hid & _); exact Hid end).
  assert (Ls: Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32).
  { unfold M, hkp5_o0L_mk, hkp5_o0_mk. cbn [m5_send m5_recv]. destruct (hkp5_o0L_init O); auto. }
  assert (EMh: m5_hashed M = sn_hashed sn) by reflexivity.
  assert (EMi: m5_index M = if sn_hashed sn then e_index (sn_entry sn) else Int.zero) by reflexivity.
  assert (EMid: m5_id M = Int64.add (y_kc (o_Y O)) Int64.one) by reflexivity.
  clearbody M sn.
  destruct R as [Rn Rb Rc Rr].
  unfold hkp5_o0L_s2b.
  abbreviate_semax.
  (* if (!id_known) { next_id = kp->internal_id; id_known = 1; } *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    let Qf := eval pattern (y_next_id (o_Y O)), (y_id_known (o_Y O)) in Q in
    match Qf with ?f _ _ =>
      forward_if (PROPx P (LOCALx (f (Int64.add (y_kc (o_Y O)) Int64.one) true) (SEPx Rs))) end end.
  { destruct (y_id_known (o_Y O)) eqn:Eid.
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    sep_apply (hkp5_o0L2b_kp_open _ _ _ HK). unfold hkp5_o0L2b_idf. Intros.
    forward. forward.
    sep_apply (wand_frame_elim
      (@field_at W_keypairs Ews (Tstruct KC._noise_keypair noattr) [StructField KC._internal_id]
         (Vlong (kp_id (kp_new (p_hs (y_P (o_Y O))) (Int64.add (y_kc (o_Y O)) Int64.one) (y_now (o_Y O))))) (o_kp O))
      (keypairs_rep W_keypairs (kw_KS (snd (fst res))))).
    entailer!. }
  { destruct (y_id_known (o_Y O)) eqn:Eid.
    2: { exfalso. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    rewrite (Hnid eq_refl). forward. entailer!. }
  forward.
  forward.
  assert_PROP (is_pointer_or_null (hk5_head (h5_ML HH))) as Phd
    by (sep_apply (hkp5_o0L2b_head_pn (h5_ML HH)); entailer!).
  forward.
  forward.
  forward.
  sep_apply (hkp5_o0L2b_snap_open sn (f_snap F)). unfold hkp5_o0L2b_snf. Intros.
  forward.
  forward.
  forward.
  forward_if (temp KC._t'32 (Vint (if sn_hashed sn then e_index (sn_entry sn) else Int.zero))).
  { forward. forward.
    match goal with Hc: typed_true tbool _ |- _ => rename Hc into Htt end.
    destruct (sn_hashed sn); [entailer! | exfalso; inv Htt]. }
  { forward.
    match goal with Hc: typed_false tbool _ |- _ => rename Hc into Htt end.
    destruct (sn_hashed sn); [exfalso; inv Htt | entailer!]. }
  forward.
  sep_apply (wand_frame_elim
    (sepcon (@field_at W_keypairs Tsh (Tstruct KC._hs_snap noattr) [StructField KC._hashed] (Val.of_bool (sn_hashed sn)) (f_snap F))
     (@field_at W_keypairs Tsh (Tstruct KC._hs_snap noattr) [StructField KC._index] (Vint (e_index (sn_entry sn))) (f_snap F)))
    (@data_at HCS Tsh t_hsnap (hsnap_val sn) (f_snap F))).
  match goal with |- context [@data_at _ Ews t_mk5 ?v (o_k O)] =>
    replace v with (hk5_mk_val M (hk5_head (h5_ML HH)))
      by (unfold hk5_mk_val; rewrite EMh, EMi, EMid; destruct (sn_hashed sn); reflexivity) end.
  sep_apply (hkp5_o0L2b_node_fold (o_k O) M (hk5_head (h5_ML HH)) (proj1 Ls) (proj2 Ls)).
  change (hk5_head ((o_k O, M) :: h5_ML HH)) with (o_k O).
  change (hk5_mklist ((o_k O, M) :: h5_ML HH))
    with (sepcon (hk5_node (o_k O) M (hk5_head (h5_ML HH))) (hk5_mklist (h5_ML HH))).
  change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one.
  entailer!.
Qed.
