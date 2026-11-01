(* body of hs_take (v4 spec: hs_mem whole, the entry from the
   pool of T), adapted from hc3_body_snap.v's hc4nb2_hs_tk_body_fix (whose helpers hc4nb2_hs_tk_* are
   reused). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4nb2_hs_tklib.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_handshake.code.

Module FH := WgNoise.harness.x_handshake.code.
Local Open Scope logic.
Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Section Take.
#[local] Existing Instance CSkhnb.
#[local] Instance hc4nb2_hs_take_cce_n : change_composite_env Noise.CS CSkhnb.
Proof. make_cs_preserve Noise.CS CSkhnb. Defined.

(* the handshake's memory but the fields hs_take reads *)
Definition hc4nb2_hs_take_rest (whole: bool) (sh: share) (p: val) (P: peer) : mpred :=
  if whole then hc4nb2_hs_tk_prest sh p P
  else !! hs_ok (p_hs P) &&
       ((EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk (hs_addr p)) *
        spacer sh 36 40 (hs_addr p) * spacer sh 300 304 (hs_addr p) *
        @field_at_ Noise.CS sh t_peer [StructField I._device] p).

Lemma hc4nb2_hs_take_mem whole sh p P :
  hs_mem whole sh p P = hc4nb2_hs_tk_hsf sh (hs_addr p) (p_hs P) * hc4nb2_hs_take_rest whole sh p P.
Proof.
  destruct whole; [apply hc4nb2_hs_tk_peer_eq|].
  unfold hs_mem, hs_rep, hc4nb2_hs_take_rest.
  apply pred_ext.
  - Intros. rewrite hc4nb2_hs_tk_hsf_eq by auto. Intros lk. Exists lk. entailer!.
  - Intros lk. rewrite hc4nb2_hs_tk_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc4nb2_hs_take_fch whole sh p P :
  hs_mem whole sh p P |-- !! (field_compatible t_hs [] (hs_addr p) /\ hs_ok (p_hs P)).
Proof.
  destruct whole; unfold hs_mem.
  - rewrite hc4nb2_hs_tk_peer_eq. unfold hc4nb2_hs_tk_prest. Intros. apply prop_right.
    split; auto. apply hc4nb2_hs_tk_fch; auto.
  - unfold hs_rep. Intros.
    sep_apply (@field_at_compatible' Noise.CS sh t_hs [StructField I._state] (Vint (hs_state (p_hs P))) (hs_addr p)).
    Intros. apply prop_right. split; auto.
    match goal with Hc: @field_compatible Noise.CS t_hs _ (hs_addr p) |- _ =>
      destruct Hc as (A1 & A2 & A3 & A4 & A5 & _) end.
    apply (@field_compatible_change_composite Noise.CS CSkhnb _ t_hs); [reflexivity|].
    repeat split; auto.
Qed.

Lemma hc4nb2_hs_take_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hc4nb2_hs_take_entry_fa sh v h :
  field_compatible t_hs [] h ->
  @data_at Noise.CS sh t_entry_s v h = @field_at CSkhnb sh t_hs (DOT FH._entry) v h.
Proof.
  intros FC2.
  rewrite (@data_at_change_composite Noise.CS CSkhnb _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC3: field_compatible t_hs (DOT FH._entry) h) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (destruct FC2 as [Hp _]; exact Hp).
  reflexivity.
Qed.

Lemma hc4nb2_hs_take_open sht tab T h she E :
  field_compatible t_hs [] h -> itable_wf T -> sfind (t_D T) h = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at CSkhnb she t_hs (DOT FH._entry) (entry_val E (succ_in (t_L T) h) (vin h (t_L T))) h *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) h)).
Proof.
  intros FC W HS. unfold itable. rewrite (hc4nb2_hs_tk_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hc4nb2_hs_take_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma hc4nb2_hs_take_body :
  @semax_body [] hc4_G_hs_take CSkhnb FH.f_hs_take hs_take4_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_hs [] (hs_addr p) /\ hs_ok (p_hs P)) as FCH.
  { sep_apply hc4nb2_hs_take_fch. entailer!. }
  destruct FCH as [FCh HOK].
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  destruct (hc4nb2_hs_take_sfind_in _ _ H) as (she & E & HS).
  assert (TE: t_entry_d T (hs_addr p) = E) by (unfold t_entry_d, t_entry; rewrite HS; reflexivity).
  unfold hs_snap_cur. rewrite TE in *. clear TE.
  assert_PROP (Forall isptr (saddrs (t_D T))) as PP.
  { unfold itable. Intros. sep_apply hc4nb2_hs_tk_pool_ptrs. entailer!. }
  pose proof (hc4nb2_hs_tk_succ_ptr T (hs_addr p) W PP) as PN.
  assert_PROP (field_compatible t_hsnap [] s) as FCs.
  { sep_apply hc4nb2_hs_tk_fcs. entailer!. }
  rewrite (hc4nb2_hs_take_open sht tab T (hs_addr p) she E FCh W HS).
  rewrite hc4nb2_hs_take_mem. unfold hc4nb2_hs_tk_hsf.
  change (@data_at_ HCS shs t_hsnap s) with (@data_at HCS shs t_hsnap
    (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
     (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 32,
     (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 12, Vundef)))))))))))))))) s).
  rewrite hc4nb2_hs_tk_snap_eq. rewrite !hc4nb2_hs_tk_hout.
  repeat flatten_sepcon_in_SEP.
  destruct HOK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  assert (WS: writable_share she).
  { destruct W as (_ & _ & _ & HF). apply hc4nb2_hs_tk_sfind_In in HS.
    rewrite Forall_forall in HF. apply (HF _ HS). }
  unfold entry_val.
  assert_PROP (is_pointer_or_null (e_peer E) /\ is_pointer_or_null (hs_sid (p_hs P))) as PEPS.
  { entailer!. split.
    - match goal with Hv: value_fits _ (e_peer E, _) |- _ => rewrite value_fits_eq in Hv; simpl in Hv; destruct Hv as [Hv _]; apply Hv; auto end.
    - match goal with Hv: tc_val' _ (hs_sid (p_hs P)) |- _ => apply Hv; auto end. }
  destruct PEPS as [PE PS].
  do 4 forward. forward.
  1: (entailer!; destruct (vin (hs_addr p) (t_L T)); simpl; auto).
  do 11 forward.
  forward_call (shs, field_address t_hsnap (DOT FH._ephemeral_private) s, shp,
                field_address t_hs (DOT FH._ephemeral_private) (hs_addr p), hs_eph (p_hs P)).
  { entailer!. rewrite L1, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L1. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._remote_static) s, shp,
                field_address t_hs (DOT FH._remote_static) (hs_addr p), hs_rstatic (p_hs P)).
  { entailer!. rewrite L2, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L2. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._remote_ephemeral) s, shp,
                field_address t_hs (DOT FH._remote_ephemeral) (hs_addr p), hs_reph (p_hs P)).
  { entailer!. rewrite L3, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L3. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._precomputed_static_static) s, shp,
                field_address t_hs (DOT FH._precomputed_static_static) (hs_addr p), hs_ss (p_hs P)).
  { entailer!. rewrite L4, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L4. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._preshared_key) s, shp,
                field_address t_hs (DOT FH._preshared_key) (hs_addr p), hs_psk (p_hs P)).
  { entailer!. rewrite L5, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L5. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._hash) s, shp,
                field_address t_hs (DOT FH._hash) (hs_addr p), hs_hash (p_hs P)).
  { entailer!. rewrite L6, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L6. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._chaining_key) s, shp,
                field_address t_hs (DOT FH._chaining_key) (hs_addr p), hs_ck (p_hs P)).
  { entailer!. rewrite L7, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L7. cancel. }
  forward_call (shs, field_address t_hsnap (DOT FH._latest_timestamp) s, shp,
                field_address t_hs (DOT FH._latest_timestamp) (hs_addr p), hs_ts (p_hs P)).
  { entailer!. rewrite L8, !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite L8. cancel. }
  forward. forward.
  replace (force_val (sem_cast_i2bool (Val.of_bool (vin (hs_addr p) (t_L T)))))
    with (Val.of_bool (vin (hs_addr p) (t_L T))) by (destruct (vin _ _); reflexivity).
  unfold hsnap_val, snap_of. cbv zeta. cbn [sn_entry sn_next sn_hashed sn_hs].
  rewrite hc4nb2_hs_tk_snap_eq.
  rewrite (hc4nb2_hs_tk_hbytes shs 32 (hs_eph (p_hs P))), (hc4nb2_hs_tk_hbytes shs 32 (hs_rstatic (p_hs P))),
    (hc4nb2_hs_tk_hbytes shs 32 (hs_reph (p_hs P))), (hc4nb2_hs_tk_hbytes shs 32 (hs_ss (p_hs P))),
    (hc4nb2_hs_tk_hbytes shs 32 (hs_psk (p_hs P))), (hc4nb2_hs_tk_hbytes shs 32 (hs_hash (p_hs P))),
    (hc4nb2_hs_tk_hbytes shs 32 (hs_ck (p_hs P))), (hc4nb2_hs_tk_hbytes shs 12 (hs_ts (p_hs P))) by auto.
  rewrite hc4nb2_hs_take_mem. unfold hc4nb2_hs_tk_hsf.
  rewrite (hc4nb2_hs_take_open sht tab T (hs_addr p) she E FCh W HS).
  entailer!.
  unfold hs_snap_cur, t_entry_d, t_entry; rewrite HS; cbn [sn_entry snap_of]; cancel.
Qed.
End Take.
