(* (common4 group hs): body of hs_same (v4 spec), closes hc4_body_hs_same *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common4.hc4b_hs_same_lem.

Module FH := WgNoise.harness.x_handshake.code.
Local Open Scope logic.
#[local] Existing Instance CSkh.
#[local] Instance hc4b_hs_same_j1 : change_composite_env HCS CSkh. make_cs_preserve HCS CSkh. Defined.
#[local] Instance hc4b_hs_same_j2 : change_composite_env CSkh HCS. make_cs_preserve CSkh HCS. Defined.
#[local] Instance hc4b_hs_same_j3 : change_composite_env Noise.CS CSkh. make_cs_preserve Noise.CS CSkh. Defined.
#[local] Instance hc4b_hs_same_j4 : change_composite_env CSkh Noise.CS. make_cs_preserve CSkh Noise.CS. Defined.

Ltac hc4b_hs_same_tc CSw VO whole shp p P sht tab T FC W HS :=
  apply denote_tc_test_eq_split;
  (sep_apply (derives_refl' _ _ (eq_sym (hc4b_hs_same_open sht tab T p _ _ FC W HS)));
   eapply derives_trans; [| apply (hc4b_hs_same_vp CSw VO whole shp p P sht tab T _ TT); auto]; cancel).

Ltac hc4b_hs_same_fin :=
  entailer!;
  match goal with H: typed_true tint _ |- _ => apply hc4b_hs_same_tt in H; rewrite H end;
  cbn [andb];
  first [ match goal with |- Val.of_bool (Bool.eqb ?x ?y) = _ => destruct x, y; reflexivity end
        | match goal with |- Val.of_bool ?X = bool2val ?Y => change Y with X; destruct X; reflexivity end
        | match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end ].
Ltac hc4b_hs_same_fin_false :=
  entailer!;
  match goal with H: typed_false tint _ |- _ => apply hc4b_hs_same_tf in H; rewrite H end;
  reflexivity.

Lemma hc4b_hs_same_body :
  forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_handshake.code.f_hs_same (hs_same4_spec CSw).
Proof.
  intros CSw. start_function.
  rename H into HV, SH into RS, SH0 into RP, SH1 into RT, H0 into HIn, H1 into VP.
  destruct (hc4b_hs_same_sfind_in _ _ HIn) as (she & E & HS).
  assert (HC: hs_snap_cur T p P = snap_of T (hs_addr p) E (p_hs P)).
  { unfold hs_snap_cur, t_entry_d, t_entry. rewrite HS. reflexivity. }
  rewrite HC in VP.
  unfold hs_ptrs, hs_ptrs_nn in VP. cbn [snap_of sn_next sn_entry sn_hs] in VP.
  repeat rewrite Forall_cons_iff in VP.
  destruct VP as (V1 & V2 & V3 & V4 & V5 & V6 & _).
  rewrite hc4b_hs_same_mem_eq.
  assert_PROP (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) as FCH.
  { unfold hc4b_hs_same_rest. entailer!. }
  destruct FCH as [FC HOK].
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (sn_next sn) /\ is_pointer_or_null (succ_in (t_L T) (hs_addr p)) /\
     is_pointer_or_null (e_peer (sn_entry sn)) /\ is_pointer_or_null (e_peer E) /\
     is_pointer_or_null (hs_sid (sn_hs sn)) /\ is_pointer_or_null (hs_sid (p_hs P))) as PN.
  { go_lower. match goal with |- ?L |-- _ => assert (K: forall x, vp_ok (hs_own p T VO) x -> L |-- !! is_pointer_or_null x) end.
    { intros x Vx. eapply derives_trans; [| apply (hc4b_hs_same_vp_pn CSw VO whole shp p P sht tab T x
        (data_at shs t_hsnap (hsnap_val sn) s * hc4b_hs_same_hsf shp (hs_addr p) (p_hs P))); auto]. cancel. }
    rewrite !prop_and. repeat apply andp_right; apply K; auto. }
  destruct PN as (PN1 & PN2 & PN3 & PN4 & PN5 & PN6).
  assert_PROP (@field_compatible HCS t_hsnap [] s /\ hs_ok (sn_hs sn)) as FCS.
  { entailer!.
    match goal with Hv: value_fits t_hsnap _ |- _ => unfold t_hsnap, hsnap_val in Hv; simplify_value_fits in Hv;
      destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _) end.
    simplify_value_fits in A1. simplify_value_fits in A2. simplify_value_fits in A3. simplify_value_fits in A4.
    simplify_value_fits in A5. simplify_value_fits in A6. simplify_value_fits in A7. simplify_value_fits in A8.
    unfold hs_ok, bytes in *. rewrite !Zlength_map in *. tauto. }
  destruct FCS as [FCs0 SOK].
  assert (FCs: @field_compatible CSkh t_hsnap [] s)
    by (apply (@field_compatible_change_composite HCS CSkh _ t_hsnap); auto).
  pose proof (hc4b_hs_same_fch p FC) as FCh.
  rewrite (hc4b_hs_same_open sht tab T p she E FC W HS).
  unfold hc4b_hs_same_hsf.
  unfold hsnap_val. rewrite hc4b_hs_same_snap_eq.
  pose proof SOK as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  rewrite (hc4b_hs_same_hbytes shs 32 (hs_eph (sn_hs sn))), (hc4b_hs_same_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc4b_hs_same_hbytes shs 32 (hs_reph (sn_hs sn))), (hc4b_hs_same_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc4b_hs_same_hbytes shs 32 (hs_psk (sn_hs sn))), (hc4b_hs_same_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc4b_hs_same_hbytes shs 32 (hs_ck (sn_hs sn))), (hc4b_hs_same_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  repeat flatten_sepcon_in_SEP.
  unfold entry_val.
  assert (Pp: isptr p) by (destruct FC; auto).
  assert (WS: writable_share she).
  { destruct W as (_ & _ & _ & HF). apply hc4b_hs_same_sfind_In in HS.
    rewrite Forall_forall in HF. apply (HF _ HS). }
  assert (RSh: readable_share she) by auto.
  remember (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) as bp eqn:B0.
  remember (if eq_dec (sn_next sn) (succ_in (t_L T) (hs_addr p)) then true else false) as b1 eqn:B1.
  remember (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false) as bs eqn:B2.
  change (hc4b_hs_same_isb bp (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false)) in B0.
  change (hc4b_hs_same_isb b1 (if eq_dec (sn_next sn) (succ_in (t_L T) (hs_addr p)) then true else false)) in B1.
  change (hc4b_hs_same_isb bs (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false)) in B2.
  forward. forward.
  forward_if (temp FH._t'1 (Val.of_bool (bp && b1))).
  { entailer!. hc4b_hs_same_tc CSw VO whole shp p P sht tab T FC W HS. }
  { forward. forward. forward.
    { entailer!. hc4b_hs_same_tc CSw VO whole shp p P sht tab T FC W HS. }
    entailer!. rewrite hc4b_hs_same_cmp by auto.
    unfold hc4b_hs_same_isb in B0, B1. subst bp b1.
    destruct (eq_dec (e_peer (sn_entry sn)) (e_peer E)); [|congruence]. reflexivity. }
  { forward. entailer!.
    unfold hc4b_hs_same_isb in B0. subst bp.
    destruct (eq_dec (e_peer (sn_entry sn)) (e_peer E)); [congruence|]. reflexivity. }
  assert (TB1: tc_val tbool (Val.of_bool (sn_hashed sn))) by (destruct (sn_hashed sn); hnf; auto).
  assert (TB2: tc_val tbool (Val.of_bool (vin (hs_addr p) (t_L T)))) by (destruct (vin _ _); hnf; auto).
  pose proof HOK as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  forward_if (temp FH._t'2 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T))))).
  { forward. forward. forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'3 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E)))).
  { forward. forward. forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'4 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E)))).
  { forward. forward. forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'5 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P))))).
  { forward. forward. forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'6 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P))))).
  { forward. forward. forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'7 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs))).
  { forward. forward. forward.
    { entailer!. hc4b_hs_same_tc CSw VO whole shp p P sht tab T FC W HS. }
    entailer!. rewrite hc4b_hs_same_cmp by auto.
    match goal with H: typed_true tint _ |- _ => apply hc4b_hs_same_tt in H; rewrite H end.
    unfold hc4b_hs_same_isb in B2. subst bs. reflexivity. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'8 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._ephemeral_private) s, hs_eph (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._ephemeral_private) (hs_addr p), hs_eph (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M1. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'10 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._remote_static) s, hs_rstatic (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._remote_static) (hs_addr p), hs_rstatic (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M2. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'12 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._remote_ephemeral) s, hs_reph (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._remote_ephemeral) (hs_addr p), hs_reph (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M3. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'14 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._precomputed_static_static) s, hs_ss (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._precomputed_static_static) (hs_addr p), hs_ss (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M4. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'16 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._preshared_key) s, hs_psk (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._preshared_key) (hs_addr p), hs_psk (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M5. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'18 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)) && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._hash) s, hs_hash (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._hash) (hs_addr p), hs_hash (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M6. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'20 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)) && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P)) && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._chaining_key) s, hs_ck (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._chaining_key) (hs_addr p), hs_ck (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M7. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'22 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)) && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P)) && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck (p_hs P)) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._latest_timestamp) s, hs_ts (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._latest_timestamp) (hs_addr p), hs_ts (p_hs P)).
    { split; [destruct FCs0 as [? _]; auto | destruct FCh as [? _]; auto]. }
    { entailer!. simpl. rewrite M8. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward_if (temp FH._t'24 (Val.of_bool (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)) && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P)) && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck (p_hs P)) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P)) && Int.eq (hs_rindex (sn_hs sn)) (hs_rindex (p_hs P))))).
  { forward. forward. forward. hc4b_hs_same_fin. }
  { forward. hc4b_hs_same_fin_false. }
  forward.
  rewrite HC.
  unfold hsnap_val. rewrite hc4b_hs_same_snap_eq.
  rewrite (hc4b_hs_same_hbytes shs 32 (hs_eph (sn_hs sn))), (hc4b_hs_same_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc4b_hs_same_hbytes shs 32 (hs_reph (sn_hs sn))), (hc4b_hs_same_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc4b_hs_same_hbytes shs 32 (hs_psk (sn_hs sn))), (hc4b_hs_same_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc4b_hs_same_hbytes shs 32 (hs_ck (sn_hs sn))), (hc4b_hs_same_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  rewrite hc4b_hs_same_mem_eq. unfold hc4b_hs_same_hsf.
  rewrite (hc4b_hs_same_open sht tab T p she E FC W HS). unfold entry_val.
  unfold hc4b_hs_same_isb in B0, B1, B2.
  rewrite (hc4b_hs_same_eqb sn T p E (p_hs P) bp b1 bs B0 B1 B2).
  entailer!.
  all: match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end.
Qed.