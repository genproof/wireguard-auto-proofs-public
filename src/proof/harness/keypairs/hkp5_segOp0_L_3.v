(* law keypairs, segment Op0 branch L, piece 3: statement 22 (CHECK(r == snap.hashed && !p.handshake.entry.hashed)).

   States: hkp5_segOp0_L_defs.v; "Op0 branch L". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require WgNoise.contracts.x_keypairs.
Require WgNoise.harness.x_keypairs.code.
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

#[local] Existing Instance W_keypairs.
Local Open Scope logic.
Local Open Scope Z_scope.

(* helpers *)
Lemma hkp5_o0L3_tc_bool b : tc_val tbool (Val.of_bool b).
Proof. destruct b; simpl; auto. Qed.

#[local] Instance hkp5_o0L3_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Definition hkp5_o0L3_CCEh : change_composite_env HCS W_keypairs.
Proof. make_cs_preserve HCS W_keypairs. Defined.

Lemma hkp5_o0L3_snapcs : cs_preserve_type HCS W_keypairs (@coeq _ _ hkp5_o0L3_CCEh) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0L3_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> VST.msl.iter_sepcon.iter_sepcon f D = (f (a, sh, E) * VST.msl.iter_sepcon.iter_sepcon f (sdel D a))%logic.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hkp5_o0L3_hscs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0L3_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0L3_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_keypairs (Tstruct KC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_keypairs hkp5_o0L3_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hkp5_o0L3_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_keypairs (Tstruct KC._wg_peer noattr) [StructField KC._handshake] p = hs_addr p.
Proof. intros H. apply hkp5_o0L3_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hkp5_o0L3_entry sh E nx hd p : @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s (entry_val E nx hd) (hs_addr p) =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
    (entry_val E nx hd) p.
Proof.
  intros FC.
  change [StructField KC._entry; StructField KC._handshake] with ([StructField KC._entry] ++ [StructField KC._handshake]).
  rewrite (@field_at_app W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._entry] [StructField KC._handshake]
             (entry_val E nx hd) (entry_val E nx hd) p (JMeq_refl _)).
  rewrite hkp5_o0L3_hsaddr by exact FC.
  transitivity (@field_at Noise.CS sh t_hs (DOT I._entry) (entry_val E nx hd) (hs_addr p)).
  2: { exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0L3_CCE sh t_hs
           [StructField I._entry] (entry_val E nx hd) (entry_val E nx hd) (JMeq_refl _) hkp5_o0L3_hscs)). }
  assert (FC1: @field_compatible Noise.CS t_peer (DOT I._handshake) p) by auto with field_compatible.
  assert (FC2: @field_compatible Noise.CS t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: @field_compatible Noise.CS t_hs (DOT I._entry) (hs_addr p)) by auto with field_compatible.
  rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hkp5_o0L3_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  (!! itable_wf T &&
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
   @field_at W_keypairs she (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
     (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) p *
   VST.msl.iter_sepcon.iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))))%logic.
Proof.
  intros FC HS. unfold itable. rewrite (hkp5_o0L3_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hkp5_o0L3_entry by exact FC.
  apply pred_ext; entailer!.
Qed.

Lemma hkp5_o0L_3_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> 
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0L_2 x25519 F V steps FR i O) hkp5_o0L_s3
    (overridePost (hkp5_o0L_2 x25519 F V steps FR i O) R).
Proof.
  intros HF HX HL.
  destruct O as [Y E k kp].
  destruct F as [gv w t pt p raw pub snap opub first second].
  unfold hkp5_o0L_2, hkp5_o0L_props, hkp5_o0L_locals2, hkp5_o0L_SEP, hkp5_o0_props, hkp5_lvars in *.
  cbv zeta.
  unfold hkp5_o0L_fs, hk5_items, hkp5_globs.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second o_Y o_E o_k o_kp] in *.
  Intros.
  unfold hkp5_o0L_facts in HL. cbv zeta in HL.
  cbn [f_p o_Y o_E o_k o_kp] in HL.
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub; f_snap := snap;
                f_opub := opub; f_first := first; f_second := second |}) in *.
  set (O0 := {| o_Y := Y; o_E := E; o_k := k; o_kp := kp |}) in *.
  set (HH1 := hkp5_o0L_H1 F0 O0) in *.
  set (HH3 := hkp5_o0L_H3 F0 O0) in *.
  set (sn := o5_sn p O0) in *.
  set (res := o5_res p O0) in *.
  clearbody HH1 HH3 sn res.
  destruct res as [[[r P'] [KS' T' S']] kc'].
  cbn [fst snd kw_KS kw_T kw_S] in *.
  destruct HL as (Hr & Hkc & Hhs & Hdev & Hrefs & Hpr & Hslot & HK & Hent & Hvin & Hal & Hfl & Hrel & Hwarn & Hfr & Hal2 & Hl1 & Hl2).
  assert (HS: sfind (t_D T') (hs_addr p) = Some (Tsh, E)).
  { destruct Hrel as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (idx & Hf) & _) & _).
    unfold t_entry in Hent. rewrite Hf in Hent |- *. injection Hent as <-. reflexivity. }
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfcp by (unfold peer_rep; entailer!).
  rewrite (hkp5_o0L3_open Tsh t T' p Tsh E Hfcp HS).
  rewrite (@data_at_change_composite HCS W_keypairs hkp5_o0L3_CCEh Tsh t_hsnap (hsnap_val sn) (hsnap_val sn) (JMeq_refl _) hkp5_o0L3_snapcs).
  destruct sn as [sE snx shd shs].
  unfold entry_val, hsnap_val. cbn [sn_entry sn_next sn_hashed sn_hs] in *.
  subst r. rewrite Hvin.
  destruct R as [Rn Rb Rc Rr].
  unfold hkp5_Delta.
  abbreviate_semax.
  Intros.
  unfold hkp5_o0L_s3.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'33 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward.
      forward.
      entailer!. }
    { exfalso. match goal with Hf: typed_false _ _ |- _ => destruct shd; compute in Hf; discriminate Hf end. }
    forward_if.
    { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward.
    entailer!.
  + forward. apply ENTAIL_refl.
  + subst POSTCONDITION. unfold abbreviate, overridePost. cbn [RA_normal].
    entailer!.
Qed.
