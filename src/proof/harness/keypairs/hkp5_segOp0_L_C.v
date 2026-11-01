(* law keypairs, segment Op0 branch L, piece C: statement 3 (CHECK(kp->sending_counter.counter == 0 && replay_counter_fresh(&kp->receiving_counter)): kp is
   begin_session's kp_new, fresh counters).

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

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers (prefix hkp5_o0LC_)                                             *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hkp5_o0LC_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkp5_o0LC_kpcs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0LC_CCE) t_kp = true.
Proof. vm_compute; reflexivity. Qed.

(* a factor A of B, the rest R kept in a wand *)
Lemma hkp5_o0LC_wand_gen (A B C R: mpred) : (B |-- A * R)%logic -> (R * A |-- C)%logic -> (B |-- A * (A -* C))%logic.
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. exact H2.
Qed.

(* t without the factor A (a left-nested sepcon chain) *)
Ltac hkp5_o0LC_remove A t :=
  match t with
  | sepcon ?X A => X
  | sepcon ?X ?Y => let X' := hkp5_o0LC_remove A X in constr:(sepcon X' Y)
  end.

(* the keypair's sending counter at main's compspecs *)
Lemma hkp5_o0LC_sc_cs kp v :
  @field_at Noise.CS Ews t_kp [StructField prot_repr3.I._sending_counter] (Vlong v) kp =
  @field_at W_keypairs Ews (Tstruct KC._noise_keypair noattr) [StructField KC._sending_counter] (Vlong v) kp.
Proof.
  exact (f_equal (fun f => f kp) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0LC_CCE Ews t_kp
           [StructField prot_repr3.I._sending_counter] (Vlong v) (Vlong v) (JMeq_refl _) hkp5_o0LC_kpcs)).
Qed.

Definition hkp5_o0LC_scf (kp: val) (v: int64) : mpred :=
  @field_at W_keypairs Ews (Tstruct KC._noise_keypair noattr) [StructField KC._sending_counter] (Vlong v) kp.

Definition hkp5_o0LC_rcf (kp: val) (rc: int64) (lk: val) (bt: list int64) : mpred :=
  @data_at Noise.CS Ews hk5_t_rc (Vlong rc, (lk, map Vlong bt))
    (@field_address Noise.CS t_kp [StructField prot_repr3.I._receiving_counter] kp).

Lemma hkp5_o0LC_rc_eq kp rc lk bt :
  @field_at Noise.CS Ews t_kp [StructField prot_repr3.I._receiving_counter] (Vlong rc, (lk, map Vlong bt)) kp =
  hkp5_o0LC_rcf kp rc lk bt.
Proof.
  unfold hkp5_o0LC_rcf. rewrite field_at_data_at. reflexivity.
Qed.

Lemma hkp5_o0LC_kp1_open kp K :
  keypair_rep W_keypairs kp K |--
  EX lk: val, !! (@field_compatible Noise.CS t_kp [] kp) &&
  ((hkp5_o0LC_scf kp (kp_scounter K) * hkp5_o0LC_rcf kp (kp_rcounter K) lk (kp_backtrack K)) *
   ((hkp5_o0LC_scf kp (kp_scounter K) * hkp5_o0LC_rcf kp (kp_rcounter K) lk (kp_backtrack K)) -*
    keypair_rep W_keypairs kp K)).
Proof.
  unfold keypair_rep at 1. Intros r lk. Exists lk. apply andp_right; [apply prop_right; tauto |].
  unfold hkp5_o0LC_scf. rewrite hkp5_o0LC_sc_cs. rewrite hkp5_o0LC_rc_eq.
  match goal with |- ?B |-- sepcon (sepcon ?A1 ?A2) (wand _ ?C) =>
    let R1 := hkp5_o0LC_remove A1 B in let R := hkp5_o0LC_remove A2 R1 in
    apply (hkp5_o0LC_wand_gen (sepcon A1 A2) B C R) end.
  - cancel.
  - unfold keypair_rep. rewrite hkp5_o0LC_sc_cs, <- hkp5_o0LC_rc_eq.
    apply andp_right; [apply prop_right; tauto |]. Exists r lk. cancel.
Qed.

Lemma hkp5_o0LC_kp_open KS kp K : In (kp, K) KS ->
  keypairs_rep W_keypairs KS |--
  EX lk: val, !! (@field_compatible Noise.CS t_kp [] kp) &&
  ((hkp5_o0LC_scf kp (kp_scounter K) * hkp5_o0LC_rcf kp (kp_rcounter K) lk (kp_backtrack K)) *
   ((hkp5_o0LC_scf kp (kp_scounter K) * hkp5_o0LC_rcf kp (kp_rcounter K) lk (kp_backtrack K)) -*
    keypairs_rep W_keypairs KS)).
Proof.
  intros Hin. apply in_split in Hin as (l1 & l2 & ->).
  unfold keypairs_rep. rewrite VST.msl.iter_sepcon.iter_sepcon_app. cbn [VST.msl.iter_sepcon.iter_sepcon].
  unfold keypair_item_rep at 2.
  sep_apply (hkp5_o0LC_kp1_open kp K). Intros lk. Exists lk.
  apply andp_right; [apply prop_right; assumption |].
  set (A := hkp5_o0LC_scf kp (kp_scounter K) * hkp5_o0LC_rcf kp (kp_rcounter K) lk (kp_backtrack K)).
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  apply -> wand_sepcon_adjoint.
  sep_apply (wand_frame_elim A (keypair_rep W_keypairs kp K)).
  change (keypair_item_rep W_keypairs (kp, K)) with (keypair_rep W_keypairs kp K). cancel.
Qed.

Lemma hkp5_o0L_C_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> 
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0L_1 x25519 F V steps FR i O) hkp5_o0L_sC
    (overridePost (hkp5_o0L_1 x25519 F V steps FR i O) R).
Proof.
  intros HM Hx HF.
  unfold hkp5_o0L_facts in HF. cbv zeta in HF.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & HK & _).
  unfold hkp5_o0L_1, hkp5_Delta, hkp5_o0L_locals1, hkp5_o0_SEP, hkp5_o0L_fs, hk5_items, hkp5_hglobs, hkp5_globs,
    hkp5_o0L_props, hkp5_o0_props, hkp5_o0_locals, hkp5_temps, hkp5_lvars.
  cbv zeta. cbn [app].
  set (KS' := kw_KS (snd (fst (o5_res (f_p F) O)))) in *.
  let K := constr:(kp_new (p_hs (y_P (o_Y O))) (Int64.add (y_kc (o_Y O)) Int64.one) (y_now (o_Y O))) in
  replace_SEP 4 (EX lk: val, !! (@field_compatible Noise.CS t_kp [] (o_kp O)) &&
    ((hkp5_o0LC_scf (o_kp O) (kp_scounter K) * hkp5_o0LC_rcf (o_kp O) (kp_rcounter K) lk (kp_backtrack K)) *
     ((hkp5_o0LC_scf (o_kp O) (kp_scounter K) * hkp5_o0LC_rcf (o_kp O) (kp_rcounter K) lk (kp_backtrack K)) -*
      keypairs_rep W_keypairs KS'))).
  { go_lower. apply (hkp5_o0LC_kp_open _ _ _ HK). }
  Intros lk.
  cbn [kp_scounter kp_rcounter kp_backtrack kp_new].
  destruct R as [Rn Rb Rc Rr].
  unfold hkp5_o0L_sC; abbreviate_semax.
  unfold hkp5_o0LC_scf.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'27 (Vint Int.one) :: Q) (SEPx S))) end.
    { unfold hkp5_o0LC_rcf.
      forward_call (Ews, @field_address Noise.CS t_kp [StructField prot_repr3.I._receiving_counter] (o_kp O),
                    Int64.zero, lk, Zrepeat Int64.zero 128).
      match goal with |- context [temp KC._t'28 (Vint (if ?b then _ else _))] =>
        replace b with true by reflexivity end.
      forward.
      unfold hkp5_o0LC_rcf. entailer!. }
    { match goal with Hc: Int64.repr 0 <> Int64.repr 0 |- _ => exfalso; exact (Hc eq_refl) end. }
    forward_if.
    { match goal with Hc: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero Hc) end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  match goal with Hpo := @abbreviate ret_assert _ |- _ => unfold Hpo, abbreviate end.
  cbn [RA_normal overridePost].
  sep_apply (wand_frame_elim
    (field_at Ews (Tstruct KC._noise_keypair noattr) (DOT KC._sending_counter) (Vlong Int64.zero) (o_kp O) *
     hkp5_o0LC_rcf (o_kp O) Int64.zero lk (Zrepeat Int64.zero 128)) (keypairs_rep W_keypairs KS')).
  entailer!.
Qed.
