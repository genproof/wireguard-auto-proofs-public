(* law replay: main's segment B (statements 15..22: the three mallocs, the NULL test with its frees and
   return 0 (the locals back to data_at_: hrp3_close), latest = 0, last = 0, now = draw_boottime(),
   steps = draw_steps()).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

#[local] Instance hrp3_segB_CCE1 : change_composite_env HCS W_replay.
Proof. make_cs_preserve HCS W_replay. Defined.
#[local] Instance hrp3_segB_CCE2 : change_composite_env W_replay Noise.CS.
Proof. make_cs_preserve W_replay Noise.CS. Defined.

Lemma hrp3_segB_mid (v: reptype t_mident) (p: val) :
  @data_at HCS Tsh t_mident v p |-- @data_at_ W_replay Tsh (Tstruct RC._m_identity noattr) p.
Proof.
  sep_apply (@data_at_data_at_ HCS). rewrite (@data_at__change_composite HCS W_replay _ Tsh t_mident) by reflexivity.
  apply derives_refl.
Qed.

Lemma hrp3_segB_mcinit (p: val) :
  @data_at_ HCS Tsh t_mcinit p |-- @data_at_ W_replay Tsh (Tstruct RC._m_consumed_initiation noattr) p.
Proof.
  rewrite (@data_at__change_composite HCS W_replay _ Tsh t_mcinit) by reflexivity. apply derives_refl.
Qed.

Lemma hrp3_segB_hsnap (p: val) :
  @data_at_ HCS Tsh t_hsnap p |-- @data_at_ W_replay Tsh (Tstruct RC._hs_snap noattr) p.
Proof.
  rewrite (@data_at__change_composite HCS W_replay _ Tsh t_hsnap) by reflexivity. apply derives_refl.
Qed.

Lemma hrp3_segB_hbytes (bs: list byte) (n: Z) (p: val) :
  Zlength bs = n ->
  hbytes Tsh bs p |-- @data_at_ W_replay Tsh (tarray tuchar n) p.
Proof.
  intros <-. unfold hbytes. sep_apply (@data_at_data_at_ HCS).
  rewrite (@data_at__change_composite HCS W_replay _ Tsh (tarray tuchar (Zlength bs))) by reflexivity.
  apply derives_refl.
Qed.

Lemma hrp3_segB_hout (n: Z) (p: val) :
  hout Tsh n p |-- @data_at_ W_replay Tsh (tarray tuchar n) p.
Proof.
  unfold hout. rewrite (@data_at__change_composite HCS W_replay _ Tsh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma hrp3_segB_minit (p: val) :
  @data_at_ W_replay Ews t_init p = @data_at_ Noise.CS Ews t_init p.
Proof.
  rewrite (@data_at__change_composite W_replay Noise.CS _ Ews t_init) by reflexivity. reflexivity.
Qed.

Definition hrp3_segB_M0 : init_msg := mkIM Int.zero Int.zero [] [] [] [] [].

Lemma hrp3_segB_mbuf (p: val) :
  (@malloc_token W_replay Ews t_init p * @data_at_ W_replay Ews t_init p)%logic |-- hrp3_mbuf false hrp3_segB_M0 p.
Proof. unfold hrp3_mbuf. rewrite hrp3_segB_minit. apply derives_refl. Qed.

Lemma hrp3_segB_inv x25519 aead_dec (F: hrp3_fix) (V: hrp3_val) (S: shim) (now: int64) :
  Int64.unsigned now < 2 ^ 62 ->
  hrp3_inv x25519 aead_dec F V
    (mkRDyn S (hrp3_TB0 (f_pb F)) (hrp3_PB0 x25519 F V) (hrp3_PA0 x25519 F V) (zeros 12) (Int64.repr 0) now
            false hrp3_segB_M0 false hrp3_segB_M0).
Proof.
  intros Hnow. unfold hrp3_inv; cbn [y_TA y_PB y_PA y_latest y_last y_now y_ha y_Ma].
  split; [eexists; split; reflexivity |].
  split; [reflexivity |]. split; [reflexivity |].
  split.
  { exists HS_ZEROED, zeros32, zeros32, zeros32, Int.zero. reflexivity. }
  split; [reflexivity |]. split; [rewrite Int64.unsigned_repr by rep_lia; lia |].
  split; [exact Hnow | discriminate].
Qed.

Lemma hrp3_segB_tc (p: val) (R: mpred) :
  ((if eq_dec p nullval then emp else (@malloc_token W_replay Ews t_init p * @data_at_ W_replay Ews t_init p)) * R)%logic
  |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  destruct (eq_dec p nullval) as [->|Hp].
  - simpl. unfold nullval. simpl. entailer!.
  - entailer!.
Qed.

Ltac hrp3_ptr_ne p :=
  match goal with Hf: field_compatible _ [] p |- _ => apply field_compatible_isptr in Hf end;
  destruct p; try contradiction; reflexivity.

Ltac hrp3_fixH :=
  repeat match goal with H: context [EqDec_val ?a ?b] |- _ => change (EqDec_val a b) with (eq_dec a b) in H end.

Lemma hrp3_segB_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec) (hrp3_PA x25519 F FR) hrp3_segB
    (overridePost (hrp3_PB x25519 aead_dec F FR) (hrp3_R (f_gv F))).
Proof.
  intros HH Hx Ha. unfold hrp3_PA, hrp3_Delta, hrp3_R. apply hrp3_post_canon. abbreviate_semax.
  Intros V S.
  unfold hrp3_globs, hrp3_lvars; cbn [app].
  unfold hrp3_segB.
  forward_call (t_init, f_gv F). Intros sp.
  forward_call (t_init, f_gv F). Intros ap.
  forward_call (t_init, f_gv F). Intros mp.
  freeze [4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25] FR1.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'8 (Vint (if eq_dec sp nullval then Int.one else
                                                      if eq_dec ap nullval then Int.one else Int.zero)) :: Q)
                (SEPx R))) end.
  { eapply derives_trans; [| apply (hrp3_segB_tc sp TT)]. cancel. }
  { forward. destruct (eq_dec sp nullval); [|congruence]. apply ENTAIL_refl. }
  { forward.
    - entailer!. eapply derives_trans; [| apply (hrp3_segB_tc ap TT)]. cancel.
    - destruct (eq_dec sp nullval); [congruence|]. destruct (eq_dec ap nullval).
      + subst ap. entailer!.
      + entailer!. hrp3_ptr_ne ap. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp RC._t'9 (Vint (if eq_dec sp nullval then Int.one else
                                                      if eq_dec ap nullval then Int.one else
                                                      if eq_dec mp nullval then Int.one else Int.zero)) :: Q)
                (SEPx R))) end.
  { forward. destruct (eq_dec sp nullval); [apply ENTAIL_refl|].
    destruct (eq_dec ap nullval); [apply ENTAIL_refl|].
    match goal with Hn: _ <> Int.zero |- _ => exfalso; apply Hn; rewrite !if_false by auto; reflexivity end. }
  { forward.
    - entailer!. eapply derives_trans; [| apply (hrp3_segB_tc mp TT)]. cancel.
    - hrp3_fixH. destruct (eq_dec sp nullval); [discriminate|]. destruct (eq_dec ap nullval); [discriminate|].
      destruct (eq_dec mp nullval).
      + subst mp. entailer!.
      + entailer!. hrp3_ptr_ne mp. }
  thaw FR1.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((sp <> nullval) :: (ap <> nullval) :: (mp <> nullval) :: P) (LOCALx Q (SEPx R))) end.
  { forward_call (t_init, sp, f_gv F).
    forward_call (t_init, ap, f_gv F).
    forward_call (t_init, mp, f_gv F).
    forward.
    destruct HH as (_ & _ & Hc).
    assert (Hta: hrp3_ta_ok (f_pb F) (hrp3_TB0 (f_pb F))) by (eexists; split; reflexivity).
    destruct H as (Hra & Hrb & Hps & _ & _ & _).
    assert (Hss: Zlength (hrp3_SS x25519 V) = 32).
    { unfold hrp3_SS, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
    sep_apply (Hc F (hrp3_DA x25519 F V) (hrp3_DB x25519 F V) (hrp3_TB0 (f_pb F)) (hrp3_PB0 x25519 F V)
                  (hrp3_PA0 x25519 F V) Hta).
    sep_apply (hrp3_segB_mid (mident_val (hrp3_IA x25519 V)) (f_ia F)).
    sep_apply (hrp3_segB_mid (mident_val (hrp3_IB x25519 V)) (f_ib F)).
    sep_apply (hrp3_segB_hbytes (v_RAWA V) 32 (f_rawa F) Hra).
    sep_apply (hrp3_segB_hbytes (v_RAWB V) 32 (f_rawb F) Hrb).
    sep_apply (hrp3_segB_hbytes (v_PSK V) 32 (f_psk F) Hps).
    sep_apply (hrp3_segB_hbytes (hrp3_SS x25519 V) 32 (f_ssb F) Hss).
    sep_apply (hrp3_segB_hout 12 (f_latest F)).
    sep_apply (hrp3_segB_mcinit (f_ci F)).
    sep_apply (hrp3_segB_hsnap (f_snap F)).
    cancel. }
  { forward. hrp3_fixH.
    destruct (eq_dec sp nullval); [discriminate|]. destruct (eq_dec ap nullval); [discriminate|].
    destruct (eq_dec mp nullval); [discriminate|]. entailer!. }
  Intros. destruct (eq_dec sp nullval); [contradiction|]. destruct (eq_dec ap nullval); [contradiction|].
  destruct (eq_dec mp nullval); [contradiction|].
  sep_apply (hrp3_segB_mbuf sp). sep_apply (hrp3_segB_mbuf ap). sep_apply (hrp3_segB_mbuf mp).
  forward_call (Tsh, f_latest F, Byte.zero, 12).
  forward.
  forward_call tt. Intros now.
  forward_call tt. Intros steps.
  change (Int.signed (Int.repr 0)) with 0. change (Zrepeat Byte.zero 12) with (zeros 12).
  forward.
  assert (Hinv := hrp3_segB_inv x25519 aead_dec F V S now (proj2 H3)).
  Exists V (mkRDyn S (hrp3_TB0 (f_pb F)) (hrp3_PB0 x25519 F V) (hrp3_PA0 x25519 F V) (zeros 12) (Int64.repr 0) now
                   false hrp3_segB_M0 false hrp3_segB_M0) sp ap mp steps.
  unfold hrp3_world, hrp3_globs, hrp3_temps, hrp3_lvars;
    cbn [app y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma].
  entailer!.
Qed.
