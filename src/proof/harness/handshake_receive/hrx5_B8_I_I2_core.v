(* law handshake_receive, phase B8 branch I, segment I2: the CHECK
   of I2 cut into its 10 blocks (the 9 `&&` conditionals and the final if), one semax lemma per block over a small
   state (the sixteen fields the CHECK reads and a frame F), and their assembly hrx5_B8I_I2_core.  Port of
   consume_initiation_any's hci5_p8_A3_s11_core.v. *)
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The statement, cut into its blocks                                      *)
(* ---------------------------------------------------------------------- *)

Ltac hrx5_B8I_I2_get k :=
  let x := eval cbv delta [hrx5_B8I_I2] in hrx5_B8I_I2 in
  match x with
  | Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence ?b1 ?i2) ?i3) ?i4) ?i5) ?i6) ?i7) ?i8) ?i9) ?last) Sbreak =>
    let r := match k with 1 => b1 | 2 => i2 | 3 => i3 | 4 => i4 | 5 => i5 | 6 => i6 | 7 => i7 | 8 => i8
                        | 9 => i9 | 10 => last end in exact r
  end.

Definition hrx5_B8I_I2_b1 : statement := ltac:(hrx5_B8I_I2_get 1).
Definition hrx5_B8I_I2_b2 : statement := ltac:(hrx5_B8I_I2_get 2).
Definition hrx5_B8I_I2_b3 : statement := ltac:(hrx5_B8I_I2_get 3).
Definition hrx5_B8I_I2_b4 : statement := ltac:(hrx5_B8I_I2_get 4).
Definition hrx5_B8I_I2_b5 : statement := ltac:(hrx5_B8I_I2_get 5).
Definition hrx5_B8I_I2_b6 : statement := ltac:(hrx5_B8I_I2_get 6).
Definition hrx5_B8I_I2_b7 : statement := ltac:(hrx5_B8I_I2_get 7).
Definition hrx5_B8I_I2_b8 : statement := ltac:(hrx5_B8I_I2_get 8).
Definition hrx5_B8I_I2_b9 : statement := ltac:(hrx5_B8I_I2_get 9).
Definition hrx5_B8I_I2_b10 : statement := ltac:(hrx5_B8I_I2_get 10).

Lemma hrx5_B8I_I2_eq : hrx5_B8I_I2 =
  Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence hrx5_B8I_I2_b1 hrx5_B8I_I2_b2) hrx5_B8I_I2_b3) hrx5_B8I_I2_b4)
      hrx5_B8I_I2_b5) hrx5_B8I_I2_b6) hrx5_B8I_I2_b7) hrx5_B8I_I2_b8) hrx5_B8I_I2_b9)
      hrx5_B8I_I2_b10) Sbreak.
Proof. reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* ---------------------------------------------------------------------- *)
(* The block lemmas                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_I2_eqp t1 t2 x : is_pointer_or_null x ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t1) (tptr t2) x x)) = Vint Int.one.
Proof.
  intros Hx. destruct x; try contradiction; simpl in Hx;
    unfold eval_binop, sem_binary_operation', sem_cmp, sem_cmp_pp; simpl; rewrite !andb_false_r; simpl.
  - subst. reflexivity.
  - destruct (eq_block b b); [| congruence]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hrx5_B8I_I2_eqb_refl A : bytes_eqb A A = true.
Proof.
  unfold bytes_eqb. destruct (list_eq_dec _ _ _) as [|n]; [reflexivity | congruence].
Qed.

Section Core.
Variables (gv: globals) (L: hrx5_loc) (NS: list hnode4) (nk: val) (KE: list kent4) (st i: Z) (S: shim)
  (lul1: int64) (dp img: val) (M: init_msg) (T: tstate) (a: val) (hv sv: val) (pe nxt: val) (hb: bool)
  (ty ix: int) (sid: val) (eph rs ss psk: list byte) (F: mpred).

Definition hrx5_B8I_I2_S : list mpred :=
  [@field_at W Ews t_hs (DOT HM._entry) (pe, (nxt, (Val.of_bool hb, (Vint ty, Vint ix)))) hv;
   @field_at W Ews t_hs (DOT HM._static_identity) sid hv;
   hbytes Ews eph (@field_address W t_hs (DOT HM._ephemeral_private) hv);
   hbytes Ews rs (@field_address W t_hs (DOT HM._remote_static) hv);
   hbytes Ews ss (@field_address W t_hs (DOT HM._precomputed_static_static) hv);
   hbytes Ews psk (@field_address W t_hs (DOT HM._preshared_key) hv);
   @field_at W Ews t_hsnap (DOT HM._peer) pe sv;
   @field_at W Ews t_hsnap (DOT HM._next) nxt sv;
   @field_at W Ews t_hsnap (DOT HM._hashed) (Val.of_bool hb) sv;
   @field_at W Ews t_hsnap (DOT HM._type) (Vint ty) sv;
   @field_at W Ews t_hsnap (DOT HM._index) (Vint ix) sv;
   @field_at W Ews t_hsnap (DOT HM._static_identity) sid sv;
   hbytes Ews eph (@field_address W t_hsnap (DOT HM._ephemeral_private) sv);
   hbytes Ews rs (@field_address W t_hsnap (DOT HM._remote_static) sv);
   hbytes Ews ss (@field_address W t_hsnap (DOT HM._precomputed_static_static) sv);
   hbytes Ews psk (@field_address W t_hsnap (DOT HM._preshared_key) sv);
   F].

Definition hrx5_B8I_I2_st (tk: list localdef) : environ -> mpred :=
  PROPx [] (LOCALx (tk ++ [temp HM._h__1 hv; temp HM._s sv] ++
                           hrx5_B8I_temps NS nk KE st i S lul1 dp img M T a ++ hrx5_lvars gv L)
           (SEPx hrx5_B8I_I2_S)).

Definition hrx5_B8I_I2_hyps : Prop :=
  is_pointer_or_null pe /\ is_pointer_or_null nxt /\ is_pointer_or_null sid /\
  @field_compatible W t_hs [] hv /\ @field_compatible W t_hsnap [] sv /\
  Zlength eph = 32 /\ Zlength rs = 32 /\ Zlength ss = 32 /\ Zlength psk = 32 /\
  (forall x, In x [pe; nxt; sid] -> fold_right_sepcon hrx5_B8I_I2_S |-- valid_pointer x).

Ltac hrx5_B8I_I2_start s :=
  unfold hrx5_Delta; simplify_func_tycontext;
  unfold hrx5_B8I_I2_st, hrx5_B8I_I2_S, hrx5_B8I_temps, hrx5_lvars; cbn [app];
  unfold s; abbreviate_semax.

Lemma hrx5_B8I_I2_p1 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [])
    hrx5_B8I_I2_b1 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'125 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b1.
  forward. forward. forward_if.
  { apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV pe); simpl; auto]);
      unfold hrx5_B8I_I2_S; simpl fold_right_sepcon; cancel. }
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV nxt); simpl; auto]);
        unfold hrx5_B8I_I2_S; simpl fold_right_sepcon; cancel. }
    rewrite hrx5_B8I_I2_eqp by exact Hnx. entailer!. }
  { contradiction. }
Qed.

Lemma hrx5_B8I_I2_p2 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'125 (Vint Int.one)])
    hrx5_B8I_I2_b2 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'126 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b2.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  assert (TB: tc_val tbool (Val.of_bool hb)) by (destruct hb; hnf; auto).
  forward. forward. forward.
  replace (force_val (sem_cast tint tbool (eval_binop Oeq tbool tbool (Val.of_bool hb) (Val.of_bool hb))))
    with (Vint Int.one) by (destruct hb; reflexivity).
  entailer!.
Qed.

Lemma hrx5_B8I_I2_p3 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'126 (Vint Int.one)])
    hrx5_B8I_I2_b3 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'127 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b3.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hrx5_B8I_I2_p4 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'127 (Vint Int.one)])
    hrx5_B8I_I2_b4 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'128 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b4.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hrx5_B8I_I2_p5 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'128 (Vint Int.one)])
    hrx5_B8I_I2_b5 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'129 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b5.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV sid); simpl; auto]);
      unfold hrx5_B8I_I2_S; simpl fold_right_sepcon; cancel. }
  rewrite hrx5_B8I_I2_eqp by exact Hsd. entailer!.
Qed.

Lemma hrx5_B8I_I2_p6 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'129 (Vint Int.one)])
    hrx5_B8I_I2_b6 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'130 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b6.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._ephemeral_private) hv, eph,
                Ews, field_address t_hsnap (DOT HM._ephemeral_private) sv, eph).
  { entailer!. simpl. rewrite Le. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8I_I2_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8I_I2_p7 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'130 (Vint Int.one)])
    hrx5_B8I_I2_b7 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'132 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b7.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._remote_static) hv, rs,
                Ews, field_address t_hsnap (DOT HM._remote_static) sv, rs).
  { entailer!. simpl. rewrite Lr. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8I_I2_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8I_I2_p8 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'132 (Vint Int.one)])
    hrx5_B8I_I2_b8 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'134 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b8.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._precomputed_static_static) hv, ss,
                Ews, field_address t_hsnap (DOT HM._precomputed_static_static) sv, ss).
  { entailer!. simpl. rewrite Ls. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8I_I2_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8I_I2_p9 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'134 (Vint Int.one)])
    hrx5_B8I_I2_b9 (normal_ret_assert (hrx5_B8I_I2_st [temp HM._t'136 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b9.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._preshared_key) hv, psk,
                Ews, field_address t_hsnap (DOT HM._preshared_key) sv, psk).
  { entailer!. simpl. rewrite Lp. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8I_I2_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8I_I2_p10 {Espec: OracleKind} : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st [temp HM._t'136 (Vint Int.one)])
    hrx5_B8I_I2_b10 (normal_ret_assert (hrx5_B8I_I2_st [])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hrx5_B8I_I2_start hrx5_B8I_I2_b10.
  forward_if.
  { exfalso; exact (Int.one_not_zero H). }
  forward. entailer!.
Qed.

Lemma hrx5_B8I_I2_core {Espec: OracleKind} (Rr: ret_assert) : hrx5_B8I_I2_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8I_I2_st []) hrx5_B8I_I2
    (overridePost (hrx5_B8I_I2_st []) Rr).
Proof.
  intros Hh. rewrite hrx5_B8I_I2_eq. destruct Rr as [r1 r2 r3 r4].
  apply semax_loop with (Q' := hrx5_B8I_I2_st []).
  - eapply semax_post; [ | | | | ].
    5: { eapply semax_seq'; [| exact (hrx5_B8I_I2_p10 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p9 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p8 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p7 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p6 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p5 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p4 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p3 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8I_I2_p2 Hh)].
         exact (hrx5_B8I_I2_p1 Hh). }
    all: intros; cbn [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert];
         apply andp_left2; first [apply derives_refl | apply FF_left].
  - eapply semax_pre; [| apply semax_break].
    cbn [RA_break overridePost loop2_ret_assert]. apply andp_left2, derives_refl.
Qed.

End Core.
End Seg.
