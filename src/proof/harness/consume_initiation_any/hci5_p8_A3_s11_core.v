(* law consume_initiation_any, phase P8, segment A3, statement s11 (helper file of
   hci5_p8_A3_s11.v; port of v1's hci5_p8_A3_s11_core.v): the CHECK cut into its 10 blocks (the 9 `&&`
   conditionals and the final if), one semax lemma per block over a small state (the fields the CHECK reads, the
   same values on the handshake side h and the snapshot side s, and a frame F), and their assembly
   hci5_p8_A3_s11_core. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_defs.
Require WgNoise.harness.x_consume_initiation_any.code.
#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The statement, cut into its blocks                                      *)
(* ---------------------------------------------------------------------- *)

Ltac hci5_p8_A3_s11_get k :=
  let x := eval cbv delta [hci5_p8_A3_s11] in hci5_p8_A3_s11 in
  match x with
  | Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence ?b1 ?i2) ?i3) ?i4) ?i5) ?i6) ?i7) ?i8) ?i9) ?last) Sbreak =>
    let r := match k with 1 => b1 | 2 => i2 | 3 => i3 | 4 => i4 | 5 => i5 | 6 => i6 | 7 => i7 | 8 => i8
                        | 9 => i9 | 10 => last end in exact r
  end.

Definition hci5_p8_A3_s11_b1 : statement := ltac:(hci5_p8_A3_s11_get 1).
Definition hci5_p8_A3_s11_b2 : statement := ltac:(hci5_p8_A3_s11_get 2).
Definition hci5_p8_A3_s11_b3 : statement := ltac:(hci5_p8_A3_s11_get 3).
Definition hci5_p8_A3_s11_b4 : statement := ltac:(hci5_p8_A3_s11_get 4).
Definition hci5_p8_A3_s11_b5 : statement := ltac:(hci5_p8_A3_s11_get 5).
Definition hci5_p8_A3_s11_b6 : statement := ltac:(hci5_p8_A3_s11_get 6).
Definition hci5_p8_A3_s11_b7 : statement := ltac:(hci5_p8_A3_s11_get 7).
Definition hci5_p8_A3_s11_b8 : statement := ltac:(hci5_p8_A3_s11_get 8).
Definition hci5_p8_A3_s11_b9 : statement := ltac:(hci5_p8_A3_s11_get 9).
Definition hci5_p8_A3_s11_b10 : statement := ltac:(hci5_p8_A3_s11_get 10).

Lemma hci5_p8_A3_s11_eq : hci5_p8_A3_s11 =
  Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence hci5_p8_A3_s11_b1 hci5_p8_A3_s11_b2) hci5_p8_A3_s11_b3) hci5_p8_A3_s11_b4)
      hci5_p8_A3_s11_b5) hci5_p8_A3_s11_b6) hci5_p8_A3_s11_b7) hci5_p8_A3_s11_b8) hci5_p8_A3_s11_b9)
      hci5_p8_A3_s11_b10) Sbreak.
Proof. reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* ---------------------------------------------------------------------- *)
(* The block lemmas                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hci5_p8_A3_s11_eqp t1 t2 x : is_pointer_or_null x ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t1) (tptr t2) x x)) = Vint Int.one.
Proof.
  intros Hx. destruct x; try contradiction; simpl in Hx;
    unfold eval_binop, sem_binary_operation', sem_cmp, sem_cmp_pp; simpl; rewrite !andb_false_r; simpl.
  - subst. reflexivity.
  - destruct (eq_block b b); [| congruence]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hci5_p8_A3_s11_eqb_refl A : bytes_eqb A A = true.
Proof.
  unfold bytes_eqb. destruct (list_eq_dec _ _ _) as [|n]; [reflexivity | congruence].
Qed.

Section Core.
Variables (gv: globals) (L: hci5_loc) (kv m nw r tg hv sv: val) (pe nxt: val) (hb: bool)
  (ty ix: int) (sid: val) (eph rs ss psk: list byte) (F: mpred).

Definition hci5_p8_A3_s11_S : list mpred :=
  [@field_at W Ews t_hs (DOT HC._entry) (pe, (nxt, (Val.of_bool hb, (Vint ty, Vint ix)))) hv;
   @field_at W Ews t_hs (DOT HC._static_identity) sid hv;
   hbytes Ews eph (@field_address W t_hs (DOT HC._ephemeral_private) hv);
   hbytes Ews rs (@field_address W t_hs (DOT HC._remote_static) hv);
   hbytes Ews ss (@field_address W t_hs (DOT HC._precomputed_static_static) hv);
   hbytes Ews psk (@field_address W t_hs (DOT HC._preshared_key) hv);
   @field_at W Ews t_hsnap (DOT HC._peer) pe sv;
   @field_at W Ews t_hsnap (DOT HC._next) nxt sv;
   @field_at W Ews t_hsnap (DOT HC._hashed) (Val.of_bool hb) sv;
   @field_at W Ews t_hsnap (DOT HC._type) (Vint ty) sv;
   @field_at W Ews t_hsnap (DOT HC._index) (Vint ix) sv;
   @field_at W Ews t_hsnap (DOT HC._static_identity) sid sv;
   hbytes Ews eph (@field_address W t_hsnap (DOT HC._ephemeral_private) sv);
   hbytes Ews rs (@field_address W t_hsnap (DOT HC._remote_static) sv);
   hbytes Ews ss (@field_address W t_hsnap (DOT HC._precomputed_static_static) sv);
   hbytes Ews psk (@field_address W t_hsnap (DOT HC._preshared_key) sv);
   F].

Definition hci5_p8_A3_s11_st (tk: list localdef) : environ -> mpred :=
  PROPx [] (LOCALx (tk ++ [temp HC._kes kv; temp HC._msg m; temp HC._now nw; temp HC._ret r; temp HC._target tg;
                           temp HC._h hv; temp HC._s sv] ++ hci5_lvars gv L)
           (SEPx hci5_p8_A3_s11_S)).

Definition hci5_p8_A3_s11_hyps : Prop :=
  is_pointer_or_null pe /\ is_pointer_or_null nxt /\ is_pointer_or_null sid /\
  @field_compatible W t_hs [] hv /\ @field_compatible W t_hsnap [] sv /\
  Zlength eph = 32 /\ Zlength rs = 32 /\ Zlength ss = 32 /\ Zlength psk = 32 /\
  (forall x, In x [pe; nxt; sid] -> fold_right_sepcon hci5_p8_A3_s11_S |-- valid_pointer x).

Ltac hci5_p8_A3_s11_start s :=
  unfold hci5_Delta; simplify_func_tycontext;
  unfold hci5_p8_A3_s11_st, hci5_p8_A3_s11_S, hci5_lvars; cbn [app];
  unfold s; abbreviate_semax.

Lemma hci5_p8_A3_s11_p1 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [])
    hci5_p8_A3_s11_b1 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'47 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b1.
  forward. forward. forward_if.
  { apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV pe); simpl; auto]);
      unfold hci5_p8_A3_s11_S; simpl fold_right_sepcon; cancel. }
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV nxt); simpl; auto]);
        unfold hci5_p8_A3_s11_S; simpl fold_right_sepcon; cancel. }
    rewrite hci5_p8_A3_s11_eqp by exact Hnx. entailer!. }
  { contradiction. }
Qed.

Lemma hci5_p8_A3_s11_p2 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'47 (Vint Int.one)])
    hci5_p8_A3_s11_b2 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'48 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b2.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  assert (TB: tc_val tbool (Val.of_bool hb)) by (destruct hb; hnf; auto).
  forward. forward. forward.
  replace (force_val (sem_cast tint tbool (eval_binop Oeq tbool tbool (Val.of_bool hb) (Val.of_bool hb))))
    with (Vint Int.one) by (destruct hb; reflexivity).
  entailer!.
Qed.

Lemma hci5_p8_A3_s11_p3 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'48 (Vint Int.one)])
    hci5_p8_A3_s11_b3 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'49 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b3.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hci5_p8_A3_s11_p4 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'49 (Vint Int.one)])
    hci5_p8_A3_s11_b4 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'50 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b4.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hci5_p8_A3_s11_p5 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'50 (Vint Int.one)])
    hci5_p8_A3_s11_b5 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'51 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b5.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV sid); simpl; auto]);
      unfold hci5_p8_A3_s11_S; simpl fold_right_sepcon; cancel. }
  rewrite hci5_p8_A3_s11_eqp by exact Hsd. entailer!.
Qed.

Lemma hci5_p8_A3_s11_p6 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'51 (Vint Int.one)])
    hci5_p8_A3_s11_b6 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'52 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b6.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HC._ephemeral_private) hv, eph,
                Ews, field_address t_hsnap (DOT HC._ephemeral_private) sv, eph).
  { entailer!. simpl. rewrite Le. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hci5_p8_A3_s11_eqb_refl.
  forward. entailer!.
Qed.

Lemma hci5_p8_A3_s11_p7 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'52 (Vint Int.one)])
    hci5_p8_A3_s11_b7 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'54 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b7.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HC._remote_static) hv, rs,
                Ews, field_address t_hsnap (DOT HC._remote_static) sv, rs).
  { entailer!. simpl. rewrite Lr. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hci5_p8_A3_s11_eqb_refl.
  forward. entailer!.
Qed.

Lemma hci5_p8_A3_s11_p8 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'54 (Vint Int.one)])
    hci5_p8_A3_s11_b8 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'56 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b8.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HC._precomputed_static_static) hv, ss,
                Ews, field_address t_hsnap (DOT HC._precomputed_static_static) sv, ss).
  { entailer!. simpl. rewrite Ls. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hci5_p8_A3_s11_eqb_refl.
  forward. entailer!.
Qed.

Lemma hci5_p8_A3_s11_p9 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'56 (Vint Int.one)])
    hci5_p8_A3_s11_b9 (normal_ret_assert (hci5_p8_A3_s11_st [temp HC._t'58 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b9.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HC._preshared_key) hv, psk,
                Ews, field_address t_hsnap (DOT HC._preshared_key) sv, psk).
  { entailer!. simpl. rewrite Lp. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hci5_p8_A3_s11_eqb_refl.
  forward. entailer!.
Qed.

Lemma hci5_p8_A3_s11_p10 {Espec: OracleKind} : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st [temp HC._t'58 (Vint Int.one)])
    hci5_p8_A3_s11_b10 (normal_ret_assert (hci5_p8_A3_s11_st [])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & HV).
  hci5_p8_A3_s11_start hci5_p8_A3_s11_b10.
  forward_if.
  { exfalso; exact (Int.one_not_zero H). }
  forward. entailer!.
Qed.

Lemma hci5_p8_A3_s11_core {Espec: OracleKind} (Rr: ret_assert) : hci5_p8_A3_s11_hyps ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_A3_s11_st []) hci5_p8_A3_s11
    (overridePost (hci5_p8_A3_s11_st []) Rr).
Proof.
  intros Hh. rewrite hci5_p8_A3_s11_eq. destruct Rr as [r1 r2 r3 r4].
  apply semax_loop with (Q' := hci5_p8_A3_s11_st []).
  - eapply semax_post; [ | | | | ].
    5: { eapply semax_seq'; [| exact (hci5_p8_A3_s11_p10 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p9 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p8 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p7 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p6 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p5 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p4 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p3 Hh)].
         eapply semax_seq'; [| exact (hci5_p8_A3_s11_p2 Hh)].
         exact (hci5_p8_A3_s11_p1 Hh). }
    all: intros; cbn [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert];
         apply andp_left2; first [apply derives_refl | apply FF_left].
  - eapply semax_pre; [| apply semax_break].
    cbn [RA_break overridePost loop2_ret_assert]. apply andp_left2, derives_refl.
Qed.

End Core.
End Seg.
