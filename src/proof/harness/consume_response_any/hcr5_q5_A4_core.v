(* law consume_response_any, phase Q5, segment A4 (helper file of hcr5_q5_A4.v: the CHECK cut into its 12 blocks, one lemma per block over a small state, and their assembly hcr5_q5_A4_core).  Segment A4: ACC 9: CHECK(h->entry.peer == s->peer && h->entry.next == s->next && h->entry.hashed == s->hashed && h->entry.type == s->type && h->entry.index == s->index && h->static_identity == s->static_identity && bytes_eq(ephemeral_private) && bytes_eq(remote_static) && bytes_eq(precomputed_static_static) && bytes_eq(preshared_key) && bytes_eq(latest_timestamp, 12) && h->last_initiation_consumption == s->last_initiation_consumption).
   States and statements: hcr5_q5_defs.v; pure facts: hcr5_q5_pure.v (its statement is a hypothesis
   here, proved separately); (section Q5). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The statement, cut into its blocks                                      *)
(* ---------------------------------------------------------------------- *)

Ltac hcr5_q5_A4_get k :=
  let x := eval cbv delta [hcr5_q5_A4] in hcr5_q5_A4 in
  match x with
  | Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence (Ssequence (Ssequence ?b1 ?i2) ?i3) ?i4) ?i5) ?i6) ?i7) ?i8) ?i9) ?i10) ?i11) ?last) Sbreak =>
    let r := match k with 1 => b1 | 2 => i2 | 3 => i3 | 4 => i4 | 5 => i5 | 6 => i6 | 7 => i7 | 8 => i8
                        | 9 => i9 | 10 => i10 | 11 => i11 | 12 => last end in exact r
  end.

Definition hcr5_q5_A4_s1 : statement := ltac:(hcr5_q5_A4_get 1).
Definition hcr5_q5_A4_s2 : statement := ltac:(hcr5_q5_A4_get 2).
Definition hcr5_q5_A4_s3 : statement := ltac:(hcr5_q5_A4_get 3).
Definition hcr5_q5_A4_s4 : statement := ltac:(hcr5_q5_A4_get 4).
Definition hcr5_q5_A4_s5 : statement := ltac:(hcr5_q5_A4_get 5).
Definition hcr5_q5_A4_s6 : statement := ltac:(hcr5_q5_A4_get 6).
Definition hcr5_q5_A4_s7 : statement := ltac:(hcr5_q5_A4_get 7).
Definition hcr5_q5_A4_s8 : statement := ltac:(hcr5_q5_A4_get 8).
Definition hcr5_q5_A4_s9 : statement := ltac:(hcr5_q5_A4_get 9).
Definition hcr5_q5_A4_s10 : statement := ltac:(hcr5_q5_A4_get 10).
Definition hcr5_q5_A4_s11 : statement := ltac:(hcr5_q5_A4_get 11).
Definition hcr5_q5_A4_s12 : statement := ltac:(hcr5_q5_A4_get 12).

Lemma hcr5_q5_A4_eq : hcr5_q5_A4 =
  Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence (Ssequence (Ssequence hcr5_q5_A4_s1 hcr5_q5_A4_s2) hcr5_q5_A4_s3) hcr5_q5_A4_s4)
      hcr5_q5_A4_s5) hcr5_q5_A4_s6) hcr5_q5_A4_s7) hcr5_q5_A4_s8) hcr5_q5_A4_s9) hcr5_q5_A4_s10)
      hcr5_q5_A4_s11) hcr5_q5_A4_s12) Sbreak.
Proof. reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* ---------------------------------------------------------------------- *)
(* The block lemmas, over a small state: the fields the CHECK reads, the   *)
(* same values on both sides (handshake h, snapshot s), and a frame F      *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_q5_A4_eqp t1 t2 x : is_pointer_or_null x ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t1) (tptr t2) x x)) = Vint Int.one.
Proof.
  intros Hx. destruct x; try contradiction; simpl in Hx;
    unfold eval_binop, sem_binary_operation', sem_cmp, sem_cmp_pp; simpl; rewrite !andb_false_r; simpl.
  - subst. reflexivity.
  - destruct (eq_block b b); [| congruence]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hcr5_q5_A4_eqb_refl A : bytes_eqb A A = true.
Proof.
  unfold bytes_eqb. destruct (list_eq_dec _ _ _) as [|n]; [reflexivity | congruence].
Qed.

Section Core.
Variables (gv: globals) (L: hcr5_loc) (kh m r tg hv sv: val) (she: share) (pe nxt: val) (hb: bool)
  (ty ix: int) (sid: val) (lic: int64) (eph rs ss psk ts: list byte) (F: mpred).

Definition hcr5_q5_A4_S : list mpred :=
  [@field_at W she t_hs (DOT HR5._entry) (pe, (nxt, (Val.of_bool hb, (Vint ty, Vint ix)))) hv;
   @field_at W Ews t_hs (DOT HR5._static_identity) sid hv;
   @field_at W Ews t_hs (DOT HR5._last_initiation_consumption) (Vlong lic) hv;
   hbytes Ews eph (@field_address W t_hs (DOT HR5._ephemeral_private) hv);
   hbytes Ews rs (@field_address W t_hs (DOT HR5._remote_static) hv);
   hbytes Ews ss (@field_address W t_hs (DOT HR5._precomputed_static_static) hv);
   hbytes Ews psk (@field_address W t_hs (DOT HR5._preshared_key) hv);
   hbytes Ews ts (@field_address W t_hs (DOT HR5._latest_timestamp) hv);
   @field_at W Ews t_hsnap (DOT HR5._peer) pe sv;
   @field_at W Ews t_hsnap (DOT HR5._next) nxt sv;
   @field_at W Ews t_hsnap (DOT HR5._hashed) (Val.of_bool hb) sv;
   @field_at W Ews t_hsnap (DOT HR5._type) (Vint ty) sv;
   @field_at W Ews t_hsnap (DOT HR5._index) (Vint ix) sv;
   @field_at W Ews t_hsnap (DOT HR5._static_identity) sid sv;
   @field_at W Ews t_hsnap (DOT HR5._last_initiation_consumption) (Vlong lic) sv;
   hbytes Ews eph (@field_address W t_hsnap (DOT HR5._ephemeral_private) sv);
   hbytes Ews rs (@field_address W t_hsnap (DOT HR5._remote_static) sv);
   hbytes Ews ss (@field_address W t_hsnap (DOT HR5._precomputed_static_static) sv);
   hbytes Ews psk (@field_address W t_hsnap (DOT HR5._preshared_key) sv);
   hbytes Ews ts (@field_address W t_hsnap (DOT HR5._latest_timestamp) sv);
   F].

Definition hcr5_q5_A4_st (tk: list localdef) : environ -> mpred :=
  PROPx [] (LOCALx (tk ++ [temp HR5._kes kh; temp HR5._msg m; temp HR5._ret r; temp HR5._target tg;
                           temp HR5._h__1 hv; temp HR5._s sv] ++ hcr5_lvars gv L)
           (SEPx hcr5_q5_A4_S)).

Definition hcr5_q5_A4_hyps : Prop :=
  readable_share she /\ is_pointer_or_null pe /\ is_pointer_or_null nxt /\ is_pointer_or_null sid /\
  @field_compatible W t_hs [] hv /\ @field_compatible W t_hsnap [] sv /\
  Zlength eph = 32 /\ Zlength rs = 32 /\ Zlength ss = 32 /\ Zlength psk = 32 /\ Zlength ts = 12 /\
  (forall x, In x [pe; nxt; sid] -> fold_right_sepcon hcr5_q5_A4_S |-- valid_pointer x).

Lemma hcr5_q5_A4_p1 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [])
    hcr5_q5_A4_s1 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'38 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  unfold hcr5_Delta. simplify_func_tycontext.
  unfold hcr5_q5_A4_st, hcr5_q5_A4_S, hcr5_lvars; cbn [app].
  unfold hcr5_q5_A4_s1. abbreviate_semax.
  forward. forward. forward_if.
  { apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV pe); simpl; auto]);
      unfold hcr5_q5_A4_S; simpl fold_right_sepcon; cancel. }
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV nxt); simpl; auto]);
        unfold hcr5_q5_A4_S; simpl fold_right_sepcon; cancel. }
    rewrite hcr5_q5_A4_eqp by exact Hnx. entailer!. }
  { contradiction. }
Qed.

Ltac hcr5_q5_A4_start s :=
  unfold hcr5_Delta; simplify_func_tycontext;
  unfold hcr5_q5_A4_st, hcr5_q5_A4_S, hcr5_lvars; cbn [app];
  unfold s; abbreviate_semax.

Lemma hcr5_q5_A4_p2 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'38 (Vint Int.one)])
    hcr5_q5_A4_s2 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'39 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s2.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  assert (TB: tc_val tbool (Val.of_bool hb)) by (destruct hb; hnf; auto).
  forward. forward. forward.
  replace (force_val (sem_cast tint tbool (eval_binop Oeq tbool tbool (Val.of_bool hb) (Val.of_bool hb))))
    with (Vint Int.one) by (destruct hb; reflexivity).
  entailer!.
Qed.

Lemma hcr5_q5_A4_p3 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'39 (Vint Int.one)])
    hcr5_q5_A4_s3 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'40 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s3.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hcr5_q5_A4_p4 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'40 (Vint Int.one)])
    hcr5_q5_A4_s4 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'41 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s4.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hcr5_q5_A4_p5 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'41 (Vint Int.one)])
    hcr5_q5_A4_s5 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'42 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s5.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV sid); simpl; auto]);
      unfold hcr5_q5_A4_S; simpl fold_right_sepcon; cancel. }
  rewrite hcr5_q5_A4_eqp by exact Hsd. entailer!.
Qed.

Lemma hcr5_q5_A4_p6 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'42 (Vint Int.one)])
    hcr5_q5_A4_s6 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'43 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s6.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HR5._ephemeral_private) hv, eph,
                Ews, field_address t_hsnap (DOT HR5._ephemeral_private) sv, eph).
  { entailer!. simpl. rewrite Le. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hcr5_q5_A4_eqb_refl.
  forward. entailer!.
Qed.

Lemma hcr5_q5_A4_p7 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'43 (Vint Int.one)])
    hcr5_q5_A4_s7 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'45 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s7.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HR5._remote_static) hv, rs,
                Ews, field_address t_hsnap (DOT HR5._remote_static) sv, rs).
  { entailer!. simpl. rewrite Lr. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hcr5_q5_A4_eqb_refl.
  forward. entailer!.
Qed.

Lemma hcr5_q5_A4_p8 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'45 (Vint Int.one)])
    hcr5_q5_A4_s8 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'47 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s8.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HR5._precomputed_static_static) hv, ss,
                Ews, field_address t_hsnap (DOT HR5._precomputed_static_static) sv, ss).
  { entailer!. simpl. rewrite Ls. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hcr5_q5_A4_eqb_refl.
  forward. entailer!.
Qed.

Lemma hcr5_q5_A4_p9 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'47 (Vint Int.one)])
    hcr5_q5_A4_s9 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'49 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s9.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HR5._preshared_key) hv, psk,
                Ews, field_address t_hsnap (DOT HR5._preshared_key) sv, psk).
  { entailer!. simpl. rewrite Lp. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hcr5_q5_A4_eqb_refl.
  forward. entailer!.
Qed.

Lemma hcr5_q5_A4_p10 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'49 (Vint Int.one)])
    hcr5_q5_A4_s10 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'51 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s10.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HR5._latest_timestamp) hv, ts,
                Ews, field_address t_hsnap (DOT HR5._latest_timestamp) sv, ts).
  { entailer!. simpl. rewrite Lt. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hcr5_q5_A4_eqb_refl.
  forward. entailer!.
Qed.

Lemma hcr5_q5_A4_p11 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'51 (Vint Int.one)])
    hcr5_q5_A4_s11 (normal_ret_assert (hcr5_q5_A4_st [temp HR5._t'53 (Vint Int.one)])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s11.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int64.eq_true. reflexivity.
Qed.

Lemma hcr5_q5_A4_p12 {Espec: OracleKind} : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st [temp HR5._t'53 (Vint Int.one)])
    hcr5_q5_A4_s12 (normal_ret_assert (hcr5_q5_A4_st [])).
Proof.
  intros (Hsh & Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hcr5_q5_A4_start hcr5_q5_A4_s12.
  forward_if.
  { exfalso; exact (Int.one_not_zero H). }
  forward. entailer!.
Qed.

Lemma hcr5_q5_A4_core {Espec: OracleKind} (Rr: ret_assert) : hcr5_q5_A4_hyps ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_A4_st []) hcr5_q5_A4
    (overridePost (hcr5_q5_A4_st []) Rr).
Proof.
  intros Hh. rewrite hcr5_q5_A4_eq. destruct Rr as [r1 r2 r3 r4].
  apply semax_loop with (Q' := hcr5_q5_A4_st []).
  - eapply semax_post; [ | | | | ].
    5: { eapply semax_seq'; [| exact (hcr5_q5_A4_p12 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p11 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p10 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p9 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p8 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p7 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p6 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p5 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p4 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p3 Hh)].
         eapply semax_seq'; [| exact (hcr5_q5_A4_p2 Hh)].
         exact (hcr5_q5_A4_p1 Hh). }
    all: intros; cbn [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert];
         apply andp_left2; first [apply derives_refl | apply FF_left].
  - eapply semax_pre; [| apply semax_break].
    cbn [RA_break overridePost loop2_ret_assert]. apply andp_left2, derives_refl.
Qed.

End Core.

End Seg.
