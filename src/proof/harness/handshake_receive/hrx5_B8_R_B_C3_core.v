(* law handshake_receive, B8 R B part C3: the CHECK of C3 cut into its 12
   blocks over a small state (the fields the CHECK reads and a frame F).  Port of hrx5_B8_I_I2_core.v with
   the latest_timestamp / last_initiation_consumption blocks added. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope Z_scope.

Ltac hrx5_B8RBC3_get k :=
  let x := eval cbv delta [hrx5_B8RB_C3] in hrx5_B8RB_C3 in
  match x with
  | Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence (Ssequence (Ssequence ?b1 ?i2) ?i3) ?i4) ?i5) ?i6) ?i7) ?i8) ?i9) ?i10) ?i11) ?last) Sbreak =>
    let r := match k with 1 => b1 | 2 => i2 | 3 => i3 | 4 => i4 | 5 => i5 | 6 => i6 | 7 => i7 | 8 => i8
                        | 9 => i9 | 10 => i10 | 11 => i11 | 12 => last end in exact r
  end.

Definition hrx5_B8RBC3_b1 : statement := ltac:(hrx5_B8RBC3_get 1).
Definition hrx5_B8RBC3_b2 : statement := ltac:(hrx5_B8RBC3_get 2).
Definition hrx5_B8RBC3_b3 : statement := ltac:(hrx5_B8RBC3_get 3).
Definition hrx5_B8RBC3_b4 : statement := ltac:(hrx5_B8RBC3_get 4).
Definition hrx5_B8RBC3_b5 : statement := ltac:(hrx5_B8RBC3_get 5).
Definition hrx5_B8RBC3_b6 : statement := ltac:(hrx5_B8RBC3_get 6).
Definition hrx5_B8RBC3_b7 : statement := ltac:(hrx5_B8RBC3_get 7).
Definition hrx5_B8RBC3_b8 : statement := ltac:(hrx5_B8RBC3_get 8).
Definition hrx5_B8RBC3_b9 : statement := ltac:(hrx5_B8RBC3_get 9).
Definition hrx5_B8RBC3_b10 : statement := ltac:(hrx5_B8RBC3_get 10).
Definition hrx5_B8RBC3_b11 : statement := ltac:(hrx5_B8RBC3_get 11).
Definition hrx5_B8RBC3_b12 : statement := ltac:(hrx5_B8RBC3_get 12).

Lemma hrx5_B8RBC3_eq : hrx5_B8RB_C3 =
  Sloop (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence (Ssequence (Ssequence hrx5_B8RBC3_b1 hrx5_B8RBC3_b2) hrx5_B8RBC3_b3) hrx5_B8RBC3_b4)
      hrx5_B8RBC3_b5) hrx5_B8RBC3_b6) hrx5_B8RBC3_b7) hrx5_B8RBC3_b8) hrx5_B8RBC3_b9)
      hrx5_B8RBC3_b10) hrx5_B8RBC3_b11) hrx5_B8RBC3_b12) Sbreak.
Proof. reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B8RBC3_eqp t1 t2 x : is_pointer_or_null x ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t1) (tptr t2) x x)) = Vint Int.one.
Proof.
  intros Hx. destruct x; try contradiction; simpl in Hx;
    unfold eval_binop, sem_binary_operation', sem_cmp, sem_cmp_pp; simpl; rewrite !andb_false_r; simpl.
  - subst. reflexivity.
  - destruct (eq_block b b); [| congruence]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hrx5_B8RBC3_eqb_refl A : bytes_eqb A A = true.
Proof.
  unfold bytes_eqb. destruct (list_eq_dec _ _ _) as [|n]; [reflexivity | congruence].
Qed.

(* the temps of the state besides h, s and the block's own (the B8 R states' list, values abstract) *)
Definition hrx5_B8RBC3_temps (gv: globals) (L: hrx5_loc)
  (va vs vhd vnk vkes vst vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vtg vh0 vpath: val) : list localdef :=
  [temp HM._alloc_ok va; temp HM._session vs; temp HM._hashed vhd; temp HM._nk vnk; temp HM._kes vkes;
   temp HM._steps vst; temp HM._i vi; temp HM._now vnow; temp HM._m_lul vlul;
   temp HM._buf vbuf; temp HM._mi vmi; temp HM._mr vmr; temp HM._mc vmc;
   temp HM._img vimg; temp HM._len vlen; temp HM._kind vkind; temp HM._acc_init vai; temp HM._acc_resp var;
   temp HM._target vtg; temp HM._head0 vh0; temp HM._path vpath] ++ hrx5_lvars gv L.

Section Core.
Variables (gv: globals) (L: hrx5_loc)
  (va vs vhd vnk vkes vst vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vtg vh0 vpath: val)
  (hv sv: val) (pe nxt: val) (hb: bool) (ty ix: int) (sid: val) (eph rs ss psk ts: list byte) (lic: int64)
  (F: mpred).

Definition hrx5_B8RBC3_S : list mpred :=
  [@field_at W Ews t_hs (DOT HM._entry) (pe, (nxt, (Val.of_bool hb, (Vint ty, Vint ix)))) hv;
   @field_at W Ews t_hs (DOT HM._static_identity) sid hv;
   hbytes Ews eph (@field_address W t_hs (DOT HM._ephemeral_private) hv);
   hbytes Ews rs (@field_address W t_hs (DOT HM._remote_static) hv);
   hbytes Ews ss (@field_address W t_hs (DOT HM._precomputed_static_static) hv);
   hbytes Ews psk (@field_address W t_hs (DOT HM._preshared_key) hv);
   hbytes Ews ts (@field_address W t_hs (DOT HM._latest_timestamp) hv);
   @field_at W Ews t_hs (DOT HM._last_initiation_consumption) (Vlong lic) hv;
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
   hbytes Ews ts (@field_address W t_hsnap (DOT HM._latest_timestamp) sv);
   @field_at W Ews t_hsnap (DOT HM._last_initiation_consumption) (Vlong lic) sv;
   F].

Definition hrx5_B8RBC3_st (tk: list localdef) : environ -> mpred :=
  PROPx [] (LOCALx (tk ++ [temp HM._h__2 hv; temp HM._s__1 sv] ++
                           hrx5_B8RBC3_temps gv L va vs vhd vnk vkes vst vi vnow vlul vbuf vmi vmr vmc vimg vlen
                             vkind vai var vtg vh0 vpath)
           (SEPx hrx5_B8RBC3_S)).

Definition hrx5_B8RBC3_hyps : Prop :=
  is_pointer_or_null pe /\ is_pointer_or_null nxt /\ is_pointer_or_null sid /\
  @field_compatible W t_hs [] hv /\ @field_compatible W t_hsnap [] sv /\
  Zlength eph = 32 /\ Zlength rs = 32 /\ Zlength ss = 32 /\ Zlength psk = 32 /\ Zlength ts = 12 /\
  (forall x, In x [pe; nxt; sid] -> fold_right_sepcon hrx5_B8RBC3_S |-- valid_pointer x).

Ltac hrx5_B8RBC3_start s :=
  unfold hrx5_Delta; simplify_func_tycontext;
  unfold hrx5_B8RBC3_st, hrx5_B8RBC3_S, hrx5_B8RBC3_temps, hrx5_lvars; cbn [app];
  unfold s; abbreviate_semax.

Lemma hrx5_B8RBC3_p1 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [])
    hrx5_B8RBC3_b1 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'159 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b1.
  forward. forward. forward_if.
  { apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV pe); simpl; auto]);
      unfold hrx5_B8RBC3_S; simpl fold_right_sepcon; cancel. }
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV nxt); simpl; auto]);
        unfold hrx5_B8RBC3_S; simpl fold_right_sepcon; cancel. }
    rewrite hrx5_B8RBC3_eqp by exact Hnx. entailer!. }
  { contradiction. }
Qed.

Lemma hrx5_B8RBC3_p2 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'159 (Vint Int.one)])
    hrx5_B8RBC3_b2 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'160 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b2.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  assert (TB: tc_val tbool (Val.of_bool hb)) by (destruct hb; hnf; auto).
  forward. forward. forward.
  replace (force_val (sem_cast tint tbool (eval_binop Oeq tbool tbool (Val.of_bool hb) (Val.of_bool hb))))
    with (Vint Int.one) by (destruct hb; reflexivity).
  entailer!.
Qed.

Lemma hrx5_B8RBC3_p3 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'160 (Vint Int.one)])
    hrx5_B8RBC3_b3 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'161 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b3.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hrx5_B8RBC3_p4 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'161 (Vint Int.one)])
    hrx5_B8RBC3_b4 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'162 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b4.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hrx5_B8RBC3_p5 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'162 (Vint Int.one)])
    hrx5_B8RBC3_b5 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'163 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b5.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  { entailer!. apply denote_tc_test_eq_split; (eapply derives_trans; [| apply (HV sid); simpl; auto]);
      unfold hrx5_B8RBC3_S; simpl fold_right_sepcon; cancel. }
  rewrite hrx5_B8RBC3_eqp by exact Hsd. entailer!.
Qed.

Lemma hrx5_B8RBC3_p6 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'163 (Vint Int.one)])
    hrx5_B8RBC3_b6 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'164 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b6.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._ephemeral_private) hv, eph,
                Ews, field_address t_hsnap (DOT HM._ephemeral_private) sv, eph).
  { entailer!. simpl. rewrite Le. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8RBC3_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8RBC3_p7 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'164 (Vint Int.one)])
    hrx5_B8RBC3_b7 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'166 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b7.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._remote_static) hv, rs,
                Ews, field_address t_hsnap (DOT HM._remote_static) sv, rs).
  { entailer!. simpl. rewrite Lr. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8RBC3_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8RBC3_p8 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'166 (Vint Int.one)])
    hrx5_B8RBC3_b8 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'168 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b8.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._precomputed_static_static) hv, ss,
                Ews, field_address t_hsnap (DOT HM._precomputed_static_static) sv, ss).
  { entailer!. simpl. rewrite Ls. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8RBC3_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8RBC3_p9 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'168 (Vint Int.one)])
    hrx5_B8RBC3_b9 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'170 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b9.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._preshared_key) hv, psk,
                Ews, field_address t_hsnap (DOT HM._preshared_key) sv, psk).
  { entailer!. simpl. rewrite Lp. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8RBC3_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8RBC3_p10 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'170 (Vint Int.one)])
    hrx5_B8RBC3_b10 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'172 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b10.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward_call (Ews, field_address t_hs (DOT HM._latest_timestamp) hv, ts,
                Ews, field_address t_hsnap (DOT HM._latest_timestamp) sv, ts).
  { entailer!. simpl. rewrite Lt. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  rewrite hrx5_B8RBC3_eqb_refl.
  forward. entailer!.
Qed.

Lemma hrx5_B8RBC3_p11 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'172 (Vint Int.one)])
    hrx5_B8RBC3_b11 (normal_ret_assert (hrx5_B8RBC3_st [temp HM._t'174 (Vint Int.one)])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b11.
  forward_if.
  2: { exfalso; exact (Int.one_not_zero H). }
  forward. forward. forward.
  entailer!. rewrite Int64.eq_true. reflexivity.
Qed.

Lemma hrx5_B8RBC3_p12 {Espec: OracleKind} : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st [temp HM._t'174 (Vint Int.one)])
    hrx5_B8RBC3_b12 (normal_ret_assert (hrx5_B8RBC3_st [])).
Proof.
  intros (Hpe & Hnx & Hsd & Hfh & Hfs & Le & Lr & Ls & Lp & Lt & HV).
  hrx5_B8RBC3_start hrx5_B8RBC3_b12.
  forward_if.
  { exfalso; exact (Int.one_not_zero H). }
  forward. entailer!.
Qed.

Lemma hrx5_B8RBC3_core {Espec: OracleKind} (Rr: ret_assert) : hrx5_B8RBC3_hyps ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RBC3_st []) hrx5_B8RB_C3
    (overridePost (hrx5_B8RBC3_st []) Rr).
Proof.
  intros Hh. rewrite hrx5_B8RBC3_eq. destruct Rr as [r1 r2 r3 r4].
  apply semax_loop with (Q' := hrx5_B8RBC3_st []).
  - eapply semax_post; [ | | | | ].
    5: { eapply semax_seq'; [| exact (hrx5_B8RBC3_p12 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p11 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p10 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p9 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p8 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p7 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p6 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p5 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p4 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p3 Hh)].
         eapply semax_seq'; [| exact (hrx5_B8RBC3_p2 Hh)].
         exact (hrx5_B8RBC3_p1 Hh). }
    all: intros; cbn [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert];
         apply andp_left2; first [apply derives_refl | apply FF_left].
  - eapply semax_pre; [| apply semax_break].
    cbn [RA_break overridePost loop2_ret_assert]. apply andp_left2, derives_refl.
Qed.

End Core.
End Seg.
