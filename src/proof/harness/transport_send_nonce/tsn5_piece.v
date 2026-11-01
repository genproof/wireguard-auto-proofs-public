(* Law transport_send_nonce: the harness piece (harness/transport_send_nonce.c):
   draw_steps, draw_u64 and main, proved in W_tsn5 against the external world QuickProof.Env at W_tsn5.
   Interface: tsn5_spec.v.  draw_steps / draw_u64: copies of law counter's (hcnt_piece3.v, the same Clight). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_world.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_spec.
Require WgNoise.contracts.x_transport_send_nonce.
Require Import WgNoise.harness.x_transport_send_nonce.code.

#[local] Existing Instance W_tsn5.
Local Open Scope Z_scope.

Definition tsn5_V : varspecs := QPvarspecs WgNoise.contracts.x_transport_send_nonce.Harness.qp.
Definition tsn5_Gprog : funspecs := tsn5_imports W_tsn5 ++ tsn5_G.

Lemma tsn5_body_draw_steps : semax_body tsn5_V tsn5_Gprog f_draw_steps tsn5_draw_steps_spec.
Proof.
  start_function.
  forward_call tt. Intros n.
  forward_if (temp _t'2 (Vlong (Int64.repr n))).
  { forward. entailer!. }
  { exfalso. unfold Int64.ltu in H0. rewrite (Int64.unsigned_repr n) in H0 by rep_lia.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned in H0.
    if_tac in H0. lia. discriminate. }
  forward. Exists n. entailer!.
Qed.

Lemma tsn5_body_draw_u64 : semax_body tsn5_V tsn5_Gprog f_draw_u64 tsn5_draw_u64_spec.
Proof.
  start_function.
  eapply semax_seq' with (P' := (EX hi:Z, PROP (0 <= hi <= Int.max_unsigned)
                                         LOCAL (temp _hi (Vlong (Int64.repr hi))) SEP ())%assert).
  { eapply semax_seq'. forward_call tt. apply ENTAIL_refl. Intros hi. forward. Exists hi. entailer!. }
  abbreviate_semax. Intros hi.
  forward_call tt. Intros lo.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. rewrite Int64.repr_unsigned; auto.
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma tsn5_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

(* R = REJECT_AFTER_MESSAGES = 2^64 - 1 - 8128 - 1 *)
Definition tsn5_R : Z := Int64.max_unsigned - 8129.

Definition tkp := Tstruct _noise_keypair noattr.

Lemma tsn5_R_val : tsn5_R = Int64.modulus - 8130.
Proof. reflexivity. Qed.

Lemma tsn5_neg z : - Int64.modulus <= z < 0 -> Int64.unsigned (Int64.repr z) = z + Int64.modulus.
Proof.
  intros Hz. rewrite Int64.unsigned_repr_eq.
  replace z with ((z + Int64.modulus) + (-1) * Int64.modulus) at 1 by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* the start values of the switch's five cases are counters of a valid key, [0, R] *)
Lemma tsn5_start1 x : 0 <= x ->
  0 <= Int64.unsigned (Int64.repr (-1 - 8128 - 1 - Int.unsigned (Int.repr (x mod 8)))) <= tsn5_R.
Proof.
  intros Hx. pose proof (Z.mod_pos_bound x 8).
  rewrite Int.unsigned_repr by rep_lia. rewrite tsn5_neg by rep_lia. rewrite tsn5_R_val. rep_lia.
Qed.

Lemma tsn5_start2 x : 0 <= x <= Int64.max_unsigned ->
  0 <= Int64.unsigned
    (Int64.add (Int64.shl (Int64.repr 1) (Int64.repr 63))
       (Int64.modu (Int64.repr x)
          (Int64.add (Int64.sub (Int64.repr (-1 - 8128 - 1)) (Int64.shl (Int64.repr 1) (Int64.repr 63)))
             (Int64.repr 1)))) <= tsn5_R.
Proof.
  intros Hx.
  replace (Int64.shl (Int64.repr 1) (Int64.repr 63)) with (Int64.repr (2 ^ 63)) by reflexivity.
  replace (Int64.add (Int64.sub (Int64.repr (-1 - 8128 - 1)) (Int64.repr (2 ^ 63))) (Int64.repr 1))
    with (Int64.repr (tsn5_R - 2 ^ 63 + 1)) by reflexivity.
  unfold Int64.modu. rewrite (Int64.unsigned_repr x) by rep_lia.
  rewrite (Int64.unsigned_repr (tsn5_R - 2 ^ 63 + 1)) by (rewrite tsn5_R_val; rep_lia).
  assert (Hm: 0 <= x mod (tsn5_R - 2 ^ 63 + 1) < tsn5_R - 2 ^ 63 + 1)
    by (apply Z.mod_pos_bound; rewrite tsn5_R_val; rep_lia).
  rewrite add64_repr.
  rewrite Int64.unsigned_repr by (rewrite tsn5_R_val in *; rep_lia). lia.
Qed.

Lemma tsn5_start4 x : 0 <= x <= Int64.max_unsigned ->
  0 <= Int64.unsigned (Int64.modu (Int64.repr x) (Int64.add (Int64.repr (-1 - 8128 - 1)) (Int64.repr 1)))
    <= tsn5_R.
Proof.
  intros Hx.
  replace (Int64.add (Int64.repr (-1 - 8128 - 1)) (Int64.repr 1)) with (Int64.repr (tsn5_R + 1))
    by reflexivity.
  unfold Int64.modu. rewrite (Int64.unsigned_repr x) by rep_lia.
  rewrite (Int64.unsigned_repr (tsn5_R + 1)) by (rewrite tsn5_R_val; rep_lia).
  assert (Hm: 0 <= x mod (tsn5_R + 1) < tsn5_R + 1)
    by (apply Z.mod_pos_bound; rewrite tsn5_R_val; rep_lia).
  rewrite Int64.unsigned_repr by (rewrite tsn5_R_val in *; rep_lia). lia.
Qed.

(* kp: the two fields main uses (sending.is_valid, sending_counter.counter) and the rest *)
(* (unfold_data_at of the whole struct takes ~70 s: split its memory block instead, at the offsets 72 (is_valid,
   1 byte), 80 (counter, 8 bytes); sizeof = 1200) *)
Definition tsn5_rest (p: val) : mpred :=
  (!! field_compatible tkp nil p &&
   (memory_block Tsh 72 p * memory_block Tsh 7 (offset_val 73 p) * memory_block Tsh 1112 (offset_val 88 p)))%logic.

Lemma tsn5_split p : headptr p ->
  data_at_ Tsh tkp p =
  (tsn5_rest p * field_at_ Tsh tkp (DOT _sending DOT _is_valid) p *
   field_at_ Tsh tkp (DOT _sending_counter DOT _counter) p)%logic.
Proof.
  intros [b ->].
  rewrite data_at__memory_block, !field_at__memory_block.
  unfold tsn5_rest.
  change (sizeof tkp) with 1200.
  change (sizeof (nested_field_type tkp (DOT _sending DOT _is_valid))) with 1.
  change (sizeof (nested_field_type tkp (DOT _sending_counter DOT _counter))) with 8.
  assert (F: forall gfs, field_compatible tkp [] (Vptr b Ptrofs.zero) -> legal_nested_field tkp gfs ->
            field_compatible tkp gfs (Vptr b Ptrofs.zero)).
  { intros gfs (?&?&?&?&?) ?. repeat split; auto. }
  assert (L1: legal_nested_field tkp (DOT _sending DOT _is_valid)) by (compute; auto).
  assert (L2: legal_nested_field tkp (DOT _sending_counter DOT _counter)) by (compute; intuition).
  assert (E: forall k, offset_val k (Vptr b Ptrofs.zero) = Vptr b (Ptrofs.repr k))
    by (intros; simpl; rewrite Ptrofs.add_zero_l; auto).
  assert (S: memory_block Tsh 1200 (Vptr b Ptrofs.zero) =
     (memory_block Tsh 72 (Vptr b (Ptrofs.repr 0)) * memory_block Tsh 1 (Vptr b (Ptrofs.repr 72)) *
      memory_block Tsh 7 (Vptr b (Ptrofs.repr 73)) * memory_block Tsh 8 (Vptr b (Ptrofs.repr 80)) *
      memory_block Tsh 1112 (Vptr b (Ptrofs.repr 88)))%logic).
  { change Ptrofs.zero with (Ptrofs.repr 0).
    change 1200 with (72 + 1128). rewrite (memory_block_split Tsh b 0 72 1128) by rep_lia.
    change 1128 with (1 + 1127). rewrite (memory_block_split Tsh b (0 + 72) 1 1127) by rep_lia.
    change 1127 with (7 + 1120). rewrite (memory_block_split Tsh b (0 + 72 + 1) 7 1120) by rep_lia.
    change 1120 with (8 + 1112). rewrite (memory_block_split Tsh b (0 + 72 + 1 + 7) 8 1112) by rep_lia.
    rewrite !sepcon_assoc. reflexivity. }
  rewrite S. clear S.
  apply pred_ext.
  - Intros. rewrite !field_compatible_field_address by (apply F; auto).
    change (nested_field_offset tkp (DOT _sending DOT _is_valid)) with 72.
    change (nested_field_offset tkp (DOT _sending_counter DOT _counter)) with 80.
    rewrite !E. change (Ptrofs.repr 0) with Ptrofs.zero. entailer!.
  - Intros. rewrite !field_compatible_field_address by (apply F; auto).
    change (nested_field_offset tkp (DOT _sending DOT _is_valid)) with 72.
    change (nested_field_offset tkp (DOT _sending_counter DOT _counter)) with 80.
    rewrite !E. change (Ptrofs.repr 0) with Ptrofs.zero. entailer!.
Qed.

Lemma tsn5_body_main : semax_body tsn5_V tsn5_Gprog f_main tsn5_main_spec.
Proof.
  unfold tsn5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply tsn5_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  abbreviate_semax.
  forward_call tt. Intros b.
  eapply semax_seq' with (P' := (EX st: Z,
      PROP (0 <= st <= tsn5_R)
      LOCAL (temp _start (Vlong (Int64.repr st)); lvar _kp tkp v_kp; gvars gv)
      SEP (data_at_ Tsh tkp v_kp; TT))%assert).
  { apply (semax_switch_PQR (b mod 5)).
    - reflexivity.
    - entailer!. destruct H2 as [_ H2]. apply (f_equal Int.signed) in H2.
      rewrite Int.signed_repr in H2 by rep_lia. rewrite Int.signed_mone in H2. lia.
    - entailer!. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
      rewrite Z.rem_mod_nonneg by lia. reflexivity.
    - rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 5); rep_lia).
      assert (Hb: b mod 5 = 0 \/ b mod 5 = 1 \/ b mod 5 = 2 \/ b mod 5 = 3 \/ b mod 5 = 4)
        by (pose proof (Z.mod_pos_bound b 5); lia).
      destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]]; rewrite Hb; simpl seq_of_labeled_statement.
      + forward. forward.
        match goal with |- context [temp _start (Vlong ?E)] => Exists (Int64.unsigned E) end.
        entailer!.
      + forward_call tt. Intros x. forward. forward.
        match goal with |- context [temp _start (Vlong ?E)] => Exists (Int64.unsigned E) end.
        entailer!. split; [apply tsn5_start1; lia | rewrite Int64.repr_unsigned; reflexivity].
      + forward_call tt. Intros x. forward. forward.
        match goal with |- context [temp _start (Vlong ?E)] => Exists (Int64.unsigned E) end.
        entailer!. split; [apply tsn5_start2; lia | rewrite Int64.repr_unsigned; reflexivity].
      + forward_call tt. Intros x. forward. forward.
        match goal with |- context [temp _start (Vlong ?E)] => Exists (Int64.unsigned E) end.
        entailer!. pose proof (Z.mod_pos_bound x 8).
        rewrite Int.unsigned_repr by rep_lia. rewrite tsn5_R_val. rep_lia.
      + forward_call tt. Intros x. forward. forward.
        match goal with |- context [temp _start (Vlong ?E)] => Exists (Int64.unsigned E) end.
        entailer!. split; [apply tsn5_start4; lia | rewrite Int64.repr_unsigned; reflexivity]. }
  abbreviate_semax. Intros st.
  assert_PROP (headptr v_kp) as HP by entailer!.
  rewrite (tsn5_split v_kp HP). Intros.
  forward. forward. forward. forward_call tt. Intros steps. forward.
  forward_loop (EX i: Z, EX sh: Z, EX bv: bool,
    PROP (0 <= i <= steps; 0 <= sh <= tsn5_R + 1; bv = true -> sh <= tsn5_R)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _steps (Vlong (Int64.repr steps));
           temp _shadow (Vlong (Int64.repr sh)); lvar _kp tkp v_kp; gvars gv)
    SEP (tsn5_rest v_kp; field_at Tsh tkp (DOT _sending DOT _is_valid) (Val.of_bool bv) v_kp;
         field_at Tsh tkp (DOT _sending_counter DOT _counter) (Vlong (Int64.repr sh)) v_kp; TT))%assert
  continue: (EX i: Z, EX sh: Z, EX bv: bool,
    PROP (0 <= i < steps; 0 <= sh <= tsn5_R + 1; bv = true -> sh <= tsn5_R)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _steps (Vlong (Int64.repr steps));
           temp _shadow (Vlong (Int64.repr sh)); lvar _kp tkp v_kp; gvars gv)
    SEP (tsn5_rest v_kp; field_at Tsh tkp (DOT _sending DOT _is_valid) (Val.of_bool bv) v_kp;
         field_at Tsh tkp (DOT _sending_counter DOT _counter) (Vlong (Int64.repr sh)) v_kp; TT))%assert
  break: (EX sh: Z, EX bv: bool,
    PROP (0 <= sh <= tsn5_R + 1)
    LOCAL (temp _shadow (Vlong (Int64.repr sh)); lvar _kp tkp v_kp; gvars gv)
    SEP (tsn5_rest v_kp; field_at Tsh tkp (DOT _sending DOT _is_valid) (Val.of_bool bv) v_kp;
         field_at Tsh tkp (DOT _sending_counter DOT _counter) (Vlong (Int64.repr sh)) v_kp; TT))%assert.
  { Exists 0 st true. entailer!. }
  { Intros i sh bv.
    forward_if.
    2:{ forward. Exists sh bv. entailer!. }
    destruct bv.
    2:{ forward. forward_if. { forward. Exists sh false. entailer!. } { exfalso. congruence. } }
    specialize (H4 eq_refl).
    forward. forward_if. { exfalso. apply Int.one_not_zero; auto. }
    forward_if.
    { forward. Exists sh true. entailer!. }
    forward. forward. forward. forward. forward. forward. forward.
    change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr, sub64_repr. replace (sh + 1 - 1) with sh by lia.
    (* CHECK(nonce == nonce_model) *)
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { apply ENTAIL_refl. }
    { match goal with |- semax _ ?P _ _ => forward_if P end.
      - exfalso. rewrite Int64.eq_true in *. discriminate.
      - forward. entailer!.
      - forward. apply ENTAIL_refl. }
    abbreviate_semax.
    (* CHECK((nonce >= REJECT_AFTER_MESSAGES) == (nonce >= M_R)) *)
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { apply ENTAIL_refl. }
    { match goal with |- semax _ ?P _ _ => forward_if P end.
      - exfalso. rewrite !sub64_repr in H8. change (Int.signed (Int.repr 1)) with 1 in H8.
        replace (-1 - 8128 - 1) with (-8130) in H8 by lia. rewrite Int.eq_true in H8.
        apply Int.one_not_zero. exact H8.
      - forward. entailer!.
      - forward. apply ENTAIL_refl. }
    abbreviate_semax.
    forward_if.
    - rewrite Int64.unsigned_repr in H8 by (rewrite tsn5_R_val in *; rep_lia).
      rewrite tsn5_neg in H8 by rep_lia. pose proof tsn5_R_val.
      forward. Exists i (sh + 1) false. entailer!.
    - rewrite Int64.unsigned_repr in H8 by (rewrite tsn5_R_val in *; rep_lia).
      rewrite tsn5_neg in H8 by rep_lia. pose proof tsn5_R_val.
      forward. Exists i (sh + 1) true. entailer!. }
  { Intros i sh bv. forward. Exists (i + 1) sh bv. entailer!. }
  Intros sh bv.
  (* CHECK((u64)kp.sending_counter.counter == shadow) *)
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    match goal with |- semax _ ?P _ _ => forward_if P end.
    - exfalso. rewrite Int64.eq_true in *. discriminate.
    - forward. entailer!.
    - forward. entailer!. }
  abbreviate_semax.
  (* CHECK(shadow <= M_R + 1) *)
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { apply ENTAIL_refl. }
  { match goal with |- semax _ ?P _ _ => forward_if P end.
    - exfalso. rewrite !sub64_repr, add64_repr in H3. unfold Int64.ltu in H3.
      rewrite tsn5_neg in H3 by rep_lia. rewrite Int64.unsigned_repr in H3 by (rewrite tsn5_R_val in *; rep_lia).
      destruct (zlt _ _) in H3; [rewrite tsn5_R_val in *; lia | apply Int.one_not_zero; exact H3].
    - forward. entailer!.
    - forward. apply ENTAIL_refl. }
  abbreviate_semax.
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold tsn5_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward.
  change (Tstruct _noise_keypair noattr) with tkp. rewrite (tsn5_split v_kp HP).
  sep_apply (field_at_field_at_ Tsh tkp (DOT _sending DOT _is_valid)).
  sep_apply (field_at_field_at_ Tsh tkp (DOT _sending_counter DOT _counter)).
  cancel.
Qed.

Theorem tsn5_piece : piece_ok [u_tsn5] tsn5_imports tsn5_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_tsn5; (split; [left; reflexivity|]).
    + exists f_draw_steps; split; [reflexivity | exact tsn5_body_draw_steps].
    + exists f_draw_u64; split; [reflexivity | exact tsn5_body_draw_u64].
    + exists f_main; split; [reflexivity | exact tsn5_body_main].
Qed.
