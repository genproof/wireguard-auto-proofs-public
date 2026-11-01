(* law handshake_receive: main's phase B2 = body statements 12..17: the queue length, the rate limiter, the skb's protocol and source.
   From hrx5_S1 to hrx5_S2 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B2_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the side condition of `x % k` (k a positive constant) in VST's typechecker *)
Local Ltac hrx5_B2_mone :=
  let Hx := fresh "Hx" in
  first [ intros [_ Hx] | match goal with H: _ /\ Int.repr _ = Int.mone |- _ => destruct H as [_ Hx] end ];
  apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate.

Section B2.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B2_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S1 x25519 gv L FR) hrx5_B2
    (overridePost (hrx5_S2 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH. unfold hrx5_S1, hrx5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w NS. Intros PS T head nk KE st. Intros i kc lul.
  unfold hrx5_B2.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_skb0, hrx5_ltemps, hrx5_lvars. cbn [app].
  freeze [0;1;2;3;4;5;6;7;8;9;10;11;12;13;15;16;17;18;19;20;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37] FA.
  rewrite hrx5_B2_qlen_, hrx5_B2_skb_open, hrx5_B2_shim_eq. Intros.
  forward_call tt. Intros b.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lc) (SEPx (?F0 :: ?F1 :: ?F2 :: ?F3 :: _ :: ?Sr)))) _ _ =>
    eapply semax_seq' with (P' := EX q: int, PROPx [] (LOCALx Lc
      (SEPx (F0 :: F1 :: F2 :: F3 :: @data_at W Ews tint (Vint q) (gv HM._wg_shim_handshake_queue_len) :: Sr))))
  end.
  { apply (semax_switch_PQR (b mod 4)); [reflexivity | entailer! | |].
    { hrx5_B2_mone. }
    { entailer!. f_equal. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
      rewrite Z.rem_mod_nonneg by lia. reflexivity. }
    assert (Hb: b mod 4 = 0 \/ b mod 4 = 1 \/ b mod 4 = 2 \/ b mod 4 = 3) by (pose proof (Z.mod_pos_bound b 4); lia).
    destruct Hb as [Hb | [Hb | [Hb | Hb]]]; rewrite Hb; simpl seq_of_labeled_statement.
    - forward_call tt. Intros c. forward.
      { entailer!. split; [| hrx5_B2_mone].
        unfold Int.mods. rewrite (Int.signed_repr c), (Int.signed_repr 5) by rep_lia. rewrite Z.rem_mod_nonneg by lia.
        pose proof (Z.mod_pos_bound c 5). rewrite Int.signed_repr by rep_lia. rep_lia. }
      forward. Exists (Int.add (Int.repr 510) (Int.mods (Int.repr c) (Int.repr 5))). entailer!.
    - forward_call tt. Intros c. forward. forward.
      match goal with |- context [data_at _ tint (Vint ?v) _] => Exists v end. entailer!.
    - forward_call tt. Intros c. forward. forward.
      match goal with |- context [data_at _ tint (Vint ?v) _] => Exists v end. entailer!.
    - forward_call tt. Intros c. forward. forward.
      match goal with |- context [data_at _ tint (Vint ?v) _] => Exists v end. entailer!. }
  Intros q. unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS. abbreviate_semax.
  forward_call tt. Intros r. forward.
  set (rb := negb (Int.eq (Int.and (Int.repr r) (Int.repr 1)) Int.zero)).
  replace (Vint (if Int.eq (Int.and (Int.repr r) (Int.repr 1)) Int.zero then Int.zero else Int.one))
    with (Val.of_bool rb) by (unfold rb; destruct (Int.eq _ _); reflexivity).
  forward_call tt. Intros b2.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lc) (SEPx (?F0 :: ?F1 :: ?F2 :: ?F3 :: ?F4 :: ?F5 :: ?F6 :: _ :: ?Sr)))) _ _ =>
    eapply semax_seq' with (P' := EX pr: Z, PROPx [0 <= pr <= 65535] (LOCALx Lc
      (SEPx (F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: F6 ::
             @field_at W Tsh t_skb (DOT HM._protocol) (Vint (Int.repr pr)) (l_skb L) :: Sr))))
  end.
  { apply (semax_switch_PQR (b2 mod 3)); [reflexivity | entailer! | |].
    { hrx5_B2_mone. }
    { entailer!. f_equal. unfold Int.mods. rewrite (Int.signed_repr b2), (Int.signed_repr 3) by rep_lia.
      rewrite Z.rem_mod_nonneg by lia. reflexivity. }
    assert (Hb: b2 mod 3 = 0 \/ b2 mod 3 = 1 \/ b2 mod 3 = 2) by (pose proof (Z.mod_pos_bound b2 3); lia).
    destruct Hb as [Hb | [Hb | Hb]]; rewrite Hb; simpl seq_of_labeled_statement.
    - forward_call 2048. forward. forward. Exists (swab16 2048). entailer!.
    - forward_call 34525. forward. forward. Exists (swab16 34525). entailer!.
    - forward_call tt. Intros u. forward. forward.
      set (z := Int.zero_ext 16 (Int.zero_ext 16 (Int.repr u))).
      assert (0 <= Int.unsigned z <= 65535).
      { pose proof (Int.zero_ext_range 16 (Int.zero_ext 16 (Int.repr u)) ltac:(computable)) as Hz.
        unfold z. change (two_p 16) with 65536 in Hz. lia. }
      Exists (Int.unsigned z). rewrite Int.repr_unsigned. entailer!. }
  Intros pr. unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS. abbreviate_semax.
  assert_PROP (@field_compatible W t_skb (DOT HM._protocol) (l_skb L)) as FP by entailer!.
  destruct (hrx5_B2_fa_eqs _ FP) as (E4 & E16 & E2).
  forward_call (hrx5_B2_fa4 (l_skb L), 4, Tsh). Intros a4.
  forward_call (hrx5_B2_fa16 (l_skb L), 16, Tsh). Intros a6.
  forward_call (hrx5_B2_fa2 (l_skb L), 2, Tsh). Intros a2.
  rewrite (hrx5_B2_vbytes a4), (hrx5_B2_vbytes a6), (hrx5_B2_vbytes a2) by auto.
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S2 x25519 gv L FR) end.
  sep_apply (hrx5_B2_skb_close L pr (map Byte.repr a4) (map Byte.repr a6) (map Byte.repr a2) H7
    ltac:(rewrite Zlength_map; auto) ltac:(rewrite Zlength_map; auto) ltac:(rewrite Zlength_map; auto)).
  sep_apply (hrx5_B2_shim_close gv S w rb H3).
  rewrite hrx5_B2_qlen.
  thaw FA. unfold hrx5_S2.
  Exists R sec birth (hrx5_B2_srl S rb) w NS. Exists PS T head nk KE st. Exists i kc lul q pr.
  Exists (map Byte.repr a4) (map Byte.repr a6) (map Byte.repr a2).
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_ltemps, hrx5_lvars. cbn [app].
  entailer!.
Qed.

End B2.
