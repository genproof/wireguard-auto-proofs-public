(* law cookie_mac: main's phase P3, statements 34..43 of hck5_cut.v:
   v1 P3 (hck3_P3.v.old).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p3_lemmas.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* the side condition of `x % k` (k a positive constant) in VST's typechecker *)
Local Ltac hck5_p3_mone :=
  let Hx := fresh "Hx" in
  first [ intros [_ Hx] | match goal with H: _ /\ Int.repr _ = Int.mone |- _ => destruct H as [_ Hx] end ];
  apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate.

Section P3.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P3_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S2 x25519 gv L FR) hck5_P3
    (overridePost (hck5_S3 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S2, hck5_Delta, hck5_R, hck5_P3. simplify_func_tycontext. abbreviate_semax.
  Intros R S A n m c.
  unfold hck5_bside, hck5_bufs, hck5_scr, hck5_snaps0, hck5_globs, hck5_lvars. cbv [app].
  freeze [0;2;3;4;5;6;7;9;11;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;29;30;31;32] FA.
  unfold hck5_drest. Intros. freeze [1;2;3;4] FB.
  rewrite (hck5_p3_skb_open Tsh (l_skb L)), (hck5_conv_bytes Ews n m), (hck5_p3_shim_eq gv S hck5_w0). Intros.
  forward_call (m, n, Ews).
  Intros bs. rewrite (hck5_p3_vbytes bs) by auto.
  forward. forward.
  forward_call tt. Intros b.
  freeze [0;1;2;3;4;5;7;8;9;10;11;12;13] FC.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lc) (SEPx [?F; _]))) _ _ =>
    eapply semax_seq' with (P' := EX pr: Z, PROPx [0 <= pr <= 65535] (LOCALx Lc
      (SEPx [F; @field_at W_cookie_mac Tsh t_skb (DOT HK._protocol) (Vint (Int.repr pr)) (l_skb L)])))
  end.
  { apply (semax_switch_PQR (b mod 3)); [reflexivity | entailer! | |].
    { hck5_p3_mone. }
    { entailer!. f_equal. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
      rewrite Z.rem_mod_nonneg by lia. reflexivity. }
    assert (Hb: b mod 3 = 0 \/ b mod 3 = 1 \/ b mod 3 = 2) by (pose proof (Z.mod_pos_bound b 3); lia).
    destruct Hb as [Hb | [Hb | Hb]]; rewrite Hb; simpl seq_of_labeled_statement.
    - forward_call 2048. forward. forward. Exists (swab16 2048). entailer!.
    - forward_call 34525. forward. forward. Exists (swab16 34525). entailer!.
    - forward_call tt. Intros u. forward. forward.
      set (z := Int.zero_ext 16 (Int.zero_ext 16 (Int.repr u))).
      assert (0 <= Int.unsigned z <= 65535).
      { pose proof (Int.zero_ext_range 16 (Int.zero_ext 16 (Int.repr u)) ltac:(computable)) as Hz.
        unfold z. change (two_p 16) with 65536 in Hz. lia. }
      Exists (Int.unsigned z). rewrite Int.repr_unsigned. entailer!. }
  Intros pr. thaw FC. unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS. abbreviate_semax.
  assert_PROP (field_compatible t_skb (DOT HK._protocol) (l_skb L)) as FP by entailer!.
  destruct (hck5_p3_fa_eqs _ FP) as (E4 & E16 & E2).
  forward_call (hck5_p3_fa4 (l_skb L), 4, Tsh).
  Intros a4.
  forward_call (hck5_p3_fa16 (l_skb L), 16, Tsh).
  Intros a6.
  forward_call (hck5_p3_fa2 (l_skb L), 2, Tsh).
  Intros a2.
  rewrite (hck5_p3_vbytes a4), (hck5_p3_vbytes a6), (hck5_p3_vbytes a2) by auto.
  forward_call tt. Intros d.
  freeze [0;1;2;3;4;5;7;8;9;10;11;12] FD.
  forward_call tt. Intros c4.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Lr) (SEPx ?Sp))) _ _ =>
    forward_if (EX nw: int64, PROPx [0 <= Int64.unsigned nw < 2 ^ 62]
                  (LOCALx (temp HK._now (Vlong nw) :: Lr) (SEPx Sp)))
  end.
  { apply prop_right. hck5_p3_mone. }
  - forward_call tt. Intros c1.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Lr) (SEPx ?Sp))) _ _ =>
      forward_if (EX k: Z, PROPx [k = 120 \/ k = 115]
                    (LOCALx (temp HK._t'29 (Vint (Int.repr k)) :: Lr) (SEPx Sp)))
    end.
    { forward. Exists 120. entailer!. }
    { forward. Exists 115. entailer!. }
    Intros k. forward_call tt. Intros c2.
    sep_apply (hck5_p3_cc_open Tsh (l_wb L) (hck5_CC1 x25519 R L) H2). Intros.
    forward. sep_apply modus_ponens_wand.
    forward.
    { entailer!. hck5_p3_mone. }
    match goal with |- context [temp HK._edge (Vlong ?e)] => set (edge := e) end.
    forward_if.
    + match goal with Hc: Int64.unsigned edge < _ |- _ =>
        assert (0 <= Int64.unsigned edge < 2 ^ 62)
          by (pose proof (Int64.unsigned_range edge);
              change (Int64.unsigned (Int64.shl (Int64.repr 1) (Int64.repr 62))) with (2 ^ 62) in Hc; lia) end.
      forward. Exists edge. entailer!.
    + forward. Exists d. entailer!.
  - forward. Exists d. entailer!.
  - Intros nw. thaw FD. forward.
    replace (Int64.Z_mod_modulus n) with n by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
    sep_apply (hck5_p3_skb_close Tsh (l_skb L) m (Int.repr n) pr (map Byte.repr a4) (map Byte.repr a6)
                 (map Byte.repr a2) H7 ltac:(rewrite Zlength_map; auto) ltac:(rewrite Zlength_map; auto)
                 ltac:(rewrite Zlength_map; auto)).
    rewrite (hck5_p3_hbytes_eq Ews n (map Byte.repr bs) m) by (rewrite Zlength_map; auto).
    sep_apply (hck5_p3_shim_close gv S hck5_w0 nw H3).
    thaw FB. thaw FA.
    unfold hck5_S3.
    Exists R (hck5_p3_sboot S nw) A m c
      (mkPkt5 n (map Byte.repr bs) pr (map Byte.repr a4) (map Byte.repr a6) (map Byte.repr a2) nw).
    unfold hck5_bside, hck5_bufs, hck5_scr, hck5_snaps0, hck5_globs, hck5_lvars, hck5_skb, hck5_pkt_ok.
    cbv [app q_n q_msg q_now q_proto q_ip4 q_ip6 q_port].
    entailer!.
    + rewrite !Zlength_map. auto.
    + unfold hck5_drest. apply andp_right; [apply prop_right; exact H2 | cancel].
Qed.

End P3.
