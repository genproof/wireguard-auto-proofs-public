(* law cookie_reply: phase P3 of main, statements
   18..29: the message bytes, copy, skb fields, now (and its edges), wg_shim_boottime_ns = now, index.

   (+ its children's files). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p3_lemmas.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the side condition of `x % k` (k a positive constant) in VST's typechecker *)
Local Ltac hcy5_p3_mone :=
  let Hx := fresh "Hx" in
  first [ intros [_ Hx] | match goal with H: _ /\ Int.repr _ = Int.mone |- _ => destruct H as [_ Hx] end ];
  apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate.

Lemma hcy5_P3_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S2 x25519 gv L FR) hcy5_P3
    (overridePost (hcy5_S3 x25519 gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S2, hcy5_Delta, hcy5_R, hcy5_P3. simplify_func_tycontext. abbreviate_semax.
  Intros R S n m c rp.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_scrA, hcy5_snaps0, hcy5_globs, hcy5_lvars. cbv [app].
  freeze [0;1;2;3;6;7;8;9;10;12;14;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;32;33;34;35] FA.
  unfold hcy5_drest. Intros. freeze [1;2;3;4] FB.
  rewrite (hcy5_p3_skb_open Tsh (l_skb L)), (hcy5_p3_conv_bytes Ews n m), (hcy5_p3_shim_eq gv S hcy5_w0). Intros.
  forward_call (m, n, Ews).
  Intros bs. rewrite (hcy5_p3_vbytes bs) by auto.
  assert (Hz: Zlength (map Byte.repr bs) = n) by (rewrite Zlength_map; auto).
  rewrite (hcy5_p3_hbytes_eq Ews n (map Byte.repr bs) m) by auto.
  forward_call (Ews, c, Ews, m, map Byte.repr bs).
  { rewrite Hz. entailer!. }
  { rewrite Hz. cancel. }
  forward. forward.
  forward_call tt. Intros b.
  freeze [0;1;2;3;4;5;6;8;9;10;11;12;13] FC.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lc) (SEPx [?F; _]))) _ _ =>
    eapply semax_seq' with (P' := EX pr: Z, PROPx [0 <= pr <= 65535] (LOCALx Lc
      (SEPx [F; @field_at W_cookie_reply Tsh t_skb (DOT HY._protocol) (Vint (Int.repr pr)) (l_skb L)])))
  end.
  { apply (semax_switch_PQR (b mod 3)); [reflexivity | entailer! | |].
    { hcy5_p3_mone. }
    { entailer!. f_equal. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
      rewrite Z.rem_mod_nonneg by lia. reflexivity. }
    assert (Hb: b mod 3 = 0 \/ b mod 3 = 1 \/ b mod 3 = 2) by (pose proof (Z.mod_pos_bound b 3); lia).
    destruct Hb as [Hb | [Hb | Hb]]; rewrite Hb; simpl seq_of_labeled_statement.
    - forward_call 2048. forward. forward. Exists (swab16 2048). entailer!.
    - forward_call 34525. forward. forward. Exists (swab16 34525). entailer!.
    - forward_call tt. Intros u. forward. forward.
      set (z := Int.zero_ext 16 (Int.zero_ext 16 (Int.repr u))).
      assert (0 <= Int.unsigned z <= 65535).
      { pose proof (Int.zero_ext_range 16 (Int.zero_ext 16 (Int.repr u)) ltac:(computable)) as Hz'.
        unfold z. change (two_p 16) with 65536 in Hz'. lia. }
      Exists (Int.unsigned z). rewrite Int.repr_unsigned. entailer!. }
  Intros pr. thaw FC. unfold MORE_COMMANDS, abbreviate. clear MORE_COMMANDS. abbreviate_semax.
  assert_PROP (field_compatible t_skb (DOT HY._protocol) (l_skb L)) as FP by entailer!.
  destruct (hcy5_p3_fa_eqs _ FP) as (E4 & E16 & E2).
  forward_call (hcy5_p3_fa4 (l_skb L), 4, Tsh).
  Intros a4.
  forward_call (hcy5_p3_fa16 (l_skb L), 16, Tsh).
  Intros a6.
  forward_call (hcy5_p3_fa2 (l_skb L), 2, Tsh).
  Intros a2.
  rewrite (hcy5_p3_vbytes a4), (hcy5_p3_vbytes a6), (hcy5_p3_vbytes a2) by auto.
  forward_call tt. Intros d.
  freeze [0;1;2;3;4;5;6;8;9;10;11;12;13] FD.
  forward_call tt. Intros c4.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Lr) (SEPx ?Sp))) _ _ =>
    forward_if (EX nw: int64, PROPx [0 <= Int64.unsigned nw < 2 ^ 62]
                  (LOCALx (temp HY._now (Vlong nw) :: Lr) (SEPx Sp)))
  end.
  { apply prop_right. hcy5_p3_mone. }
  - forward_call tt. Intros c1.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Lr) (SEPx ?Sp))) _ _ =>
      forward_if (EX k: Z, PROPx [k = 120 \/ k = 115]
                    (LOCALx (temp HY._t'16 (Vint (Int.repr k)) :: Lr) (SEPx Sp)))
    end.
    { forward. Exists 120. entailer!. }
    { forward. Exists 115. entailer!. }
    Intros k. forward_call tt. Intros c2.
    sep_apply (hcy5_p3_cc_open Tsh (l_wb L) (hcy5_CC1 x25519 R L) H1). Intros.
    forward. sep_apply modus_ponens_wand.
    forward.
    { entailer!. hcy5_p3_mone. }
    match goal with |- context [temp HY._edge (Vlong ?e)] => set (edge := e) end.
    forward_if.
    + match goal with Hc: Int64.unsigned edge < _ |- _ =>
        assert (0 <= Int64.unsigned edge < 2 ^ 62)
          by (pose proof (Int64.unsigned_range edge);
              change (Int64.unsigned (Int64.shl (Int64.repr 1) (Int64.repr 62))) with (2 ^ 62) in Hc; lia) end.
      forward. Exists edge. entailer!.
    + forward. Exists d. entailer!.
  - forward. Exists d. entailer!.
  - Intros nw. thaw FD. forward.
    forward_call tt. Intros ix. forward.
    replace (Int64.Z_mod_modulus n) with n by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
    sep_apply (hcy5_p3_skb_close Tsh (l_skb L) m (Int.repr n) pr (map Byte.repr a4) (map Byte.repr a6)
                 (map Byte.repr a2) H6 ltac:(rewrite Zlength_map; auto) ltac:(rewrite Zlength_map; auto)
                 ltac:(rewrite Zlength_map; auto)).
    sep_apply (hcy5_p3_shim_close gv S hcy5_w0 nw H2).
    thaw FB. thaw FA.
    unfold hcy5_S3.
    Exists R (hcy5_p3_sboot S nw) m c rp
      (mkPkt n (map Byte.repr bs) pr (map Byte.repr a4) (map Byte.repr a6) (map Byte.repr a2) nw (Int.repr ix)).
    unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrA, hcy5_snaps0, hcy5_globs, hcy5_lvars, hcy5_skb, hcy5_pkt_ok.
    cbv [app q_n q_msg q_now q_proto q_ip4 q_ip6 q_port q_index].
    entailer!.
    + rewrite !Zlength_map. auto.
    + unfold hcy5_drest. apply andp_right; [apply prop_right; exact H1 | cancel].
Qed.

End Phase.
