(* law handshake_receive: main's phase B3 = body statements 18..20: kind, the packet (the four kinds; `continue` on a failure), skb.len.
   From hrx5_S2 to hrx5_S3 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_lem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K2.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section B3.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

#[local] Instance hrx5_b3_cce : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

Lemma hrx5_b3_skb_cs sh (dv lv pv: val) (a b c: list val) p :
  @data_at Cookie.CS sh t_skb (dv, (lv, (pv, (a, (b, c))))) p =
  @data_at W_handshake_receive sh t_skb (dv, (lv, (pv, (a, (b, c))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Cookie.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_b3_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hrx5_b3_obj_len o : obj_ok o -> 0 <= Zlength (obj_bytes o) <= Int.max_unsigned.
Proof.
  destruct o as [b|M|M|M]; simpl; intros HO.
  - pose proof (Zlength_nonneg b). lia.
  - destruct HO as (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
    rewrite !Zlength_app, !hrx5_b3_le32_len, L1, L2, L3, L4, L5. rep_lia.
  - destruct HO as (L1 & L2 & L3 & L4). unfold resp_bytes.
    rewrite !Zlength_app, !hrx5_b3_le32_len, L1, L2, L3, L4. rep_lia.
  - destruct HO as (L1 & L2). unfold cookie_msg_bytes.
    rewrite !Zlength_app, !hrx5_b3_le32_len, L1, L2. rep_lia.
Qed.

Ltac hrx5_b3_branch k lem :=
  match goal with
  | |- semax _ _ _ _ =>
    match goal with HY: hrx5_hyps ?x25519 ?aead_enc ?aead_dec ?xaead_enc ?xaead_dec, H: _ |- _ =>
    match goal with
    | gv: globals, L: hrx5_loc, FR: mpred |- _ =>
      pose proof (@lem x25519 aead_enc aead_dec xaead_enc xaead_dec _ gv L FR (hrx5_B3_lem x25519) HY) as HK;
      unfold hrx5_RB in HK;
      eapply semax_pre with (P' := hrx5_B3_P x25519 k gv L FR);
      [ | match goal with D := _ : tycontext, PO := _ : ret_assert, MC := _ : statement |- _ =>
            unfold PO, MC, abbreviate; rewrite hrx5_overridePost2;
            change D with (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec); exact HK end ]
    end end end.

Lemma hrx5_B3_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S2 x25519 gv L FR) hrx5_B3
    (overridePost (hrx5_S3 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HY.
  rewrite hrx5_B3_eq.
  unfold hrx5_Delta, hrx5_S2.
  Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto.
  Intros ip4 ip6 port.
  unfold hrx5_B3_draw, hrx5_B3_if, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr.
  cbn [app].
  abbreviate_semax.
  forward_call tt. Intros b.
  forward.
  { entailer!. match goal with X: _ /\ Int.repr 4 = Int.mone |- _ => destruct X as [_ X];
      apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate X end. }
  assert (Hk: Int.mods (Int.repr b) (Int.repr 4) = Int.repr (b mod 4)).
  { unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Hk.
  assert (Hm: 0 <= b mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  forward_if (hrx5_B3_Q x25519 gv L FR).
  - (* kind 0 *)
    hrx5_b3_branch 0 hrx5_B3_K0_ok.
    assert (Hkk: b mod 4 = 0) by lia. rewrite Hkk.
    unfold hrx5_B3_P. Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto. Exists ip4 ip6 port.
    unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
    entailer!.
  - forward_if.
    + (* kind 1 *)
      hrx5_b3_branch 1 hrx5_B3_K1_ok.
      assert (Hkk: b mod 4 = 1) by lia. rewrite Hkk.
      unfold hrx5_B3_P. Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto. Exists ip4 ip6 port.
      unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
      entailer!.
    + forward_if.
      * (* kind 2 *)
        hrx5_b3_branch 2 hrx5_B3_K2_ok.
        assert (Hkk: b mod 4 = 2) by lia. rewrite Hkk.
        unfold hrx5_B3_P. Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto. Exists ip4 ip6 port.
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
        entailer!.
      * (* kind 3 *)
        assert (Hk3: b mod 4 = 3) by lia.
        hrx5_b3_branch 3 hrx5_B3_K3_ok.
        assert (Hkk: b mod 4 = 3) by lia. rewrite Hkk.
        unfold hrx5_B3_P. Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto. Exists ip4 ip6 port.
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
        entailer!.
  - (* skb.len = len *)
    unfold hrx5_B3_Q.
    Intros R1 sec1 birth1 S1 w1 NS1 PS1 T1.
    Intros head1 nk1 KE1 st1 i1 kc1 lul1 q1.
    Intros proto1 ip41 ip61 port1 o dp img.
    unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_ptrs, hrx5_B3_len; cbn [app].
    unfold hrx5_B3_skbd. Intros lv.
    rewrite hrx5_b3_skb_cs.
    match goal with Ho: obj_ok o |- _ => pose proof (hrx5_b3_obj_len o Ho) as Hlen end.
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S3 x25519 gv L FR) end.
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    unfold hrx5_S3.
    Exists R1 sec1 birth1 S1 w1 NS1 PS1 T1.
    Exists head1 nk1 KE1 st1 i1 kc1 lul1 q1.
    Exists proto1 ip41 ip61 port1 o dp img.
    unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_ptrs; cbn [app].
    unfold skb_rep, hrx5_skb, skb_val; cbn [sk_data sk_len sk_proto sk_ip4 sk_ip6 sk_port].
    rewrite hrx5_b3_skb_cs.
    entailer!.
    unfold skb_ok; cbn [sk_proto sk_ip4 sk_ip6 sk_port]; auto.
Qed.

End B3.
