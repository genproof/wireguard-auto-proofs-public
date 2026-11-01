(* law handshake_receive: main's phase B5 = body statements 26..33: dev_take, head0, skb_take, shim_take, rx_reset, secret_birth, secret, dispatch.
   From hrx5_S4 to hrx5_S5 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B5_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section B5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B5_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) hrx5_B5
    (overridePost (hrx5_S5 x25519 aead_dec xaead_enc xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH. unfold hrx5_S4, hrx5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w NS. Intros PS T head nk KE st. Intros i kc lul q proto.
  Intros ip4 ip6 port o dp. Intros img tg ai ar.
  unfold hrx5_B5.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr4, hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app].
  freeze [4;5;6;7;8;9;10;11;12;17;18;24;25;29;30;32;33;34;35;36;37;38;39] FA.
  set (D := hrx5_DL x25519 R L sec birth).
  assert_PROP (isptr (l_wd L) /\ isptr (l_ptd L) /\ isptr (l_itd L)) as Hptrs by entailer!.
  assert_PROP (head <> Vundef) as Hhd.
  { destruct H0 as (_ & _ & _ & Hch & _). sep_apply (hrx5_b5_head_def head PS Hch). entailer!. }
  (* dev_take(&ds, &wd) *)
  change (l_ptd L) with (d_ptab D).
  forward_call (Tsh, l_ds L, Tsh, l_wd L, D, Tsh, head).
  { destruct Hptrs as (P1 & P2 & P3). unfold D, hrx5_DL, hrx5_D, setup_dev; simpl.
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction | assumption]. }
  (* head0 = itd.head *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd0.
  { sep_apply (prot3_shim_table1_hd Tsh (l_itd L) T [] (t_L T) eq_refl). entailer!. }
  unfold itable. Intros. rewrite hrx5_b5_itab_cs.
  forward.
  rewrite <- hrx5_b5_itab_cs.
  (* skb_take(&sks, &skb) *)
  assert (Hdp: isptr dp) by (clear - H4; unfold malloc_compatible in H4; destruct dp; try contradiction; exact I).
  forward_call (Tsh, l_sks L, Tsh, l_skb L, hrx5_skb dp o proto ip4 ip6 port).
  { simpl. destruct dp; try contradiction; discriminate. }
  (* shim_take(&ss) *)
  forward_call (gv, Tsh, l_ss L, S, w).
  (* rx_reset() *)
  forward_call gv.
  (* secret_birth = wd.cookie_checker.secret_birthdate; bytes_copy(secret, wd.cookie_checker.secret, 32) *)
  rewrite (hrx5_b5_dev_split Tsh (l_wd L) D).
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wd L)) as FCB by (unfold hrx5_b5_drest; entailer!).
  rewrite (hrx5_b5_cc_open Tsh (l_wd L) (d_cc D)) by exact FCB. Intros.
  match goal with Hc: cc_ok (d_cc D) |- _ => rename Hc into HCC end.
  change (cc_birth (d_cc D)) with birth.
  forward.
  assert (Hs: Zlength (cc_secret (d_cc D)) = 32) by (destruct H as (_ & Hs & _); exact Hs).
  forward_call (Tsh, l_secret L, Tsh, cc_addr (l_wd L), cc_secret (d_cc D)).
  { rewrite Hs. entailer!. unfold cc_addr, OFS_DEV_CHECKER. destruct (l_wd L); try contradiction. simpl.
    rewrite Ptrofs.add_assoc. reflexivity. }
  { rewrite Hs. cancel. }
  change (Vlong birth) with (Vlong (cc_birth (d_cc D))).
  sep_apply (hrx5_b5_cc_close Tsh (l_wd L) (d_cc D) FCB HCC).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_b5_dev_split Tsh (l_wd L) D))).
  (* dispatch(&wd, &skb) *)
  assert (HIT: @data_at Noise.CS Tsh t_itab (hd nullval (t_L T)) (l_itd L) * iter_sepcon (pool_item_rep (t_L T)) (t_D T)
                |-- itable Tsh (d_itab D) T) by (unfold itable; entailer!).
  sep_apply HIT. clear HIT.
  sep_apply (hrx5_b5_rxw_fold gv (l_wd L) head D T PS S w kc lul).
  rewrite (hrx5_b5_obj_open dp o H3 H4).
  pose proof (hrx5_b5_obj_len o H3) as Hlen.
  forward_call (gv, hrx5_W0 D T PS S w kc lul, q, Tsh, l_wd L, head, Tsh, l_skb L,
                hrx5_skb dp o proto ip4 ip6 port, Ews, obj_bytes o).
  { change (sk_data (hrx5_skb dp o proto ip4 ip6 port)) with dp. cancel. }
  { split; [split; [simpl; rewrite Int.unsigned_repr by lia; reflexivity | exact H4] |].
    exact (hrx5_b5_rxw_ok x25519 R L NS PS KE T head nk D S w kc lul H0 H6). }
  Intros d.
  change (sk_data (hrx5_skb dp o proto ip4 ip6 port)) with dp.
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_b5_obj_open dp o H3 H4))).
  change (cc_secret (d_cc D)) with sec.
  change (cc_birth (d_cc D)) with birth.
  match goal with |- _ |-- RA_normal ?X =>
    change (RA_normal X) with (hrx5_S5 x25519 aead_dec xaead_enc xaead_dec gv L FR) end.
  thaw FA. unfold hrx5_S5.
  Exists R sec birth S w NS. Exists PS T head nk KE st. Exists i kc lul q proto.
  Exists ip4 ip6 port o dp. Exists img tg ai ar d.
  unfold hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app].
  entailer!.
  unfold D. apply derives_refl.
Qed.

End B5.
