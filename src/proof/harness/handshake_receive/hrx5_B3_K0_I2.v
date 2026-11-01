(* law handshake_receive, phase B3, branch kind 0, segment I2:
   the response block of stmt 6 (guard nk <> NULL, len > 92 given by hrx5_K0_M2): fill_resp(&t__1); k_response(&t__1, &nk->p->handshake, &itd, &id); t__1.header.type = 2; resp_img(buf, &t__1) (the world may change: use hrx5_B3_lem_stmt).
   States and statements: hrx5_B3_K0_defs.v. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_defs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_I2_lem.
Local Open Scope logic.

Section K0I2.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K0_I2_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K0_M2 x25519 gv L FR) hrx5_K0_I2
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K0_M2, hrx5_K0_Mc. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port B dp.
  unfold hrx5_K0_I2, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  assert (HLEM0 := HLEM). destruct HLEM0 as (HL1 & HL2 & HL3 & HL4 & HL5 & HL6).
  destruct (HL4 _ _ _ _ _ _ _ _ H0 H5) as (N & HN & HNa).
  destruct (HL3 _ _ _ _ _ _ _ _ _ H0 HN) as (P & HP & HPok & HPin).
  forward_call (Tsh, l_t1 L). Intros M0.
  sep_apply (hrx5_k0i2_node (hrx5_head NS) NS N (hn_p N) HN eq_refl). rewrite HNa.
  unfold peers_rep; rewrite (prot_rep3_split _ _ _ _ _ HP); cbn [peer_item_rep].
  Intros. assert_PROP (@field_compatible Noise.CS t_peer [] (hn_p N)) as HFC by (unfold peer_rep; entailer!).
  assert (HIDL := hrx5_k0i2_id_len x25519 R (proj1 HY) (proj1 H)).
  forward.
  { entailer!. apply isptr_is_pointer_or_null. exact (field_compatible_isptr _ _ _ HFC). }
  sep_apply (modus_ponens_wand (field_at Ews t_hnode4 (DOT HC._p) (hn_p N) nk) (hnodes_rep4 W (hrx5_head NS) NS)).
  forward_call (gv, S, w, Tsh, l_t1 L, M0, Ews, hn_p N, P, Tsh, l_itd L, T, Tsh, l_id L, hrx5_ID x25519 R).
  { exact (field_compatible_isptr _ _ _ HFC). }
  Intros vret. destruct vret as [[M1 b] idx]; cbn [fst snd] in *.
  rewrite hrx5_k0i2_resp_W. Intros. forward.
  set (M2 := mkRM (Int.repr 2) (rm_sender M1) (rm_receiver M1) (rm_eph M1) (rm_encn M1) (rm_mac1 M1)
                  (rm_mac2 M1)).
  assert (HM2: rm_ok M2) by exact H8.
  change (Vint (Int.repr 2), snd (resp_val M1)) with (resp_val M2).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_k0i2_resp_W Tsh (l_t1 L) M2))). { exact HM2. }
  unfold obj_rep. Intros. sep_apply (hrx5_k0i2_buf_split B dp). { lia. }
  forward_call (Ews, dp, Tsh, l_t1 L, M2). { cancel. }
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K0_M x25519 gv L FR) end.
  assert (HRL := hrx5_k0i2_resp_len M2 HM2).
  sep_apply (hrx5_k0i2_buf_join (resp_bytes M2) B dp HRL ltac:(lia)).
  set (B' := resp_bytes M2 ++ sublist 92 (Zlength B) B).
  assert (HBL: Zlength B' = Zlength B) by (subst B'; rewrite Zlength_app, Zlength_sublist; lia).
  destruct (hrx5_k0i2_world x25519 R L NS PS KE T head nk sec birth S (hn_p N) P b idx HLEM H H0 HP HPok)
    as (HW1 & HW2).
  set (P' := if b then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P) in *.
  set (c := (b && negb (vin (hs_addr (hn_p N)) (t_L T)))%bool) in *.
  unfold hrx5_K0_M, hrx5_K0_Mc.
  Exists R sec birth (if c then shim_u32 S idx else S) w NS (supd PS (hn_p N) P') (if c then t_insert T (hs_addr (hn_p N)) idx else T).
  Exists head nk KE st i kc lul q. Exists proto ip4 ip6 port B' dp.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  unfold peers_rep; rewrite (hrx5_k0i2_supd PS (hn_p N) Ews P P' _ HP); cbn [peer_item_rep].
  unfold obj_rep. rewrite HBL.
  unfold resp_rep. Intros.
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_resp (resp_val M2) (l_t1 L)).
  clear HL1 HL2 HL3 HL4 HL5 HL6 HLEM. entailer!.
  split.
  - unfold obj_ok in *. rewrite HBL. exact H3.
  - destruct c; reflexivity.
Qed.

End K0I2.
