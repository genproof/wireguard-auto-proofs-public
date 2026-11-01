(* law handshake_receive, phase B4, segment I, part D:
   ifp = `if (target != NULL) x` (port of hci5_p7_D): not found (pk_find PS s = None, hrx5_B4_I_after_ok: target = NULL) -> skip and the final state S4 (hrx5_acc_ok: OInit case, fwd true (hrx5_B4_I_c1f_some), hrx5ci_tgt = None by hrx5_B4_I_tgt_none2, ai = 0, tg = nullval; ci_rep None: data_at_); found -> the premise after rewriting target to hrx5_nfind NS a.
*)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_defs.
Local Open Scope logic.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B4_I_D_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  (forall a P, pk_find PS s = Some (a, P) ->
     semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
       (hrx5_B4_I_Qf x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a) hrx5_B4_I_x
       (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR))) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Qb x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1) hrx5_B4_I_ifp
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1 HX.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hfwd Hc1'].
  unfold hrx5_B4_I_Qb, hrx5_B4_I_st, hrx5_B4_I_ifp, hrx5_B4_I_ci1, hrx5_B4_I_scr. cbn [app].
  Intros.
  destruct (hrx5_B4_I_after_ok x25519 R L NS PS KE T head nk H0) as (Hpe & Hsh & Hnone & Hsome).
  destruct (pk_find PS s) as [[a P]|] eqn:Hpk.
  2: {
    rewrite (Hnone s Hpk). cbn [hrx5_B4_I_fmv].
    unfold hrx5_Delta. simplify_func_tycontext.
    unfold hrx5_ltemps, hrx5_ptrs, hrx5_lvars; cbn [app obj_kind].
    forward_if. 1: { hrx5_B4_I_absurd. }
    forward.
    match goal with |- _ |-- ?X => change X with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4. Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OInit M) dp img nullval. Exists 0 0.
    pose proof (hrx5_B4_I_tgt_none2 x25519 aead_dec _ PS _ (s_boot S) _ _ _ _ Hc1' Hpk) as Htg.
    unfold hrx5_scr4, hrx5_acc_ok, hrx5_ci_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars.
    cbn [obj_bytes obj_kind app hrx5_st_rep hrx5_pt_rep]. rewrite Hfwd, Htg.
    entailer!.
    rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon]. cancel. }
  destruct (Hsome s a P Hpk) as (NS1 & N & NS2 & P' & sn & Hfm & HNS & HinP & Hnf & Hrest).
  rewrite Hfm. cbn [hrx5_B4_I_fmv].
  assert (HinN: In (hn_addr N) (map hn_addr (hnodes_snapped4 T NS PS))).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  pose proof (hrx5_B4_I_hn_valid (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) (hn_addr N) HinN) as HvN.
  unfold hrx5_rest, hrx5_ltemps, hrx5_ptrs, hrx5_lvars. cbn [app obj_kind].
  assert_PROP (Forall isptr (map hn_addr (hnodes_snapped4 T NS PS))) as Hptrs.
  { go_lower. rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon].
    sep_apply (hrx5_B4_I_hn_isptr (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  assert (HpNa: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
  specialize (HX a P eq_refl).
  eapply semax_pre; [ | apply semax_ifthenelse_PQR' with (v := Vint Int.one)].
  - apply andp_left2, now_later.
  - reflexivity.
  - entailer!.
    rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon]. apply denote_tc_test_eq_split. 2: auto with valid_pointer.
    eapply derives_trans; [|apply sepcon_valid_pointer1 with (Q := TT); exact HvN]. cancel.
  - entailer!. destruct (hn_addr N); try contradiction. reflexivity.
  - eapply semax_pre; [ | exact HX ].
    unfold hrx5_B4_I_Qf, hrx5_B4_I_st, hrx5_B4_I_ci1, hrx5_B4_I_scr, hrx5_rest, hrx5_ltemps, hrx5_ptrs, hrx5_lvars.
    cbn [app obj_kind].
    rewrite <- Hnf. Intros. entailer!.
  - Intros. hrx5_B4_I_absurd.
Qed.

End Seg.
