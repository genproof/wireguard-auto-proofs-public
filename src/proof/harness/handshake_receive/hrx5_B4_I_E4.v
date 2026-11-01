(* law handshake_receive, phase B4, segment I, part E4:
   asg = `acc_init = t'81` and the final state S4 (hrx5_acc_ok OInit: fwd true, hrx5ci_tgt by hrx5_B4_I_tgt_some: accepted -> ai = 1, tg = hrx5_nfind NS a, ci_rep EX key spub (ci2's kdf2 / s); rejected -> ai = 0, tg = nfind NS a In (map hn_addr NS) (needs the found node: pk_find PS s = Some -> In (hrx5_nfind NS a) (map hn_addr NS), from hrx5_inv's hnodes_peers4), ci_rep data_at_; sst hbytes -> hout (hrx5_B4_I_hout)); the port of hci5_p7_E4 (which assigned target).
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

Lemma hrx5_B4_I_E4_inN : forall NS PS s a P, hnodes_peers4 NS PS -> pk_find PS s = Some (a, P) ->
  In (hrx5_nfind NS a) (map hn_addr NS).
Proof.
  unfold hnodes_peers4. induction NS as [|N NS IH]; intros PS s a P Hm Hf.
  - destruct PS; [discriminate | discriminate].
  - destruct PS as [|[[p sh] Q] PS]; [discriminate|].
    cbn [map] in Hm. injection Hm as Hp Hm. cbn [peer_addr4] in Hp.
    cbn [hrx5_nfind map]. destruct (eq_dec (hn_p N) a) as [E|E]; [left; reflexivity|].
    right. cbn [pk_find] in Hf. destruct (bytes_eqb (hs_rstatic (p_hs Q)) s).
    + injection Hf as Ha _. subst. contradiction.
    + eapply IH; eauto.
Qed.

Lemma hrx5_B4_I_E4_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Q8 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s ck1 h1 a P) hrx5_B4_I_asg
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1 Hpk.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hfwd Hc1'].
  destruct (hrx5_B4_I_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1') as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa).
  destruct (hrx5_B4_I_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlID & Hl1 & Hlpre & Hl2).
  pose proof (hrx5_B4_I_tgt_some x25519 aead_dec (hrx5_ID x25519 R) PS M (s_boot S) _ _ _ _ _ _ Hc1' Hpk) as Htg.
  unfold hrx5_B4_I_Q8, hrx5_B4_I_st, hrx5_B4_I_ci2, hrx5_B4_I_b15, hrx5_B4_I_scr, hrx5_B4_I_asg. cbn [app].
  set (SS := hrx5_B4_I_SS x25519 (hrx5_ID x25519 R) P) in *.
  assert (HlSS: Zlength SS = 32) by apply Hlpre.
  Intros.
  pose proof H0 as Hinv. destruct H0 as (Hi1 & Hi2 & Hi3 & Hi4 & Hnp & Hi6).
  pose proof (hrx5_B4_I_E4_inN NS PS s a P Hnp Hpk) as HinN.
  destruct (hrx5_B4_I_c2v aead_dec SS ck1 h1 M) as [[[t ck2] h2]|] eqn:H2m; cbv beta iota in *.
  1: destruct ((ts_newer t (hs_ts (p_hs P)) && not_flood (hs_lic (p_hs P)) (s_boot S))%bool) eqn:Hacc.
  all: cbv beta iota in *.
  all: unfold hrx5_Delta; simplify_func_tycontext; unfold hrx5_ltemps, hrx5_ptrs, hrx5_lvars; cbn [app obj_kind].
  all: forward.
  all: match goal with |- _ |-- ?X => change X with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
  all: unfold hrx5_S4; Exists R sec birth S w NS PS T; Exists head nk KE st i kc lul q;
       Exists proto ip4 ip6 port (OInit M) dp img (hrx5_nfind NS a).
  1: Exists 1 0.
  2,3: Exists 0 0.
  all: unfold hrx5_scr4, hrx5_acc_ok, hrx5_ci_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars;
       cbn [obj_bytes obj_kind app hrx5_st_rep hrx5_pt_rep]; rewrite Hfwd, Htg.
  - assert (Hls: Zlength s = 32).
    { cbn [obj_ok] in H3. destruct H3 as (_ & He & _). exact (proj1 (Hl1 _ _ _ s key ck1 h1 He H1m)). }
    entailer!.
    rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon].
    sep_apply (hrx5_B4_I_hout SS (l_sst L) HlSS).
    Exists (bytes (kdf2 ck1 SS)) (bytes s).
    entailer!.
    + unfold bytes. rewrite Zlength_map. exact Hls.
    + apply derives_refl.
  - entailer!.
    rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon].
    sep_apply (hrx5_B4_I_hout SS (l_sst L) HlSS).
    sep_apply (@data_at_data_at_ HCS Tsh t_mcinit (mcinit_val ck2 h2 (bytes (kdf2 ck1 SS)) (bytes s) (bytes t)) (l_ci L)).
    cancel. all: try apply derives_refl.
  - cbn [andb]. entailer!.
    rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon].
    sep_apply (hrx5_B4_I_hout SS (l_sst L) HlSS).
    cancel. all: try apply derives_refl.
Qed.

End Seg.
