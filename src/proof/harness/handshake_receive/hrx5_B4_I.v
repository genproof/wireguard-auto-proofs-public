(* law handshake_receive, phase B4, segment I: statement 25 (the model block) for an initiation object OInit M: hrx5_B4_Q -> hrx5_S4. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_A.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_L.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_D.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_E1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_E2a.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_E2b.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_E3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_E4.
Local Open Scope logic.

Section B.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* if2 = if (t'97) body else els: els evaluates its conditions (kind 2, kind 3) to false for an initiation *)
Lemma hrx5_B4_I_B_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  (forall s key ck1 h1, hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
     semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
       (hrx5_B4_I_Q2 x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1) hrx5_B4_I_body
       (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR))) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Q1 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img) hrx5_B4_I_if2
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH HB.
  rewrite hrx5_B4_I_if2_eq.
  destruct (hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M) as [[[[s key] ck1] h1]|] eqn:Hc1.
  - specialize (HB s key ck1 h1 eq_refl).
    unfold hrx5_B4_I_Q1. rewrite Hc1. cbn [hrx5_B4_I_ok1].
    eapply semax_pre; [ | apply semax_ifthenelse_PQR' with (v := Vint Int.one)].
    all: unfold hrx5_B4_I_c97, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs; cbn [app].
    1: apply andp_left2, now_later.
    1: reflexivity.
    1: entailer!.
    1: entailer!.
    1: eapply semax_pre; [ | exact HB]; unfold hrx5_B4_I_Q2, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_ltemps, hrx5_ptrs,
         hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs; cbn [app]; Intros; entailer!.
    1: apply semax_extract_PROP; intro Hf; exfalso; cbv in Hf; discriminate Hf.
  - unfold hrx5_B4_I_Q1. rewrite Hc1. cbn [hrx5_B4_I_ok1 hrx5_B4_I_ci1].
    eapply semax_pre; [ | apply semax_ifthenelse_PQR' with (v := Vint Int.zero)].
    all: unfold hrx5_B4_I_c97, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs; cbn [app].
    1: apply andp_left2, now_later.
    1: reflexivity.
    1: entailer!.
    1: entailer!.
    1: apply semax_extract_PROP; intro Hf; exfalso; cbv in Hf; discriminate Hf.
    apply semax_extract_PROP; intros _.
    cbn [obj_kind]. unfold hrx5_B4_I_els, hrx5_Delta. simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if (temp HM._t'93 (Vint Int.zero)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if (temp HM._t'94 (Vint Int.zero)).
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    { forward. entailer!. }
    forward_if.
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                             | H: Int.zero <> Int.zero |- _ => apply H; reflexivity end. }
    forward_if (temp HM._t'92 (Vint Int.zero)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                             | H: Int.zero <> Int.zero |- _ => apply H; reflexivity end. }
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    pose proof (hrx5_B4_I_c1f_none x25519 aead_dec (hrx5_ID x25519 R) PS M (s_boot S) Hc1) as Hn.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OInit M) dp img nullval.
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore,
      hrx5_rest, hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OInit M) (s_boot S) nullval 0 0).
    { unfold hrx5_acc_ok. cbn [obj_bytes]. destruct (hrx5_fwd (init_bytes M)); [rewrite Hn |]; auto. }
    destruct (hrx5_fwd (init_bytes M)) eqn:Hfw; [rewrite Hn | ]; entailer!.
Qed.

End B.

Lemma hrx5_B4_I_ok : hrx5_B4_I_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img HH Ho.
  destruct o as [b | M | M | M]; try contradiction Ho. clear Ho.
  rewrite hrx5_B4_I_M_eq.
  eapply semax_seq.
  { rewrite overridePost_overridePost.
    eapply semax_pre; [ | apply (hrx5_B4_I_A_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img HH)].
    apply andp_left2. unfold hrx5_B4_Q, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_scr. apply derives_refl. }
  apply (hrx5_B4_I_B_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img HH).
  intros s key ck1 h1 Hc1.
  rewrite hrx5_B4_I_body_eq.
  eapply semax_seq; [ rewrite overridePost_overridePost; apply (hrx5_B4_I_L_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 HH Hc1) | ].
  apply (hrx5_B4_I_D_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 HH Hc1).
  intros a P Hpk.
  rewrite hrx5_B4_I_x_eq.
  eapply semax_seq; [ rewrite overridePost_overridePost; apply (hrx5_B4_I_E1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P HH Hc1 Hpk) | ].
  eapply semax_seq; [ | apply (hrx5_B4_I_E4_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P HH Hc1 Hpk) ].
  rewrite overridePost_overridePost.
  eapply semax_seq; [ | apply (hrx5_B4_I_E3_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P HH Hc1 Hpk) ].
  rewrite overridePost_overridePost.
  eapply semax_seq; [ | apply (hrx5_B4_I_E2b_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P HH Hc1 Hpk) ].
  rewrite overridePost_overridePost.
  apply (hrx5_B4_I_E2a_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P HH Hc1 Hpk).
Qed.
