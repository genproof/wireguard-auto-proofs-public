(* law handshake_receive, phase B4, segment C: statement 25 (the model block) for a cookie-reply object OCookie M: hrx5_B4_Q -> hrx5_S4. *)
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

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_W.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_N.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_D.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_G.
Local Open Scope logic.

(* node addresses are pointers *)
Lemma hrx5_B4_C_nodes_ptr l NS : hnodes_rep4 W l NS |-- !! Forall (fun N => isptr (hn_addr N)) NS.
Proof.
  revert l; induction NS as [|N NS IH]; intros l; simpl.
  - entailer!.
  - Intros nx. sep_apply (IH nx). Intros. entailer!.
    constructor; [destruct H2 as [Hp _]; exact Hp | assumption].
Qed.

Lemma hrx5_B4_C_snap_ptr T NS PS : length NS = length PS ->
  Forall (fun N => isptr (hn_addr N)) (hnodes_snapped4 T NS PS) -> Forall (fun N => isptr (hn_addr N)) NS.
Proof.
  unfold hnodes_snapped4. revert PS; induction NS as [|N NS IH]; intros [|x PS] Hl HF; simpl in *; try discriminate.
  - constructor.
  - inversion HF; subst. constructor.
    + destruct x as [[p sh] P]. exact H1.
    + apply (IH PS); [lia | exact H2].
Qed.

Ltac hrx5_B4_C_ent :=
  cbv beta iota delta [hrx5_RB loop1_ret_assert overridePost hrx5_R frame_ret_assert function_body_ret_assert
                       RA_break RA_normal]; entailer!.
Ltac hrx5_B4_C_absurd :=
  exfalso; first
  [ discriminate
  | match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end
  | match goal with H: Int.repr 0 <> Int.zero |- _ => exact (H eq_refl) end
  | match goal with H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H) end
  | match goal with H: Int.zero = Int.one |- _ => exact (Int.one_not_zero (eq_sym H)) end ].

Section C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the facts the glue needs from a state *)
Lemma hrx5_B4_C_st_facts gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img tl tg ptR :
  hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img tl tg ptR
  |-- !! (hrx5_inv x25519 R L NS PS KE T head nk /\ Forall (fun N => isptr (hn_addr N)) NS).
Proof.
  unfold hrx5_B4_C_st, hrx5_rest. cbn [app].
  unfold PROPx; apply derives_extract_prop; cbn [fold_right]; intros (_ & Hinv & _).
  unfold LOCALx; apply andp_left2. unfold SEPx. intro rho.
  match goal with |- _ |-- ?X =>
    change X with (!! (hrx5_inv x25519 R L NS PS KE T head nk /\ Forall (fun N => isptr (hn_addr N)) NS)) end.
  rewrite !fold_right_sepcon_app. cbn [fold_right_sepcon].
  sep_apply (hrx5_B4_C_nodes_ptr (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)).
  Intros. apply prop_right. split; [exact Hinv|].
  destruct Hinv as (_ & _ & _ & _ & Hnp & _). eapply hrx5_B4_C_snap_ptr; [|eassumption].
  unfold hnodes_peers4 in Hnp. rewrite <- (map_length hn_p NS), Hnp, map_length. reflexivity.
Qed.

(* the body for fwd: W; N; D (or nothing for a NULL target) *)
Lemma hrx5_B4_C_body_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port
  M dp img :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
       [] nullval (hout Tsh 16 (l_pt L)))
    (Ssequence hrx5_B4_C_sW (Ssequence hrx5_B4_C_sN hrx5_B4_C_sD))
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH.
  eapply semax_seq; [ rewrite overridePost_overridePost;
    apply (hrx5_B4_C_W_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i
             kc lul q proto ip4 ip6 port M dp img HH) | ].
  eapply semax_seq; [ rewrite overridePost_overridePost;
    apply (hrx5_B4_C_N_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i
             kc lul q proto ip4 ip6 port M dp img HH) | ].
  eapply semax_pre_simple; [apply andp_right; [apply andp_left2, hrx5_B4_C_st_facts | apply andp_left2, derives_refl] |].
  apply semax_extract_prop. intros [Hinv Hptr].
  destruct (hrx5_B4_C_G_ok x25519 xaead_dec R L NS PS KE T head nk M Hinv Hptr) as [G1 G2].
  destruct (eq_dec (hrx5_B4_C_t0 NS T M) nullval) as [H0|H0].
  2: { destruct (G2 H0) as (a & E & P & NS1 & N & NS2 & Hl & Hs & Hn & Ha & Hr).
       assert (Ht: hrx5_B4_C_t0 NS T M = hn_addr N) by (unfold hrx5_B4_C_t0; rewrite Hl; auto).
       rewrite Ht.
       apply (hrx5_B4_C_D_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk
                KE st i kc lul q proto ip4 ip6 port M dp img a E P NS1 N NS2 HH Hl Hs Hn Ha Hr). }
  specialize (G1 H0). rewrite H0.
  unfold hrx5_B4_C_st, hrx5_B4_C_scr, hrx5_Delta, hrx5_RB, hrx5_B4_C_sD, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore,
    hrx5_rest, hrx5_globs.
  cbn [app obj_bytes obj_kind obj_rep obj_ok]. simplify_func_tycontext. abbreviate_semax.
  Intros.
  forward_if (temp HM._t'90 (Vint Int.zero)).
  { exfalso. discriminate. }
  { forward. entailer!. }
  forward_if.
  { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
  forward.
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
  unfold hrx5_S4.
  Exists R sec birth S w NS PS T.
  Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port (OCookie M) dp img nullval.
  Exists 0 0.
  unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
    hrx5_globs.
  cbn [app obj_bytes obj_kind].
  assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OCookie M) (s_boot S) nullval 0 0).
  { unfold hrx5_acc_ok. cbn [obj_bytes]. rewrite H5, G1. auto. }
  rewrite H5, G1. entailer!.
  unfold obj_rep. cancel.
Qed.

End C.

Lemma hrx5_B4_C_ok : hrx5_B4_C_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img HH Ho.
  destruct o as [b | M | M | M]; try contradiction Ho. clear Ho.
  assert (HB := hrx5_B4_C_body_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk
                  KE st i kc lul q proto ip4 ip6 port M dp img HH).
  rewrite hrx5_B4_C_M_eq.
  unfold hrx5_B4_Q, hrx5_Delta, hrx5_B4_C_a1, hrx5_B4_C_c97, hrx5_B4_C_a2, hrx5_B4_C_c94, hrx5_B4_C_a3, hrx5_B4_C_c92,
    hrx5_ltemps, hrx5_ptrs, hrx5_lvars.
  cbn [app obj_bytes obj_kind obj_ok]. simplify_func_tycontext. abbreviate_semax.
  Intros.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  destruct (hrx5_fwd (cookie_msg_bytes M)) eqn:Hfw.
  all: forward_if (temp HM._t'95 (Vint Int.zero)); [ forward; hrx5_B4_C_ent | forward; hrx5_B4_C_ent | ].
  all: forward_if (temp HM._t'96 (Vint Int.zero)); [ hrx5_B4_C_absurd | forward; hrx5_B4_C_ent | ].
  all: forward_if (temp HM._t'97 (Vint Int.zero)); [ hrx5_B4_C_absurd | forward; hrx5_B4_C_ent | ].
  all: forward_if; [ hrx5_B4_C_absurd | ].
  all: forward_if (temp HM._t'93 (Vint Int.zero)); [ forward; hrx5_B4_C_ent | forward; hrx5_B4_C_ent | ].
  all: forward_if (temp HM._t'94 (Vint Int.zero)); [ hrx5_B4_C_absurd | forward; hrx5_B4_C_ent | ].
  all: forward_if; [ hrx5_B4_C_absurd | ].
  - (* fwd: the body *)
    forward_if (temp HM._t'92 (Vint Int.one)); [ forward; hrx5_B4_C_ent | hrx5_B4_C_absurd | ].
    forward_if; [ | hrx5_B4_C_absurd ].
    eapply semax_pre; [ | exact HB ].
    unfold hrx5_B4_C_st, hrx5_B4_C_scr, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs.
    cbn [app obj_bytes obj_kind obj_ok]. rewrite Hfw. entailer!.
  - (* not fwd: nothing *)
    forward_if (temp HM._t'92 (Vint Int.zero)); [ hrx5_B4_C_absurd | forward; hrx5_B4_C_ent | ].
    forward_if; [ hrx5_B4_C_absurd | ].
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OCookie M) dp img nullval.
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
      hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OCookie M) (s_boot S) nullval 0 0).
    { unfold hrx5_acc_ok. cbn [obj_bytes]. rewrite Hfw. auto. }
    rewrite Hfw. entailer!.
Qed.
