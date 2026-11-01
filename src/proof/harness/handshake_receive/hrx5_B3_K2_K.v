(* law handshake_receive, phase B3, branch kind 2, segment K:
   if (nk != NULL && (nondet_u8() & 1)) k_response(mr, &nk->p->handshake, &itd, &id). *)
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
Local Open Scope logic.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K2_defs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K2_K_lem.

Section K2K.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Ltac k2k_fif id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx S))) end.
Ltac k2k_fifex id :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (EX v: int, PROPx P (LOCALx (temp id (Vint v) :: Q) (SEPx S))) end.

Ltac k2k_false :=
  exfalso; match goal with
  | H: false = true |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: ?x <> ?x |- _ => apply H; reflexivity
  | H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: 1 = 0 |- _ => discriminate H
  | H: typed_true _ _ |- _ => revert H; simpl; first [discriminate | intros X; inversion X | congruence]
  | H: typed_false _ _ |- _ => revert H; simpl; first [discriminate | intros X; inversion X | congruence]
  end.

Ltac k2k_pack0 := unfold hrx5_K2_F, hrx5_K2_St.
Ltac k2k_pack1 :=
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K2_XF; cbn [app]; entailer!.

Lemma hrx5_K2_K_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K2_F x25519 gv L FR) hrx5_K2_SK
    (overridePost (hrx5_K2_F x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K2_F at 1; unfold hrx5_K2_St at 1. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port mr img M IMG.
  unfold hrx5_K2_SK, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K2_XF; cbn [app].
  abbreviate_semax. Intros.
  assert (HLEM0 := HLEM). destruct HLEM0 as (HL1 & HL2 & HL3 & HL4 & HL5 & HL6).
  destruct (Val.eq nk nullval) as [En | En].
  - subst nk.
    k2k_fif HRM._t'57 (Vint Int.zero); [k2k_false | forward; entailer! |].
    forward_if; [k2k_false |].
    forward. k2k_pack0. Exists R sec birth S w NS PS T; Exists head nullval KE st i kc lul q.
    Exists proto ip4 ip6 port mr img M IMG. k2k_pack1.
  - destruct (HL4 _ _ _ _ _ _ _ _ H0 En) as (N & HN & HNa).
    destruct (HL3 _ _ _ _ _ _ _ _ _ H0 HN) as (P & HP & HPok & HPin).
    assert_PROP (isptr nk). { sep_apply (hrx5_k2k_isptr NS (hrx5_head NS) N HN). rewrite HNa. entailer!. }
    assert (VP: forall l, hnodes_rep4 W_handshake_receive l NS |-- valid_pointer nk)
      by (intros; rewrite <- HNa; apply hrx5_k2k_vp; auto).
    destruct nk as [| | | | | nb no]; try contradiction.
    k2k_fifex HRM._t'57.
    { forward_call tt. Intros b. forward.
      Exists (if Int.eq (Int.and (Int.repr b) (Int.repr 1)) Int.zero then Int.zero else Int.one).
      entailer!. }
    { k2k_false. }
    Intros v. forward_if.
    + sep_apply (hrx5_k2k_node (hrx5_head NS) NS N (hn_p N) HN eq_refl). rewrite HNa.
      unfold peers_rep; rewrite (prot_rep3_split _ _ _ _ _ HP); cbn [peer_item_rep].
      Intros. assert_PROP (@field_compatible Noise.CS t_peer [] (hn_p N)) as HFC by (unfold peer_rep; entailer!).
      forward.
      { entailer!. try (apply isptr_is_pointer_or_null; exact (field_compatible_isptr _ _ _ HFC)). }
      sep_apply (modus_ponens_wand (field_at Ews t_hnode4 (DOT HC._p) (hn_p N) (Vptr nb no)) (hnodes_rep4 W (hrx5_head NS) NS)).
      forward_call (gv, S, w, Ews, mr, M, Ews, hn_p N, P, Tsh, l_itd L, T, Tsh, l_id L, hrx5_ID x25519 R).
      { exact (field_compatible_isptr _ _ _ HFC). }
      { exact (hrx5_k2k_id_len x25519 R (proj1 HY) (proj1 H)). }
      Intros vret. destruct vret as [[M1 b] idx]; cbn [fst snd] in *.
      match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K2_F x25519 gv L FR) end.
      destruct (hrx5_k2k_world x25519 R L NS PS KE T head (Vptr nb no) sec birth S (hn_p N) P b idx HLEM H H0 HP HPok)
        as (HW1 & HW2).
      set (P' := if b then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P) in *.
      set (c := (b && negb (vin (hs_addr (hn_p N)) (t_L T)))%bool) in *.
      k2k_pack0.
      Exists R sec birth (if c then shim_u32 S idx else S) w NS (supd PS (hn_p N) P') (if c then t_insert T (hs_addr (hn_p N)) idx else T).
      Exists head (Vptr nb no) KE st i kc lul q. Exists proto ip4 ip6 port mr img M1 IMG.
      unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K2_XF; cbn [app].
      unfold peers_rep; rewrite (hrx5_k2k_supd PS (hn_p N) Ews P P' _ HP); cbn [peer_item_rep].
      clear HL1 HL2 HL3 HL4 HL5 HL6 HLEM. entailer!.
      destruct c; reflexivity.
    + forward. k2k_pack0. Exists R sec birth S w NS PS T; Exists head (Vptr nb no) KE st i kc lul q.
      Exists proto ip4 ip6 port mr img M IMG. k2k_pack1.
Qed.

End K2K.
