(* law replay: the loop body, segment L1 (kind = nondet_u8() % 3; kind 0: fill_init, draw_real_clock,
   create_initiation (continue on failure), add_mac, copy_init(sent, m), have_sent = 1; kind 1: continue
   unless have_sent, copy_init(m, sent); kind 2: continue unless have_accepted, copy_init(m, accepted)).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

Lemma hrp3_segL1_mods3 ub : 0 <= ub <= Byte.max_unsigned ->
  Int.mods (Int.repr ub) (Int.repr 3) = Int.repr (ub mod 3).
Proof.
  intros Hb. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

(* the message after add_mac: mac1 / mac2 replaced *)
Definition hrp3_segL1_M2 (C: cookie) (M: init_msg) (now: int64) : init_msg :=
  let r := fst (add_mac_model C (init_bytes M) now) in
  mkIM (im_type M) (im_sender M) (im_eph M) (im_encs M) (im_enct M) (sublist 116 132 r) (sublist 132 148 r).

Lemma hrp3_segL1_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hrp3_segL1_MAC_len k m : Zlength (MAC k m) = 16.
Proof. unfold MAC, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hrp3_segL1_init_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (L1&L2&L3&L4&L5). unfold init_bytes. rewrite !Zlength_app, !hrp3_segL1_le32_len. lia.
Qed.

Lemma hrp3_segL1_addmac (C: cookie) (M: init_msg) (now: int64) : im_ok M ->
  fst (add_mac_model C (init_bytes M) now) = init_bytes (hrp3_segL1_M2 C M now) /\
  im_ok (hrp3_segL1_M2 C M now).
Proof.
  intros HM. pose proof (hrp3_segL1_init_len M HM) as LM.
  assert (HP: init_bytes M = (le32 (im_type M) ++ le32 (im_sender M) ++ im_eph M ++ im_encs M ++ im_enct M) ++
                             im_mac1 M ++ im_mac2 M) by (unfold init_bytes; rewrite !app_assoc; reflexivity).
  destruct HM as (L1&L2&L3&L4&L5).
  set (pre := le32 (im_type M) ++ le32 (im_sender M) ++ im_eph M ++ im_encs M ++ im_enct M) in HP.
  assert (Lpre: Zlength pre = 116) by (unfold pre; rewrite !Zlength_app, !hrp3_segL1_le32_len; lia).
  assert (Hr: exists m1 m2, Zlength m1 = 16 /\ Zlength m2 = 16 /\
            fst (add_mac_model C (init_bytes M) now) = pre ++ m1 ++ m2).
  { unfold add_mac_model. cbv zeta. cbn [fst]. rewrite LM.
    set (m1 := mac1_of (ck_mkey C) (init_bytes M)).
    assert (Lm1: Zlength m1 = 16) by (unfold m1, mac1_of; apply hrp3_segL1_MAC_len).
    match goal with |- context [if ?b then ?x else ?y] => set (m2 := if b then x else y) end.
    assert (Lm2: Zlength m2 = 16) by (unfold m2; destruct (andb _ _); [unfold mac2_of; apply hrp3_segL1_MAC_len | reflexivity]).
    clearbody m1 m2. exists m1, m2. split; [exact Lm1 | split; [exact Lm2 |]].
    rewrite HP. clearbody pre. list_solve. }
  destruct Hr as (m1 & m2 & Lm1 & Lm2 & Hr).
  unfold hrp3_segL1_M2. cbv zeta. rewrite Hr.
  assert (E1: sublist 116 132 (pre ++ m1 ++ m2) = m1) by list_solve.
  assert (E2: sublist 132 148 (pre ++ m1 ++ m2) = m2) by list_solve.
  rewrite E1, E2. split.
  - unfold init_bytes. cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2]. unfold pre. rewrite !app_assoc. reflexivity.
  - unfold im_ok. cbn [im_eph im_encs im_enct im_mac1 im_mac2]. auto.
Qed.

Lemma hrp3_segL1_rep_ sh p M : init_rep sh p M |-- @data_at_ Noise.CS sh t_init p.
Proof. unfold init_rep. Intros. apply data_at_data_at_. Qed.

Lemma hrp3_segL1_ifrep_ (b: bool) sh p M :
  (if b then init_rep sh p M else @data_at_ Noise.CS sh t_init p) |-- @data_at_ Noise.CS sh t_init p.
Proof. destruct b; [apply hrp3_segL1_rep_ | apply derives_refl]. Qed.

Lemma hrp3_segL1_peer_open sh p P C' :
  peer_rep sh p P |--
  (!! (@field_compatible Noise.CS t_peer [] p) &&
   (cookie_rep sh (cookie_addr p) (p_cookie P) *
    (cookie_rep sh (cookie_addr p) C' -* peer_rep sh p (p_set_cookie P C'))))%logic.
Proof.
  unfold peer_rep at 1. Intros. apply andp_right; [apply prop_right; auto |].
  match goal with |- ?a1 * ?a2 * ?a3 * ?a4 * ?a5 * ?ck * ?a6 * ?a7 * ?a8 * ?a9 * ?a10 |-- _ =>
    apply derives_trans with (ck * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10))%logic; [cancel |] end.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. unfold peer_rep, p_set_cookie.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Ltac hrp3_segL1_ff :=
  exfalso; first [ match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end
                 | match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end ].

Ltac hrp3_segL1_cont R Y' :=
  unfold loop1_ret_assert; destruct R as [?Rn ?Rb ?Rc ?Rr]; cbn [tycontext.RA_continue];
  unfold hrp3_Icont, hrp3_St; Exists Y';
  unfold hrp3_world, hrp3_globs, hrp3_mbuf, hrp3_temps, hrp3_lvars; cbn [app].

Lemma hrp3_segL1_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) V sp ap mp steps i R :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec)
    (EX Y: hrp3_dyn, hrp3_St x25519 aead_dec F V sp ap mp steps FR (0 <= i < steps) i Y) hrp3_segL1
    (overridePost (hrp3_PL1 x25519 aead_dec F V sp ap mp steps FR i)
       (loop1_ret_assert (hrp3_Icont x25519 aead_dec F V sp ap mp steps FR i) R)).
Proof.
  intros HF HX HA.
  unfold hrp3_St, hrp3_Delta, hrp3_lvars, hrp3_segL1, hrp3_temps.
  Intros Y.
  abbreviate_semax.
  unfold hrp3_world, hrp3_globs; cbn [app].
  forward_call tt. Intros ub.
  forward.
  { entailer!. match goal with Hx: _ /\ Int.repr 3 = Int.mone |- _ => destruct Hx as [_ Hx]; discriminate Hx end. }
  rewrite (hrp3_segL1_mods3 ub H3).
  assert (Hk: 0 <= ub mod 3 <= 2) by (pose proof (Z.mod_pos_bound ub 3); lia).
  set (kind := ub mod 3) in *.
  unfold hrp3_mbuf at 1 2 3. Intros.
  forward_if.
  { assert_PROP (@field_compatible Noise.CS t_init [] mp) as FCm by entailer!.
    forward_call (Ews, mp). Intros M0.
    forward_call (f_gv F, y_S Y). Intros vr. destruct vr as [sec ns].
    set (S1 := shim_set_real (y_S Y) (fst (sec, ns)) (Int64.repr (snd (sec, ns)))).
    destruct HF as (HM & HR & HC).
    pose proof (HM x25519 aead_enc aead_dec) as HM'.
    destruct HM' as (_ & _ & _ & _ & Hins & Hpool & Hsid & _).
    pose proof H1 as (Hta & Hdev & Hhsid & Hpa & Hlat & Hlast & Hnow & Hacc).
    change (itable Tsh (f_ita F) (y_TA Y)) with (itable Tsh (d_itab (hrp3_DA x25519 F V)) (y_TA Y)).
    forward_call (f_gv F, S1, v_kc V, Ews, mp, M0, Tsh, f_pb F, y_PB Y, Tsh, f_wa F, hrp3_DA x25519 F V, Tsh, y_TA Y).
    Intros vr. destruct vr as [r idx].
    change (fst (r, idx)) with r in *. change (snd (r, idx)) with idx in *.
    pose proof (Hsid (hrp3_DA x25519 F V) (y_PB Y) M0 S1 r idx) as Hsid1.
    destruct (ci_res x25519 aead_enc (hrp3_DA x25519 F V) (y_PB Y) M0 S1 r idx) as [[b M1] H'] eqn:ECI.
    cbn [fst snd] in *.
    change (d_itab (hrp3_DA x25519 F V)) with (f_ita F).
    set (S2 := if id_has (d_id (hrp3_DA x25519 F V)) then _ else S1).
    destruct b.
    2: { forward_if. 2: { hrp3_segL1_ff. }
         forward.
         set (Y' := mkRDyn S2 (y_TA Y) (p_set_hs (y_PB Y) H') (y_PA Y) (y_latest Y) (y_last Y) (y_now Y)
                           (y_hs Y) (y_Ms Y) (y_ha Y) (y_Ma Y)).
         assert (Hinv: hrp3_inv x25519 aead_dec F V Y').
         { unfold hrp3_inv, Y'; cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma p_set_hs p_device p_hs].
           rewrite Hsid1. auto 10. }
         sep_apply (hrp3_segL1_rep_ Ews mp M1).
         hrp3_segL1_cont R Y'.
         change (y_S Y') with S2. change (y_TA Y') with (y_TA Y). change (y_PB Y') with (p_set_hs (y_PB Y) H').
         change (y_PA Y') with (y_PA Y). change (y_latest Y') with (y_latest Y). change (y_last Y') with (y_last Y).
         change (y_now Y') with (y_now Y). change (y_hs Y') with (y_hs Y). change (y_Ms Y') with (y_Ms Y).
         change (y_ha Y') with (y_ha Y). change (y_Ma Y') with (y_Ma Y).
         entailer!. }
    forward_if. { hrp3_segL1_ff. }
    assert_PROP (im_ok M1) as HM1 by (unfold init_rep; entailer!).
    sep_apply (proj1 HR Ews mp M1).
    set (C0 := p_cookie (p_set_hs (y_PB Y) H')).
    set (C' := snd (add_mac_model C0 (init_bytes M1) (s_boot S2))).
    sep_apply (hrp3_segL1_peer_open Tsh (f_pb F) (p_set_hs (y_PB Y) H') C'). Intros.
    pose proof (hrp3_segL1_init_len M1 HM1) as LM1.
    fold C0.
    forward_call (f_gv F, S2, Ews, mp, init_bytes M1, Tsh, f_pb F, C0).
    { entailer!. rewrite LM1. reflexivity. }
    fold C'.
    destruct (hrp3_segL1_addmac C0 M1 (s_boot S2) HM1) as [EM2 HM2].
    rewrite EM2.
    set (M2 := hrp3_segL1_M2 C0 M1 (s_boot S2)) in *.
    sep_apply (proj1 (proj2 HR) Ews mp M2 FCm HM2).
    sep_apply (wand_frame_elim (cookie_rep Tsh (cookie_addr (f_pb F)) C')
                 (peer_rep Tsh (f_pb F) (p_set_cookie (p_set_hs (y_PB Y) H') C'))).
    sep_apply (hrp3_segL1_ifrep_ (y_hs Y) Ews sp (y_Ms Y)).
    forward_call (Ews, sp, Ews, mp, M2).
    forward.
    set (Y' := mkRDyn S2 (t_insert (y_TA Y) (hs_addr (f_pb F)) idx) (p_set_cookie (p_set_hs (y_PB Y) H') C')
                      (y_PA Y) (y_latest Y) (y_last Y) (y_now Y) true M2 (y_ha Y) (y_Ma Y)).
    assert (Hinv: hrp3_inv x25519 aead_dec F V Y').
    { unfold hrp3_inv, Y'; cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma p_set_hs p_set_cookie
                                p_device p_hs].
      rewrite Hsid1. auto 10. }
    unfold loop1_ret_assert; destruct R as [Rn Rb Rc Rr]; cbn [tycontext.RA_normal].
    unfold hrp3_PL1. Exists Y' M2 kind.
    unfold hrp3_world, hrp3_globs, hrp3_mbuf, hrp3_temps, hrp3_lvars; cbn [app].
    change (y_S Y') with S2. change (y_TA Y') with (t_insert (y_TA Y) (hs_addr (f_pb F)) idx).
    change (y_PB Y') with (p_set_cookie (p_set_hs (y_PB Y) H') C').
    change (y_PA Y') with (y_PA Y). change (y_latest Y') with (y_latest Y). change (y_last Y') with (y_last Y).
    change (y_now Y') with (y_now Y). change (y_hs Y') with true. change (y_Ms Y') with M2.
    change (y_ha Y') with (y_ha Y). change (y_Ma Y') with (y_Ma Y).
    entailer!. }
  forward_if.
  { destruct (y_hs Y) eqn:Hhs.
    - forward_if. { hrp3_segL1_ff. }
      forward_call (Ews, mp, Ews, sp, y_Ms Y).
      unfold loop1_ret_assert; destruct R as [Rn Rb Rc Rr]; cbn [tycontext.RA_normal].
      unfold hrp3_PL1. Exists Y (y_Ms Y) kind.
      unfold hrp3_world, hrp3_globs, hrp3_mbuf, hrp3_temps, hrp3_lvars; cbn [app]. rewrite Hhs.
      entailer!.
    - forward_if. 2: { hrp3_segL1_ff. }
      forward. hrp3_segL1_cont R Y. rewrite Hhs. entailer!. }
  assert (Hk2: kind = 2) by lia.
  destruct (y_ha Y) eqn:Hha.
  - forward_if. { hrp3_segL1_ff. }
    forward_call (Ews, mp, Ews, ap, y_Ma Y).
    unfold loop1_ret_assert; destruct R as [Rn Rb Rc Rr]; cbn [tycontext.RA_normal].
    unfold hrp3_PL1. Exists Y (y_Ma Y) kind.
    unfold hrp3_world, hrp3_globs, hrp3_mbuf, hrp3_temps, hrp3_lvars; cbn [app]. rewrite Hha.
    entailer!.
  - forward_if. 2: { hrp3_segL1_ff. }
    forward. hrp3_segL1_cont R Y. rewrite Hha. entailer!.
Qed.
