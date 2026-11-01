(* law handshake_receive: B8 branch R segment D, part S8:
   CHECK(pr_same(&target->rest, target->p)) from hrx5_B8R_RB to hrx5_B8R_RB (hrx5_B8_R_defs.v).  The statement is
   Port: B8 branch C part T. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_s8_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_s8_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RD_s8_ok : hrx5_B8R_seg hrx5_B8R_RB hrx5_B8R_RB hrx5_B8RD_s8 false.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8R_RB hrx5_B8R_St hrx5_B8R_F hrx5_B8R_facts].
  cbn [app fold_right].
  unfold hrx5_Delta, hrx5_B8RD_s8, hrx5_rest, hrx5_cglobs; cbn [app].
  simplify_func_tycontext. abbreviate_semax.
  Intros.
  match goal with |- context [rxw_rep W gv Tsh (l_wd L) head ?X] => set (Wx := X) end.
  set (Pf := hrx5_B8R_Pf d P M ck h).
  assert (EPS: rw_PS Wx = supd PS a Pf) by reflexivity.
  assert (EPf: p_device Pf = p_device P /\ p_cur Pf = p_cur P /\ p_prev Pf = p_prev P /\
               p_next Pf = p_next P /\ p_pknext Pf = p_pknext P)
    by (unfold Pf, hrx5_B8R_Pf, hrx5cr_new; destruct (hrx5_B8R_alloc d); repeat split; reflexivity).
  destruct EPf as (E1 & E2 & E3 & E4 & E5).
  destruct (hrx5_B8RDs8_pure x25519 R L NS PS KE T head nk a P Pf j (rw_D Wx) H0 H12 H13 H14 E1 E2 E3 E4 E5)
    as (N & NS1 & NS2 & PS1 & PS2 & HNS & HNa & HNp & HNrest & HPS' & Hvo & Hvp).
  unfold rxw_rep at 1. rewrite EPS.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5; cbn [app]. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as Hfcn.
  { rewrite HNS. sep_apply (hrx5_B8RDs8_node NS1 N NS2 (hrx5_head (NS1 ++ N :: NS2))). Intros nx. entailer!. }
  assert (Etg: tg = hn_addr N) by congruence.
  rewrite Etg.
  freeze FR0 := - (device_rep _ _ _) (peers_rep _) (hnodes_rep4 _ _ _).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hrx5_B8RDs8_node' _ NS1 N NS2 (hrx5_head (hnodes_snapped4 T NS PS)) HNS). Intros nx.
    unfold hrx5_B8RDs8_flds. Intros.
    rewrite HPS', hrx5_B8RDs8_papp. unfold peer_item_rep. Intros.
    rewrite HNp.
    assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca.
    { unfold peer_rep. Intros. entailer!. }
    assert (Hpa: isptr a) by exact (@field_compatible_isptr Noise.CS _ _ _ Hfca).
    forward.
    rewrite (hrx5_B8RDs8_rest N P (hn_addr N) Hfcn HNrest).
    sep_apply (derives_refl' _ _ (hrx5_B8RDs8_vo L (rw_D Wx) (PS1 ++ PS2))).
    forward_call (Ews, offset_val 304 (hn_addr N), P, Ews, a, Pf, hrx5_B8RDs8_VO L (rw_D Wx) (PS1 ++ PS2)).
    rewrite (hrx5_B8RDs8_pr_eqb d P M ck h : pr_eqb P Pf = true).
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_B8RDs8_vo L (rw_D Wx) (PS1 ++ PS2)))). Intros.
    rewrite <- (hrx5_B8RDs8_rest N P (hn_addr N) Hfcn HNrest).
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    change (peer_rep Ews a Pf) with (peer_item_rep (a, Ews, Pf)).
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_B8RDs8_papp PS1 (a, Ews, Pf) PS2))).
    rewrite HPS'.
    entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate, overridePost. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
  cbn [RA_normal]. thaw FR0. rewrite <- Etg.
  fold Wx. unfold rxw_rep at 1. rewrite EPS.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5; cbn [app]. repeat flatten_sepcon_in_SEP.
  go_lower.
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7
       (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 _))))))))))))))))));
     repeat split; rewrite ?eqb_type_refl; reflexivity |].
  cancel.
Qed.