(* law handshake_receive, B8 branch R segment A: the core of the segment, over an
   abstract frame Fr and generic local values (the kernel never sees the full state). *)
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_A_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_A_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RA_warn_refl w : warn_eqb w w = true.
Proof. unfold warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hrx5_B8RA_dead' N P l : hn_rest N = prsnap_val P ->
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l |--
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._rest DOT HC._is_dead) (Val.of_bool (p_dead P)) l *
  (@field_at W_handshake_receive Ews t_hnode4 (DOT HC._rest DOT HC._is_dead) (Val.of_bool (p_dead P)) l -*
   @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l).
Proof. intros E. rewrite E. apply hrx5_B8RA_dead. Qed.

(* the locals of the segment's states (hrx5_B8R_St with no temps of the branch), over generic values *)
Definition hrx5_B8RA_L (gv: globals) (L: hrx5_loc)
  (nk kes st i now mlul buf mi mr mc img len kind ai ar tg h0 path: val) : list localdef :=
  [temp HM._nk nk; temp HM._kes kes; temp HM._steps st; temp HM._i i; temp HM._now now; temp HM._m_lul mlul;
   temp HM._buf buf; temp HM._mi mi; temp HM._mr mr; temp HM._mc mc; temp HM._img img; temp HM._len len;
   temp HM._kind kind; temp HM._acc_init ai; temp HM._acc_resp ar; temp HM._target tg; temp HM._head0 h0;
   temp HM._path path] ++ hrx5_lvars gv L.

Definition hrx5_B8RA_new (a tg: val) (d: rxdraw) (P: peer) : list localdef :=
  [temp HM._h__2 (hs_addr a); temp HM._s__1 (offset_val 8 tg);
   temp HM._alloc_ok (Vint (if hrx5_B8R_alloc d then Int.one else Int.zero));
   temp HM._session (Vint (if hrx5_B8R_sess d P then Int.one else Int.zero));
   temp HM._hashed (Vlong (Int64.repr 0))].

Definition hrx5_B8RA_core_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_dec xaead_enc xaead_dec gv (L: hrx5_loc) (Fr: mpred)
    (nk kes st i now mlul buf mi mr mc img len kind ai ar tg h0 path: val)
    (head hd: val) (W1: rxw) (PS: list (val * share * peer)) (a: val) (P P': peer)
    (NSs NS1 NS2: list hnode4) (N: hnode4) (S: shim) (w: list int64) (s: skb) (d: rxdraw),
  rw_PS W1 = supd PS a P' -> sfind PS a = Some (Ews, P) ->
  NSs = NS1 ++ N :: NS2 -> hn_addr N = tg -> hn_p N = a -> hn_refs N = Vint (p_refs P) ->
  hn_rest N = prsnap_val P ->
  Int64.eq (s_fails (rw_S W1)) (s_fails S) = hrx5_B8R_alloc d ->
  rx_authenticated_b (rw_rx W1) a (l_skb L) (sk_len s) Int.zero (if hrx5_B8R_sess d P then Int.one else Int.zero) = true ->
  rx_peer (rw_rx W1) = a -> rx_eskb (rw_rx W1) = l_skb L -> rw_w W1 = w -> p_refs P' = p_refs P ->
  @semax W_handshake_receive Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (PROPx [] (LOCALx (hrx5_B8RA_L gv L nk kes st i now mlul buf mi mr mc img len kind ai ar tg h0 path)
      (SEPx [Fr; rxw_rep W_handshake_receive gv Tsh (l_wd L) head W1; hnodes_rep4 W_handshake_receive hd NSs;
             skb_rep Tsh (l_skb L) s; @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)])))
    hrx5_B8R_A
    (normal_ret_assert (PROPx [] (LOCALx (hrx5_B8RA_new a tg d P ++
        hrx5_B8RA_L gv L nk kes st i now mlul buf mi mr mc img len kind ai ar tg h0 path)
      (SEPx [Fr; rxw_rep W_handshake_receive gv Tsh (l_wd L) head W1; hnodes_rep4 W_handshake_receive hd NSs;
             skb_rep Tsh (l_skb L) s; @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)])))).

Lemma hrx5_B8RA_core : hrx5_B8RA_core_stmt.
Proof.
  intros Espec x25519 aead_dec xaead_enc xaead_dec gv L Fr nk kes st i now mlul buf mi mr mc img len kind ai ar tg h0
    path head hd W1 PS a P P' NSs NS1 NS2 N S w s d HPS Hsf HNS HNa HNp HNr HNrest Hfail Hauth Hpeer Heskb Hw HrefP'.
  unfold hrx5_Delta, hrx5_B8RA_L, hrx5_B8RA_new, hrx5_lvars; cbn [app].
  simplify_func_tycontext. abbreviate_semax.
  unfold rxw_rep. rewrite HPS, (hrx5_B8RA_peers_supd PS a Ews P P' Hsf).
  sep_apply (hrx5_B8RA_node' NSs NS1 N NS2 hd HNS).
  Intros nx. unfold hrx5_B8RA_flds. rewrite HNa, HNp, HNr.
  repeat flatten_sepcon_in_SEP.
  freeze [1;3;5;6;7;8;9;10;12;13;15;16] FR0.
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca by (unfold peer_rep; entailer!).
  assert (Hpa: isptr a) by exact (@field_compatible_isptr Noise.CS _ _ _ Hfca).
  unfold hrx5_B8R_A.
  forward.
  forward.
  match goal with |- context [temp HRM._h__2 ?v] => replace v with (hs_addr a) by (unfold hs_addr; f_equal; reflexivity) end.
  forward.
  match goal with |- context [temp HRM._s__1 ?v] =>
    replace v with (offset_val 8 tg) by (f_equal; reflexivity) end.
  sep_apply (hrx5_B8RA_fails gv (rw_S W1) (rw_w W1)).
  sep_apply (hrx5_B8RA_ss S w (l_ss L)).
  repeat flatten_sepcon_in_SEP.
  forward.
  forward.
  forward.
  match goal with |- context [temp HRM._alloc_ok ?v] =>
    replace v with (Vint (if hrx5_B8R_alloc d then Int.one else Int.zero))
      by (unfold Int64.cmpu; rewrite Hfail; destruct (hrx5_B8R_alloc d); reflexivity) end.
  repeat match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Q (SEPx ?Rr))) _ _ =>
    forward_if (PROPx Pr (LOCALx (temp HRM._t'146 (Vint (if hrx5_B8R_sess d P then Int.one else Int.zero)) :: Q)
      (SEPx Rr))) end.
  { destruct (hrx5_B8R_alloc d) eqn:Ea; [| exfalso; match goal with Hn: _ <> Int.zero |- _ => apply Hn; reflexivity end].
    sep_apply (hrx5_B8RA_dead' N P tg HNrest). repeat flatten_sepcon_in_SEP.
    forward.
    { entailer!. destruct (p_dead P); cbv; auto. }
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    unfold hrx5_B8R_sess. rewrite Ea. entailer!.
    destruct (p_dead P); reflexivity. }
  { destruct (hrx5_B8R_alloc d) eqn:Ea; [exfalso; apply Int.one_not_zero; assumption |].
    forward.
    unfold hrx5_B8R_sess. rewrite Ea. entailer!. }
  forward.
  forward.
  (* CHECK(rx_authenticated(target->p, &skb, 0, (unsigned)session)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (hrx5_B8RA_pfield Ews a P'). repeat flatten_sepcon_in_SEP.
    forward_call (gv, rw_rx W1, a, Ews, p_device P', Tsh, l_skb L, s, Int.zero,
                  if hrx5_B8R_sess d P then Int.one else Int.zero).
    rewrite Hauth.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(target->p->refcount.refcount == target->refs && shim_no_warning(&ss)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (hrx5_B8RA_refs Ews a P'). repeat flatten_sepcon_in_SEP.
    rewrite HrefP'.
    forward.
    forward.
    match goal with |- semax _ (PROPx ?Pr (LOCALx ?Q (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pr (LOCALx (temp HRM._t'148 (Vint Int.one) :: Q) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, w, rw_S W1, rw_w W1).
      rewrite Hw, hrx5_B8RA_warn_refl.
      forward.
      entailer!. }
    { exfalso. match goal with Hn: ?x <> ?x |- _ => apply Hn; reflexivity end. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. cbn [RA_normal normal_ret_assert app].
  thaw FR0.
  match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  unfold rxw_rep. rewrite HPS, (hrx5_B8RA_peers_supd PS a Ews P P' Hsf).
  entailer!.
Qed.
