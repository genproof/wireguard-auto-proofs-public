(* law handshake_receive, body recv:
   segment LV of wg_receive_handshake_packet: the load (last_under_load), wg_cookie_validate_packet and the verdict (drop: return).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_defs.
Local Open Scope logic.

#[local] Existing Instance HRX.

Definition hrx5_rvLV_hide : Type := compspecs.

Lemma hrx5_rvLV_len msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false -> 32 <= Zlength msg.
Proof.
  unfold hrx5_fwd. intros H HT. rewrite HT in H.
  apply andb_prop in H as [_ H]. rewrite andb_false_l, orb_false_r in H.
  apply orb_prop in H as [H | H]; apply andb_prop in H as [_ H]; apply Z.eqb_eq in H; lia.
Qed.

Lemma hrx5_rvLV_vrange CC s msg chk now rl r :
  let v := fst (validate_model CC s msg chk now rl r) in v = 0 \/ v = 1 \/ v = 2 \/ v = 3.
Proof.
  unfold validate_model. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; auto.
Qed.

Lemma hrx5_rvLV_drop x25519 aead_dec xaead_enc xaead_dec W q sp s msg d :
  Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
  hrx5_rv_cons W q s msg (rd_r d) = false -> hrx5_rv_nc W q s msg (rd_r d) = false ->
  rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d = hrx5_rv_W1 W q s msg (rd_r d).
Proof.
  intros HT Hc Hn. unfold rx_packet. rewrite HT.
  unfold hrx5_rv_cons, hrx5_rv_nc, hrx5_rv_vm, hrx5_rv_ul in *. cbv zeta. rewrite Hc, Hn. reflexivity.
Qed.

Ltac hrx5_rvLV_cases :=
  match goal with
  | ul: bool, Hv: _ \/ _ |- _ =>
      destruct ul; destruct Hv as [ -> | [ -> | [ -> | -> ]]];
      cbn in *;
      repeat match goal with
             | H: typed_true _ _ |- _ => (inv H; fail) || clear H
             | H: typed_false _ _ |- _ => (inv H; fail) || clear H
             end
  end.

Lemma hrx5_rv_LV_ok : hrx5_rv_LV_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg HY HT.
  change hrx5_rvLV_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_S0, hrx5_rv_LV.
  unfold hrx5_rv_R, hrx5_rv_post.
  simplify_func_tycontext. abbreviate_semax.
  destruct HY as (Hx & Ha & Hxa & Hshd & Hshs & Hshm & Hfwd & Hmsg & Hok).
  unfold rxw_rep, device_rep, qlen_rep, lul_rep. Intros.
  unfold hrx5_rv_LOAD1. forward. forward.
  change (Int.divs (Int.repr 4096) (Int.repr 8)) with (Int.repr 512).
  freeze FR1 := (field_at _ _ (DOT I._dev) _ _) (identity_rep _ _ _) (checker_rep _ _ _)
    (field_at _ _ (DOT I._peer_hashtable) _ _) (field_at _ _ (DOT I._index_hashtable) _ _)
    (itable _ _ _) (ptable _ _ _) (peers_rep _).
  freeze FR := (FRZL FR1) (keypairs_rep _ _) (noise_globals _ _) (rxlog_rep _ _)
    (data_at _ tint _ _) (skb_rep _ _ _) (bytes_at _ _ _) (wg_consts _) (mem_mgr _).
  unfold hrx5_rv_LOAD2.
  forward_if (PROP () LOCAL (temp HRC._under_load (Val.of_bool (hrx5_rv_ul W q)); temp HRC._peer nullval;
     gvars gv; temp HRC._wg wg; temp HRC._skb sp)
    SEP (FRZL FR; shim_state4 gv (rw_S W) (rw_w W);
         data_at Ews tulong (Vlong (hrx5_rv_lul W q)) (gv HRC._last_under_load))).
  - destruct (Int.lt q (Int.repr 512)) eqn:Hq; [inv H0 |].
    forward_call (gv, rw_S W, rw_w W). forward.
    assert (Ul: hrx5_rv_ul W q = true) by (unfold hrx5_rv_ul, load_model; rewrite Hq; reflexivity).
    assert (Lul: hrx5_rv_lul W q = s_boot (rw_S W)) by (unfold hrx5_rv_lul, load_model; rewrite Hq; reflexivity).
    rewrite Ul, Lul. entailer!.
  - destruct (Int.lt q (Int.repr 512)) eqn:Hq; [| inv H0].
    forward.
    forward_if.
    + forward. forward_call (gv, rw_S W, rw_w W, rw_lul W, Int64.repr 1). forward.
      forward_if.
      * forward.
        destruct (birthdate_expired (rw_lul W) (Int64.repr 1) (s_boot (rw_S W))) eqn:He; [| simpl in H2; inv H2].
        assert (Ul: hrx5_rv_ul W q = false)
          by (unfold hrx5_rv_ul, load_model; rewrite Hq, He, (Int64.eq_false _ _ H1); reflexivity).
        assert (Lul: hrx5_rv_lul W q = Int64.zero)
          by (unfold hrx5_rv_lul, load_model; rewrite Hq, He, (Int64.eq_false _ _ H1); reflexivity).
        rewrite Ul, Lul. entailer!.
      * forward.
        destruct (birthdate_expired (rw_lul W) (Int64.repr 1) (s_boot (rw_S W))) eqn:He; [simpl in H2; inv H2 |].
        assert (Ul: hrx5_rv_ul W q = true)
          by (unfold hrx5_rv_ul, load_model; rewrite Hq, He, (Int64.eq_false _ _ H1); reflexivity).
        assert (Lul: hrx5_rv_lul W q = rw_lul W)
          by (unfold hrx5_rv_lul, load_model; rewrite Hq, He, (Int64.eq_false _ _ H1); reflexivity).
        rewrite Ul, Lul. entailer!.
    + forward.
        assert (Ul: hrx5_rv_ul W q = false)
          by (unfold hrx5_rv_ul, load_model; rewrite Hq, H1, Int64.eq_true; reflexivity).
        assert (Lul: hrx5_rv_lul W q = rw_lul W)
          by (unfold hrx5_rv_lul, load_model; rewrite Hq, H1, Int64.eq_true; reflexivity).
        rewrite Ul, Lul. entailer!.
  - thaw FR. thaw FR1.
    pose proof (hrx5_rvLV_len msg Hfwd HT) as Hlen.
    destruct Hmsg as [Hml Hmc].
    unfold hrx5_rv_VAL.
    forward_call (gv, rw_S W, rw_w W, shd, cc_addr wg, d_cc (rw_D W), shs, sp, s, shm, msg, hrx5_rv_ul W q).
    { destruct H as [Hp _]; exact Hp. }
    { entailer!. unfold cc_addr. destruct H as [Hp _]. destruct wg; try contradiction. simpl.
      destruct (hrx5_rv_ul W q); reflexivity. }
    Intros r.
    change (validate_model (d_cc (rw_D W)) s msg (hrx5_rv_ul W q) (s_boot (rw_S W)) (s_rlallow (rw_S W)) r)
      with (hrx5_rv_vm W q s msg r).
    apply semax_pre with
      (PROP (Zlength r = 32)
       LOCAL (temp HRC._mac_state (Vint (Int.repr (fst (hrx5_rv_vm W q s msg r))));
              temp HRC._under_load (Val.of_bool (hrx5_rv_ul W q)); temp HRC._peer nullval; gvars gv;
              temp HRC._wg wg; temp HRC._skb sp)
       SEP (rxw_rep CSw gv shd wg head (hrx5_rv_W1 W q s msg r); qlen_rep gv q; skb_rep shs sp s;
            bytes_at shm msg (sk_data s); wg_consts gv; mem_mgr gv)).
    { unfold rxw_rep, device_rep, qlen_rep, lul_rep, hrx5_rv_W1. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
      unfold dev_set_cc. cbn [d_dev d_id d_cc d_ptab d_itab]. unfold hrx5_rv_vm. entailer!. }
    freeze FR2 := (rxw_rep _ _ _ _ _ _) (qlen_rep _ _) (skb_rep _ _ _) (bytes_at _ _ _) (wg_consts _) (mem_mgr _).
    unfold hrx5_rv_DEC.
    pose proof (hrx5_rvLV_vrange (d_cc (rw_D W)) s msg (hrx5_rv_ul W q) (s_boot (rw_S W)) (s_rlallow (rw_S W)) r)
      as Hv.
    change (validate_model (d_cc (rw_D W)) s msg (hrx5_rv_ul W q) (s_boot (rw_S W)) (s_rlallow (rw_S W)) r)
      with (hrx5_rv_vm W q s msg r) in Hv. cbv zeta in Hv.
    assert (Hcons: hrx5_rv_cons W q s msg r = rx_consumes (hrx5_rv_ul W q) (fst (hrx5_rv_vm W q s msg r)))
      by reflexivity.
    assert (Hnc: hrx5_rv_nc W q s msg r = rx_needs_cookie (hrx5_rv_ul W q) (fst (hrx5_rv_vm W q s msg r)))
      by reflexivity.
    assert (Hw1: hrx5_rv_W1 W q s msg r = hrx5_rv_W1 W q s msg r) by reflexivity.
    revert Hcons Hnc Hv.
    generalize (fst (hrx5_rv_vm W q s msg r)) as v.
    generalize (hrx5_rv_ul W q) as ul.
    intros ul v Hcons Hnc Hv.
    forward_if (PROP () LOCAL (temp HRC._t'5 (Val.of_bool (ul && (v =? 3))); temp HRC._mac_state (Vint (Int.repr v));
      temp HRC._under_load (Val.of_bool ul); temp HRC._peer nullval; gvars gv; temp HRC._wg wg; temp HRC._skb sp)
      SEP (FRZL FR2)).
    { forward. entailer!. destruct ul; [|inv H1]. destruct Hv as [ -> | [ -> | [ -> | -> ]]]; reflexivity. }
    { forward. entailer!. destruct ul; [inv H1|]. reflexivity. }
    forward_if (PROP () LOCAL (temp HRC._t'6 (Val.of_bool (rx_consumes ul v)); temp HRC._mac_state (Vint (Int.repr v));
      temp HRC._under_load (Val.of_bool ul); temp HRC._peer nullval; gvars gv; temp HRC._wg wg; temp HRC._skb sp)
      SEP (FRZL FR2)).
    { forward. entailer!. hrx5_rvLV_cases; reflexivity. }
    { forward_if.
      - forward. forward. entailer!. hrx5_rvLV_cases; reflexivity.
      - forward. entailer!. hrx5_rvLV_cases; reflexivity. }
    forward_if.
    { forward. unfold hrx5_rv_SV. Exists r. thaw FR2. rewrite Hcons, Hnc. entailer!; hrx5_rvLV_cases; auto. }
    forward_if (PROP () LOCAL (temp HRC._t'4 (Val.of_bool (rx_needs_cookie ul v)); temp HRC._mac_state (Vint (Int.repr v));
      temp HRC._under_load (Val.of_bool ul); temp HRC._peer nullval; gvars gv; temp HRC._wg wg; temp HRC._skb sp)
      SEP (FRZL FR2)).
    { forward. entailer!. hrx5_rvLV_cases; reflexivity. }
    { forward. entailer!. hrx5_rvLV_cases; reflexivity. }
    forward_if.
    { forward. unfold hrx5_rv_SV. Exists r. thaw FR2. rewrite Hcons, Hnc. entailer!; hrx5_rvLV_cases; auto. }
    forward.
    Exists (mkRD r (Zrepeat Byte.zero 24) (Zrepeat Byte.zero 32) nullval).
    thaw FR2.
    rewrite (hrx5_rvLV_drop x25519 aead_dec xaead_enc xaead_dec W q sp s msg
               (mkRD r (Zrepeat Byte.zero 24) (Zrepeat Byte.zero 32) nullval) HT).
    2: { cbn [rd_r]. rewrite Hcons. hrx5_rvLV_cases; reflexivity. }
    2: { cbn [rd_r]. rewrite Hnc. hrx5_rvLV_cases; reflexivity. }
    cbn [rd_r]. entailer!.
    unfold rxdraw_ok. cbn [rd_r rd_nonce rd_r2 rd_k]. split3; [auto | reflexivity | split; [reflexivity |]].
    intros C; contradiction C; reflexivity.
Qed.
