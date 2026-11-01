(* law keypairs: the final glue: check_all's body over
   the context hkc5_G from the segment statements of hkp5_check_body_defs.v (hypotheses here) and the live loop
   (hkp5_check_body_loop.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_loop.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.
Local Open Scope logic.

Lemma hkc5_conseq {Espec: OracleKind} {cs: compspecs} Delta P P' Q Q' c (R: ret_assert) :
  ENTAIL Delta, P |-- P' -> ENTAIL Delta, Q' |-- Q ->
  @semax cs Espec Delta P' c (overridePost Q' R) -> @semax cs Espec Delta P c (overridePost Q R).
Proof.
  intros HP HQ HS. eapply semax_pre; [exact HP|].
  eapply semax_post; [ | | | | exact HS]; destruct R; unfold overridePost; cbn;
  auto; intros; apply andp_left2; apply derives_refl.
Qed.

Section Glue.
Variable x25519: list byte -> list byte -> list byte.

(* the main locals and buffers: always in the frame *)
Definition hkc5_wsmall (F: hkp5_fix) (V: hkp5_val) : list mpred :=
  [ptable Tsh (f_pt F) (v_head V); hbytes Tsh (v_RAW V) (f_raw F); hbytes Tsh (v_PUB V) (f_pub F);
   @data_at_ HCS Tsh t_hsnap (f_snap F); hout Tsh 32 (f_opub F); hout Tsh 32 (f_first F); hout Tsh 32 (f_second F)].

Definition hkc5_tail (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) : list mpred :=
  hkp5_hglobs F V Y ++ hkp5_globs (f_gv F) (y_S Y) (y_w Y) (y_kc Y).

Definition hkc5_dev (F: hkp5_fix) (V: hkp5_val) : mpred := device_rep Tsh (f_w F) (hkp5_D x25519 F V).
Definition hkc5_dsm (F: hkp5_fix) (V: hkp5_val) : mpred :=
  @data_at CKS Ews t_devsnap (devsnap_val (hkp5_D x25519 F V) (v_head V)) (f_gv F KC._dsm).

(* the frames of the segments *)
Definition hkc5_frLS F V Y O : mpred :=
  fold_right_sepcon (hkc5_dev F V :: hkc5_wsmall F V ++ tl (tl (hk5_items (f_gv F) (y_H Y))) ++ hkc5_tail F V Y ++
                     [hkp5_othR x25519 F V O]).
Definition hkc5_frPH F V Y O : mpred :=
  fold_right_sepcon (hkc5_dev F V :: keypairs_rep W_keypairs (y_KS Y) :: hkc5_wsmall F V ++ hk5_items (f_gv F) (y_H Y) ++
                     hkc5_tail F V Y ++ [hkp5_othR x25519 F V O]).
Definition hkc5_frPO F V Y O : mpred :=
  fold_right_sepcon (keypairs_rep W_keypairs (y_KS Y) :: hkc5_wsmall F V ++ hk5_items (f_gv F) (y_H Y) ++
                     hkc5_tail F V Y ++
                     [data_at Ews (tptr t_kent) (o_kd O) (f_gv F KC._kes); kents_rep W_keypairs (o_kd O) (o_KE O);
                      hkc5_dsm F V]).
Definition hkc5_frPK F V Y O : mpred :=
  fold_right_sepcon (hkc5_dev F V :: peer_rep Tsh (f_p F) (y_P Y) :: keypairs_rep W_keypairs (y_KS Y) ::
                     hkc5_wsmall F V ++ hk5_items (f_gv F) (y_H Y) ++ hkc5_tail F V Y ++
                     [data_at Ews (tptr t_hnode4) (o_hd O) (f_gv F KC._others);
                      hnodes_rep4 W_keypairs (o_hd O) (o_NS O); hkc5_dsm F V]).

Definition hkc5_VO F V Y : list vobj := [VDev Tsh (f_w F) (hkp5_D x25519 F V); VPeer Tsh (f_p F) (y_P Y)].

End Glue.

Ltac hkc5_flat :=
  unfold hkc5_S, hkc5_LS, hkc5_PH, hkc5_PO, hkc5_PK, hkc5_PK', hkc5_frLS, hkc5_frPH, hkc5_frPO, hkc5_frPK, hkp5_SEP,
    hkp5_world, hk5_items, hkc5_tail, hkc5_wsmall, hkc5_dev, hkc5_dsm, hkp5_hglobs, hkp5_globs, hkc5_lv, hkp5_othR,
    hkp5_oth_rep, hkc5_VO, vobjs;
  cbn [app tl fold_right_sepcon iter_sepcon vobj_rep].

Lemma hkc5_body_from x25519 :
  hkc5_head_stmt -> hkc5_slots_stmt -> hkc5_node_stmt -> hkc5_hs_stmt -> hkc5_onode_stmt -> hkc5_oloop_stmt ->
  hkc5_kfin_stmt -> hkc5_count_index_stmt -> hkc5_table_len_stmt -> hkc5_oth_facts_stmt ->
  (forall F V O, hkp5_oth_ok F V O -> NoDup (map hs_addr (map peer_addr4 (o_PS O)) ++ map ke_addr (o_KE O))) ->
  @semax_body hkp5_V hkc5_G W_keypairs KC.f_check_all (hk5_check_all_spec x25519).
Proof.
  intros HHEAD HSLOTS HNODE HHS HONODE HOLOOP HKFIN HCI HTL HOTH HND.
  start_function.
  match goal with H: hkp5_fix_ok F V |- _ => rename H into Hfix end.
  match goal with H: hkp5_inv F V Y |- _ => rename H into Hinv end.
  match goal with H: hkp5_oth_ok F V O |- _ => rename H into Hoth end.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
  change Delta with hkc5_Delta.
  change (Ssequence _ _) with
    (Ssequence hkc5_head (Ssequence hkc5_slots (Ssequence hkc5_loop (Ssequence hkc5_hs
      (Ssequence hkc5_oloop (Ssequence (match hkc5_kfin with Ssequence k _ => k | _ => Sskip end)
        (Ssequence (match hkc5_kfin with Ssequence _ f => f | _ => Sskip end) hkc5_ret))))))).
  pose proof Hinv as (HR & _).
  pose proof HR as ((HF2 & HNDm & HNm & HNDk & HNk & HRs & HCo & HHa & HPool) & HNDs & HSp & HSc & HSn).
  pose proof HPool as (HPa & HPk & HPo & HPko & (idx & Hidx) & HOD & HNDi & HWF).
  eapply semax_pre with (P' := hkc5_S x25519 F V Y O 0).
  { unfold hkc5_S, hkc5_lv. entailer!. }
  eapply semax_seq; [apply HHEAD |].
  eapply semax_seq; [apply HSLOTS |].
  set (nh := hkc5_nh (h5_ML (y_H Y))).
  set (hb := if vin (hs_addr (f_p F)) (t_L (y_T Y)) then 1 else 0).
  set (oh := hkc5_oh (y_T Y) (o_PS O)).
  (* LOOP *)
  eapply semax_seq with (Q := hkc5_S x25519 F V Y O nh).
  { eapply hkc5_conseq;
      [ | | apply (hkc5_loop_core F (y_P Y) (y_T Y) (y_KS Y) (h5_ML (y_H Y)) (hkc5_frLS x25519 F V Y O) _
                     HNODE HCI HF2 HNm HNDi)].
    - hkc5_flat. entailer!.
    - hkc5_flat. entailer!. }
  (* HS *)
  eapply semax_seq with (Q := hkc5_S x25519 F V Y O (nh + hb)).
  { assert (HCh: vin (hs_addr (f_p F)) (t_L (y_T Y)) = true -> count_index (y_T Y) idx = 1).
    { intros Hv. apply (HCI (y_T Y) (hs_addr (f_p F)) (mkEntry (f_p F) IDX_HANDSHAKE idx)); auto.
      - unfold vin in Hv. destruct (in_dec eq_dec (hs_addr (f_p F)) (t_L (y_T Y))); [auto | congruence].
      - unfold t_entry. rewrite Hidx. reflexivity. }
    eapply hkc5_conseq;
      [ | | apply (HHS Espec F (y_T Y) (y_P Y) idx nh (hkc5_frPH x25519 F V Y O) _ Hidx HCh)].
    - hkc5_flat. entailer!.
    - hkc5_flat. entailer!. }
  (* OLOOP *)
  destruct (HOTH x25519 F V Y O Hfix Hinv Hoth) as (HlenNS & Hon & Hvok & Hke & Hks).
  eapply semax_seq with (Q := hkc5_S x25519 F V Y O (nh + hb + oh)).
  { eapply hkc5_conseq;
      [ | | apply (HOLOOP HONODE Espec F (y_T Y) (o_hd O) (o_NS O) (o_PS O) (hkc5_VO x25519 F V Y) (nh + hb)
                     (hkc5_frPO x25519 F V Y O) _ HlenNS Hon)].
    - hkc5_flat. entailer!.
    - hkc5_flat. entailer!. }
  (* KFIN *)
  apply <- seq_assoc.
  change (Ssequence (match hkc5_kfin with Ssequence k _ => k | _ => Sskip end)
            (match hkc5_kfin with Ssequence _ f => f | _ => Sskip end)) with hkc5_kfin.
  eapply semax_seq with
    (Q := PROPx [hkp5_fix_ok F V; hkp5_inv F V Y; hkp5_oth_ok F V O]
          (LOCALx (temp KC._t'43 (Vlong (Int64.repr (Zlength (t_L (y_T Y))))) ::
                   temp KC._t'44 (Vlong (Int64.repr (kents_hashed_n (y_T Y) (o_KE O)))) :: hkc5_lv F (nh + hb + oh))
          (SEPx (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O))))).
  { eapply hkc5_conseq;
      [ | | apply (HKFIN Espec F (y_T Y) (o_kd O) (o_KE O) [VPeers (o_PS O)] (nh + hb + oh)
                     (hkc5_frPK x25519 F V Y O) _ Hvok Hke Hks)].
    - hkc5_flat. entailer!.
    - hkc5_flat. entailer!. }
  (* the return *)
  pose proof (HTL F V Y O Hinv Hoth (HND F V O Hoth)) as HL.
  rewrite hkc5_ret_eq. unfold hkc5_lv.
  forward.
  unfold nh, hb, oh. rewrite <- HL, Int64.eq_true. entailer!.
Qed.
