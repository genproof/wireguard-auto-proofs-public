(* law handshake_receive: phase B8, branch R: the
   segment hrx5_B8R_E_stmt. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_E_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_E_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

Lemma hrx5_B8RE_fra (P1 P2: list Prop) : fold_right and True (P1 ++ P2) -> fold_right and True P1 /\ fold_right and True P2.
Proof. induction P1 as [|x P1 IH]; simpl; [tauto|]. intros [Hx Hr]. destruct (IH Hr). tauto. Qed.

Lemma hrx5_B8RE_extract {Espec: OracleKind} {cs: compspecs} Delta P1 P2 Q R c Post :
  (fold_right and True P2 -> semax Delta (PROPx P1 (LOCALx Q (SEPx R))) c Post) ->
  semax Delta (PROPx (P1 ++ P2) (LOCALx Q (SEPx R))) c Post.
Proof.
  intros H. eapply semax_pre; [| apply semax_extract_prop; exact H].
  apply andp_left2. unfold PROPx. intros rho. simpl.
  apply derives_extract_prop. intros Hp. apply hrx5_B8RE_fra in Hp. destruct Hp as [Hp1 Hp2].
  apply andp_right; [apply prop_right; exact Hp2|]. apply andp_right; [apply prop_right; exact Hp1 | apply derives_refl].
Qed.

Lemma hrx5_B8RE_khead T KE : hrx5_khead (map (kent_snapped T) KE) = hrx5_khead KE.
Proof. destruct KE; reflexivity. Qed.

Lemma hrx5_B8RE_supd_addr (PS: list (val * share * peer)) a Q :
  map peer_addr4 (supd PS a Q) = map peer_addr4 PS.
Proof.
  induction PS as [|[[x sh] w] PS IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hrx5_B8REm_sfind (PS: list (val * share * peer)) a sh P :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x shx] w] PS IH]; simpl; intros Hn Hin; [contradiction|].
  inversion Hn; subst. destruct (EqDec_val x a) as [->|Hne].
  - destruct Hin as [E|Hin]; [inversion E; reflexivity|].
    exfalso. apply H1. apply (in_map peer_addr4) in Hin. exact Hin.
  - destruct Hin as [E|Hin]; [inversion E; congruence | auto].
Qed.

Ltac hrx5_B8REm_dif := match goal with |- context [if ?c then _ else _] => destruct c end.

Lemma hrx5_B8RE_vin_vremove k a L : k <> a -> vin k (vremove a L) = vin k L.
Proof.
  intros Hne. unfold vin.
  destruct (in_dec eq_dec k (vremove a L)) as [H1|H1]; destruct (in_dec eq_dec k L) as [H2|H2]; auto; exfalso.
  - apply H2; clear H2. induction L as [|x L IH]; cbn in H1; [contradiction|].
    revert H1; hrx5_B8REm_dif; intros H1; [right; auto | destruct H1; [left | right]; auto].
  - apply H1; clear H1. induction L as [|x L IH]; [contradiction|]. cbn.
    destruct H2 as [<- | H2]; hrx5_B8REm_dif; subst; try contradiction; [left; auto | auto | right; auto].
Qed.

Lemma hrx5_B8RE_Tf d P T a :
  t_D (hrx5_B8R_Tf d P T a) = t_D T /\
  (forall k, k <> hs_addr a -> vin k (t_L (hrx5_B8R_Tf d P T a)) = vin k (t_L T)).
Proof.
  unfold hrx5_B8R_Tf. destruct (hrx5_B8R_sess d P); split; auto.
  intros k Hk. apply hrx5_B8RE_vin_vremove, Hk.
Qed.

Lemma hrx5_B8RE_vo1 PS : peers_rep PS = vobjs W [VPeers PS].
Proof. unfold vobjs. cbn. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_B8RE_vok x25519 R L PS : Forall (hrx5_pok x25519 R L) PS -> vobj_ok (VPeers PS).
Proof.
  intros H. cbn. eapply Forall_impl; [|exact H]. intros [[a sh] P] (-> & _).
  apply writable_readable, writable_Ews.
Qed.

Lemma hrx5_B8RE_ci x25519 aead_dec R PS M now ci :
  hrx5_ci_rep x25519 aead_dec R PS (OResp M) now ci = @data_at_ HCS Tsh t_mcinit ci.
Proof. reflexivity. Qed.

Lemma hrx5_B8RE_pt xaead_dec T PS M p : hrx5_pt_rep xaead_dec T PS (OResp M) p = hout Tsh 16 p.
Proof. reflexivity. Qed.

Lemma hrx5_B8RE_st x25519 aead_dec R T PS M a P ck h p :
  hrx5_fwd (obj_bytes (OResp M)) = true ->
  hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = Some (a, P, ck, h) ->
  hrx5_st_rep x25519 aead_dec R T PS (OResp M) p |-- @data_at_ HCS Tsh t_mstate p.
Proof.
  intros Hf Ht. unfold hrx5_st_rep. rewrite Hf, Ht. apply data_at_data_at_.
Qed.

Lemma hrx5_B8RE_rxlog gv X : rxlog_rep gv X |-- @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx).
Proof. unfold rxlog_rep. apply data_at_data_at_. Qed.

Lemma hrx5_B8RE_qlen gv q : qlen_rep gv q |-- @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len).
Proof. unfold qlen_rep. apply data_at_data_at_. Qed.

Lemma hrx5_B8R_E_ok : hrx5_B8R_E_stmt.
Proof.
  intros HI Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  unfold hrx5_B8R_RD, hrx5_B8R_St, hrx5_B8R_E, hrx5_Delta. cbv beta iota.
  simplify_func_tycontext. abbreviate_semax.
  apply hrx5_B8RE_extract. intros HF.
  Intros.
  unfold POSTCONDITION, abbreviate. destruct (hrx5_RB x25519 gv L FR) as [rn rb rc rr]. unfold overridePost.
  pose proof (HI x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE st i kc lul q proto
    ip4 ip6 port o dp tg ai ar d a P M ck h j HY H H0 H1 H2 H3 H4 H5 H6 HF) as HI'.
  cbv zeta in HI'. destruct HI' as (sec1 & birth1 & HD & HB1 & Hboot & HI1).
  unfold hrx5_B8R_F, hrx5_B8R_facts in HF. cbv zeta in HF.
  destruct HF as (Ho & Hfwd & Hai & Har & Htgt & Hj & HjP & Hnj & Htg & HW1 & _).
  clear HW1 Hnj Htg.
  fold (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d).
  unfold hrx5_B8R_Wxv, hrx5_B8R_Wx, hrx5_B8R_W1v.
  set (W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d)
    in *.
  set (Tf := hrx5_B8R_Tf d P T a) in *. set (Pf := hrx5_B8R_Pf d P M ck h) in *. set (Sf := hrx5_B8R_Sf d P W1) in *.
  unfold rxw_rep. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx]. rewrite HD.
  change (d_itab (hrx5_DL x25519 R L sec1 birth1)) with (l_itd L).
  change (d_ptab (hrx5_DL x25519 R L sec1 birth1)) with (l_ptd L).
  subst o ai ar.
  unfold hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_lvars, hrx5_B8R_tl, hrx5_ptrs. cbn [app].
  repeat flatten_sepcon_in_SEP.
  (* pure facts *)
  assert (HND: NoDup (map peer_addr4 PS)) by (destruct H0 as (_ & _ & X & _); exact X).
  assert (HinP: In (a, Ews, P) PS) by (rewrite <- HjP; apply Znth_In; exact Hj).
  assert (Hina: In a (map peer_addr4 PS)) by (exact (in_map peer_addr4 _ _ HinP)).
  assert (Hsf: sfind PS a = Some (Ews, P)) by (apply hrx5_B8REm_sfind; assumption).
  assert (Haddr: map peer_addr4 (supd PS a Pf) = map peer_addr4 PS) by apply hrx5_B8RE_supd_addr.
  assert_PROP (Forall (fun x => match x with (a, _, _) => isptr a end) (supd PS a Pf)) as Hptr'
    by (sep_apply (hrx5_B8RES_ptrs (supd PS a Pf)); Intros; apply prop_right; assumption).
  assert (Hptr: Forall (fun x => isptr (peer_addr4 x)) PS).
  { rewrite <- (Forall_map (fun v => isptr v) peer_addr4), <- Haddr, Forall_map.
    eapply Forall_impl; [| exact Hptr']. intros [[x shx] y] Hx. exact Hx. }
  clear Hptr'.
  assert_PROP (itable_wf Tf) as HwfF by (unfold itable; Intros; apply prop_right; assumption).
  assert_PROP (@field_compatible Noise.CS t_hs [] (hs_addr a)) as HFC
    by (sep_apply (hrx5_B8RES_hs_fc PS a Ews P Pf Hsf); Intros; apply prop_right; assumption).
  destruct (hrx5_B8RE_Tf d P T a) as [HTD HTL]. fold Tf in HTD, HTL.
  assert (Hpool: hrx5cr_pool (map ke_addr (map (kent_snapped T) KE)) (supd PS a Pf) Tf)
    by (destruct HI1 as (_ & _ & _ & _ & _ & _ & X); exact X).
  destruct (hrx5_B8RE_pure T Tf KE PS (supd PS a Pf) a HTD HTL HwfF Hpool Haddr HND Hptr Hina)
    as (Hkpre & Hkbn & Hkin & Hain & Hews & Hcount).
  (* 10: t = h->entry.hashed *)
  sep_apply (hrx5_B8RES_entry (l_itd L) Tf (hs_addr a) Hain Hews HFC). flatten_sepcon_in_SEP.
  forward.
  { unfold entry_val. cbv beta iota. destruct (vin (hs_addr a) (t_L Tf)); entailer!. }
  match goal with |- context [temp HRM._t'253 ?v] => change v with (Val.of_bool (vin (hs_addr a) (t_L Tf))) end.
  match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  match goal with |- semax _ (PROPx ?P (LOCALx (?t0 :: ?t1 :: ?t2 :: ?t3 :: ?t4 :: temp HM._hashed _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (t0 :: t1 :: t2 :: t3 :: t4 :: temp HM._hashed (Vlong (Int64.repr
      (hrx5_B8R_nh T a PS + (if vin (hs_addr a) (t_L Tf) then 1 else 0)))) :: Q) (SEPx R))) end.
  - (* hashed: CHECK(table_has(&itd, &h->entry)); hashed++ *)
    destruct (vin (hs_addr a) (t_L Tf)) eqn:Hv; [| match goal with Ht: typed_true _ _ |- _ => try rewrite Hv in Ht; inversion Ht end].
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    + entailer!.
    + assert (Hpa: isptr (hs_addr a)) by (destruct HFC; assumption).
      forward_call (Tsh, l_itd L, Tf, hs_addr a).
      rewrite Hv.
      forward_if True; [discriminate | forward; entailer! |].
      forward. entailer!.
    + forward. entailer!.
  - forward.
    match goal with Ht: typed_false _ _ |- _ => revert Ht end.
    destruct (vin (hs_addr a) (t_L Tf)) eqn:Hv; intros Ht; [inversion Ht|].
    rewrite Z.add_0_r. entailer!.
  - (* 11: CHECK(kents_same_but_next(kes, &itd) && table_len(&itd) == hashed + kents_hashed(kes)) *)
    set (nb := if vin (hs_addr a) (t_L Tf) then 1 else 0) in *.
    assert (Hvok: vobj_ok (VPeers (supd PS a Pf)))
      by (apply (hrx5_B8RE_vok x25519 R L); destruct HI1 as (X & _); exact X).
    rewrite (hrx5_B8RE_vo1 (supd PS a Pf)), hrx5_B8RE_khead.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    + apply ENTAIL_refl.
    + forward_call (hrx5_khead KE, map (kent_snapped T) KE, Tsh, l_itd L, Tf, [VPeers (supd PS a Pf)]).
      rewrite Hkbn.
      forward_if (temp HRM._t'195 (Vint Int.one)).
      * forward_call (Tsh, l_itd L, Tf).
        forward_call (hrx5_khead KE, map (kent_snapped T) KE, Tsh, l_itd L, Tf).
        rewrite Hcount.
        forward. entailer!.
        unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity.
      * match goal with Hc: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero Hc) end.
      * forward_if True; [discriminate | forward; entailer! |].
        forward. entailer!.
    + (* the fold into the loop's state: the new world *)
      rewrite <- hrx5_B8RE_vo1.
      rewrite hrx5_B8RE_ci, hrx5_B8RE_pt.
      sep_apply (hrx5_B8RE_st x25519 aead_dec R T PS M a P ck h (l_st L) Hfwd Htgt).
      sep_apply (hrx5_B8RE_rxlog gv (rw_rx W1)). sep_apply (hrx5_B8RE_qlen gv q).
      sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hrx5_DL x25519 R L sec1 birth1) head) (l_ds L)).
      sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
      sep_apply (@data_at_data_at_ CKS Tsh t_skbsnap (skbsnap_val (hrx5_skb dp (OResp M) proto ip4 ip6 port)) (l_sks L)).
      unfold hrx5_S8.
      Exists R sec1 birth1 Sf (rw_w W1) (hnodes_snapped4 T NS PS) (supd PS a Pf) Tf.
      Exists head nk (map (kent_snapped T) KE) st i (rw_kc W1) (rw_lul W1) q.
      Exists proto ip4 ip6 port (OResp M) dp img.
      unfold hrx5_ltemps. rewrite Hboot.
      unfold hrx5_wcore, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_lvars, hrx5_rest, hrx5_cglobs. cbn [app].
      rewrite !hrx5_B8RE_khead.
      entailer!.
Qed.
