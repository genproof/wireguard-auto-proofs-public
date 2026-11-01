(* law handshake_receive, B3 kind 3, segment P, part P1: pick a node, insert its
   handshake entry if not hashed, mc->receiver_index = its index (cut and states: hrx5_B3_K3_P_defs.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P_defs.
Local Open Scope logic.

Require Import WgNoise.proof.protocol.prot_rep_lemmas3.

(* ---- helpers (prefix hrx5_k3p1_; ports of cookie_reply's hcy5_p9_BA1_* and K3 W's hrx5_k3w_* at W) ---- *)
Notation W := W_handshake_receive.

#[local] Instance hrx5_k3p1_cceK : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.
#[local] Instance hrx5_k3p1_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_k3p1_cceC : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.

Lemma hrx5_k3p1_cmsg_W' sh p M : cm_ok M ->
  cmsg_rep sh p M = @data_at W sh t_cmsg (cmsg_val M) p.
Proof.
  intros HM. unfold cmsg_rep.
  rewrite (@data_at_change_composite Cookie.CS W hrx5_k3p1_cceC sh t_cmsg
    (cmsg_val M) (cmsg_val M) (JMeq_refl _) eq_refl).
  apply pred_ext; entailer!.
Qed.

Lemma hrx5_k3p1_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_k3p1_wand_self (X F G: mpred) : X |-- F * G -> F * G |-- X -> X |-- F * (F -* X).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hrx5_k3p1_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hrx5_k3p1_node h NS N v :
  In N NS -> hn_p N = v ->
  hnodes_rep4 W h NS |--
  @field_at W Ews t_hnode4 (DOT HC._p) v (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HC._p) v (hn_addr N) -* hnodes_rep4 W h NS).
Proof.
  intros Hin <-. revert h. induction NS as [| N0 NS IH]; intros h; [contradiction |].
  destruct Hin as [-> | Hin].
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N) * @malloc_token W Ews t_peer (hn_p N) *
       hnodes_rep4 W nx NS *
       (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N))))%logic.
    + sep_apply (hrx5_k3p1_node1 N nx). cancel.
    + apply hrx5_k3p1_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hrx5_k3p1_wand_frame. Exists nx. entailer!.
Qed.

Lemma hrx5_k3p1_head NS :
  NS <> [] -> hnodes_rep4 W (hrx5_head NS) NS |-- !! isptr (hrx5_head NS).
Proof.
  intros HN. destruct NS as [| N NS]; [congruence |]. simpl hnodes_rep4. simpl hrx5_head. Intros nx. entailer!. match goal with Hf: field_compatible _ _ (hn_addr N) |- _ => destruct Hf; auto end.
Qed.

Lemma hrx5_k3p1_pfc PS a sh P :
  sfind PS a = Some (sh, P) -> peers_rep PS |-- !! @field_compatible Noise.CS t_peer [] a.
Proof.
  intros Hf. unfold peers_rep. rewrite (prot_rep3_split _ _ _ _ _ Hf). cbn [peer_item_rep].
  unfold peer_rep at 1. entailer!.
Qed.

Lemma hrx5_k3p1_fc p : @field_compatible Noise.CS t_peer [] p -> @field_compatible W t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS W _ t_peer); auto. Qed.

(* the pool item at hs_addr p (Noise.CS) = the field entry of the handshake at hs_addr p (W) *)
Lemma hrx5_k3p1_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at W sh t_hs (DOT HC._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hrx5_k3p1_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS W _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT HC._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT HC._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hrx5_k3p1_sfind_ex (D: list (val * share * entry)) x :
  In x (saddrs D) -> exists sh E, sfind D x = Some (sh, E).
Proof.
  induction D as [| [[y shy] w] D IH]; cbn; intros H; [contradiction |].
  destruct (EqDec_val y x) as [-> | Hn]; [eauto |].
  destruct H as [-> | H]; [congruence | auto].
Qed.

Lemma hrx5_k3p1_sfind_in (D: list (val * share * entry)) x sh E :
  sfind D x = Some (sh, E) -> In (x, sh, E) D.
Proof.
  induction D as [| [[y shy] w] D IH]; cbn; intros H; [discriminate |].
  destruct (EqDec_val y x) as [-> | Hn]; [inv H; auto | auto].
Qed.

(* the entry at hs_addr a of the pool, focused as the field entry of a's handshake *)
Lemma hrx5_k3p1_ent sht tab T a :
  @field_compatible Noise.CS t_peer [] a -> itable_wf T -> In (hs_addr a) (saddrs (t_D T)) ->
  exists sh E, readable_share sh /\
  itable sht tab T |--
  @field_at W sh t_hs (DOT HC._entry)
    (entry_val E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))) (hs_addr a) *
  (@field_at W sh t_hs (DOT HC._entry)
     (entry_val E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))) (hs_addr a) -*
   itable sht tab T).
Proof.
  intros FC Hwf Hin. destruct (hrx5_k3p1_sfind_ex _ _ Hin) as (sh & E & Hf).
  exists sh, E. split.
  { destruct Hwf as (_ & _ & _ & HS). rewrite Forall_forall in HS.
    specialize (HS _ (hrx5_k3p1_sfind_in _ _ _ _ Hf)). apply writable_readable; exact HS. }
  apply hrx5_k3p1_wand_self with
    (G := (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
           iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr a)))%logic).
  - unfold itable. Intros. rewrite (prot_rep3_split _ _ _ _ _ Hf).
    change (pool_item_rep (t_L T) (hs_addr a, sh, E)) with
      (entry_at sh (hs_addr a) E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))).
    unfold entry_at.
    rewrite hrx5_k3p1_entry_fa by auto. cancel.
  - unfold itable. rewrite (prot_rep3_split _ _ _ _ _ Hf).
    change (pool_item_rep (t_L T) (hs_addr a, sh, E)) with
      (entry_at sh (hs_addr a) E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))).
    unfold entry_at.
    rewrite hrx5_k3p1_entry_fa by auto. entailer!.
Qed.

Section K3P1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3P_1_ok : hrx5_K3P_1_stmt x25519 aead_enc aead_dec xaead_enc xaead_dec.
Proof.
  unfold hrx5_K3P_1_stmt; intros Espec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port mc img M HLEM HY HNS.
  unfold hrx5_K3P_st, hrx5_K3P_props, hrx5_K3P_Q1, hrx5_Delta, hrx5_K3P_S1, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XF; cbn [app].
  abbreviate_semax.
  Intros.
  assert_PROP (isptr (hrx5_head NS)) as Hhd. { sep_apply (hrx5_k3p1_head NS HNS). entailer!. }
  forward. forward_call (hrx5_head NS, NS). Intros j. forward.
  match goal with |- context [temp HRM._x ?v] => change v with (hn_addr (Znth j NS)) end.
  assert (HjN: In (Znth j NS) NS) by (apply Znth_In; lia).
  pose proof HLEM as (HL1 & HL2 & HL3 & _ & HL5 & _).
  destruct (HL3 _ _ _ _ _ _ _ _ _ H0 HjN) as (P & HsP & HpP & HsaT).
  set (a := hn_p (Znth j NS)) in *.
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfc.
  { sep_apply (hrx5_k3p1_pfc PS a Ews P HsP). entailer!. }
  assert (Hpa: isptr a) by exact (field_compatible_isptr _ _ _ Hfc).
  sep_apply (hrx5_k3p1_node (hrx5_head NS) NS (Znth j NS) a HjN eq_refl). Intros.
  forward.
  forward.
  match goal with |- context [temp HRM._h (offset_val ?z a)] =>
    replace z with OFS_PEER_HANDSHAKE by reflexivity end.
  fold (hs_addr a).
  sep_apply (modus_ponens_wand (@field_at W Ews t_hnode4 (DOT HC._p) a (hn_addr (Znth j NS)))).
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  destruct (hrx5_k3p1_ent Tsh (l_itd L) T a Hfc Hwf HsaT) as (sh0 & E0 & Hrd0 & Hent0).
  sep_apply Hent0. Intros.
  unfold entry_val. cbn [e_peer e_type e_index].
  forward.
  { entailer!. match goal with |- context [Val.of_bool ?b] => destruct b; simpl; auto end. }
  sep_apply modus_ponens_wand.
  match goal with |- semax _ (PROPx ?Pl (LOCALx ?Q (SEPx ?Sx))) _ _ =>
    let F := eval pattern S, T in Sx in
    lazymatch F with ?G _ _ =>
      forward_if (EX S1: shim, EX T1: tstate,
        PROPx (hrx5_base_ok R sec birth S1 :: (s_boot S1 = s_boot S) :: hrx5_inv x25519 R L NS PS KE T1 head nk ::
               In (hs_addr a) (saddrs (t_D T1)) :: Pl)
        (LOCALx Q (SEPx (G S1 T1)))) end end.
  - (* not hashed: insert *)
    assert (Hha: isptr (hs_addr a)) by (unfold hs_addr; destruct a; try contradiction; exact I).
    forward_call (gv, S, w, Tsh, l_itd L, T, hs_addr a, @None (share * entry)).
    { cbn [raw_rep]. cancel. }
    Intros idx. cbn [raw_add] in *.
    pose proof (HL2 R L NS PS KE T head nk a Ews P idx H0 HsP) as Hinv1.
    destruct (HL3 _ _ _ _ _ _ _ _ _ Hinv1 HjN) as (P1 & _ & _ & Hsa1).
    Exists (shim_u32 S idx) (t_insert T (hs_addr a) idx).
    entailer!.
  - forward.
    Exists S T. entailer!.
  - Intros S1 T1.
    clear Hent0 Hrd0 E0 sh0.
    assert_PROP (itable_wf T1) as Hwf1. { unfold itable. entailer!. }
    destruct (hrx5_k3p1_ent Tsh (l_itd L) T1 a Hfc Hwf1 H9) as (sh1 & E1 & Hrd1 & Hent1).
    sep_apply Hent1. Intros.
    unfold entry_val. cbn [e_peer e_type e_index].
    forward.
    sep_apply modus_ponens_wand.
    rewrite (hrx5_k3p1_cmsg_W' _ _ _ H4).
    forward.
    match goal with |- context [@data_at _ Ews t_cmsg ?v mc] =>
      change v with (cmsg_val (hrx5_K3P_rcv M (e_index E1))) end.
    rewrite <- (hrx5_k3p1_cmsg_W' Ews mc (hrx5_K3P_rcv M (e_index E1)) H4).
    Exists S1 T1 (e_index E1) j P.
    rewrite <- H7.
    unfold hrx5_K3P_st, hrx5_K3P_props, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr,
      hrx5_K3_XF; cbn [app].
    entailer!.
Qed.

End K3P1.
