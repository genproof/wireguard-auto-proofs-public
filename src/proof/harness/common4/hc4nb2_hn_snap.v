(* the body of hnodes_snap. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4nb2_hn_common.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HI := WgNoise.harness.x_consume_initiation_any.code.

(* a node opened for hnodes_snap: p and next at CS4nb, the snapshot fields as raw memory at the callees'
   compspecs (HCS for hs_take, CKS for pr_take), refs at CS4nb *)
Definition hc4nb_hs_open (p nx l: val) : mpred :=
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) p l *
  @data_at_ HCS Ews t_hsnap (offset_val 8 l) *
  @field_at_ CS4nb Ews t_hnode4 (DOT HC._refs) l *
  @data_at_ CKS Ews t_prsnap (offset_val 304 l) *
  @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l * spacer Ews 300 304 l.

Section Split.
#[local] Existing Instance CKS.
Lemma hc4nb_hs_split N nx l :
  hc4nb_cell N nx l |-- !! (@field_compatible CKS t_hnode4 [] l) && hc4nb_hs_open (hn_p N) nx l.
Proof.
  unfold hc4nb_cell, hc4nb_hs_open.
  assert_PROP (@field_compatible CKS t_hnode4 [] l) by (sep_apply (@data_at_local_facts CKS); entailer!).
  apply andp_right; [apply prop_right; auto|].
  unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._next) nx nx l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_refs N) l) by (apply JMeq_refl || reflexivity).
  sep_apply (@field_at_field_at_ CS4nb Ews t_hnode4 [StructField HC._refs]).
  sep_apply (@field_at_field_at_ CKS Ews t_hnode4 [StructField HC._snap]).
  sep_apply (@field_at_field_at_ CKS Ews t_hnode4 [StructField HC._rest]).
  rewrite (@field_at__data_at_ CKS Ews t_hnode4 [StructField HC._snap]).
  rewrite (@field_at__data_at_ CKS Ews t_hnode4 [StructField HC._rest]).
  rewrite !(@field_address_offset CKS) by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite (@data_at__cs_eq CKS CS4nb _ Ews t_hsnap) by reflexivity.
  rewrite (@data_at__cs_eq CS4nb HCS _ Ews t_hsnap) by reflexivity.
  cancel.
Qed.

(* the node after hnodes_snap's step: the snapshots of its peer written *)
Definition hc4nb_hs_closed (T: tstate) (p: val) (P: peer) (q nx l: val) : mpred :=
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) q l *
  @data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T p P)) (offset_val 8 l) *
  @field_at CS4nb Ews t_hnode4 (DOT HC._refs) (Vint (p_refs P)) l *
  @data_at CKS Ews t_prsnap (prsnap_val P) (offset_val 304 l) *
  @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l * spacer Ews 300 304 l.

Lemma hc4nb_hs_join T N p sh P nx l :
  @field_compatible CKS t_hnode4 [] l ->
  hc4nb_hs_closed T p P (hn_p N) nx l |-- hc4nb_cell (hn_snapshot4 T N (p, sh, P)) nx l.
Proof.
  intros H. unfold hc4nb_cell, hc4nb_hs_closed, hn_snapshot4. cbn [hn_p hn_snap hn_refs hn_rest].
  unfold data_at at 3. unfold_field_at 4%nat.
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._next) nx nx l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._refs) (Vint (p_refs P)) (Vint (p_refs P)) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_data_at CKS Ews t_hnode4 [StructField HC._snap]).
  rewrite (@field_at_data_at CKS Ews t_hnode4 [StructField HC._rest]).
  rewrite !(@field_address_offset CKS) by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite (@data_at_cs_eq HCS CS4nb _ Ews t_hsnap (hsnap_val (hs_snap_cur T p P)) (hsnap_val (hs_snap_cur T p P))) by (apply JMeq_refl || reflexivity).
  rewrite (@data_at_cs_eq CS4nb CKS _ Ews t_hsnap (hsnap_val (hs_snap_cur T p P)) (hsnap_val (hs_snap_cur T p P))) by (apply JMeq_refl || reflexivity).
  cancel.
Qed.
End Split.

Lemma hc4nb_hs_join' T N p sh P nx l :
  @field_compatible CKS t_hnode4 [] l ->
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) (hn_p N) l *
  @data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T p P)) (offset_val 8 l) *
  @field_at CS4nb Ews t_hnode4 (DOT HC._refs) (Vint (p_refs P)) l *
  @data_at CKS Ews t_prsnap (prsnap_val P) (offset_val 304 l) *
  @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l * spacer Ews 300 304 l
  |-- hc4nb_cell (hn_snapshot4 T N (p, sh, P)) nx l.
Proof. apply hc4nb_hs_join. Qed.

(* the peer's reference count at CS4nb, the rest of the peer hidden in a wand *)
Lemma hc4nb_hs_refs sh p P :
  peer_rep sh p P |--
  @field_at CS4nb sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  (@field_at CS4nb sh t_peer (DOT I._refcount) (Vint (p_refs P)) p -* peer_rep sh p P).
Proof.
  rewrite <- (@field_at_cs_eq Noise.CS CS4nb _ sh t_peer (DOT I._refcount) (Vint (p_refs P)) (Vint (p_refs P)) p)
    by (apply JMeq_refl || reflexivity).
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as HFC by (unfold peer_rep; entailer!).
  unfold peer_rep at 1. Intros. cancel.
  rewrite <- wand_sepcon_adjoint. unfold peer_rep. entailer!.
Qed.

Lemma hc4nb_hs_snapped_app T NS1 PS1 N x :
  Zlength NS1 = Zlength PS1 ->
  hnodes_snapped4 T (NS1 ++ [N]) (PS1 ++ [x]) = hnodes_snapped4 T NS1 PS1 ++ [hn_snapshot4 T N x].
Proof.
  revert PS1; induction NS1 as [|M NS1 IH]; intros PS1 HL; destruct PS1 as [|y PS1].
  - reflexivity.
  - rewrite Zlength_nil, Zlength_cons in HL. pose proof (Zlength_nonneg PS1). lia.
  - rewrite Zlength_nil, Zlength_cons in HL. pose proof (Zlength_nonneg NS1). lia.
  - rewrite !Zlength_cons in HL. unfold hnodes_snapped4 in *. simpl. f_equal. apply IH. lia.
Qed.

Lemma hc4nb_hs_addr_eq T N x : hn_addr (hn_snapshot4 T N x) = hn_addr N.
Proof. destruct x as [[p sh] P]; reflexivity. Qed.
Lemma hc4nb_hs_p_eq T N x : hn_p (hn_snapshot4 T N x) = hn_p N.
Proof. destruct x as [[p sh] P]; reflexivity. Qed.

(* the world compspecs as a hypothesis that typeclass resolution does not take for the proof's compspecs CS4nb *)
Definition hc4nb_hs_csw := compspecs.
#[local] Typeclasses Opaque hc4nb_hs_csw.

Section Body.
#[local] Existing Instance CS4nb.

Lemma hc4nb2_hn_snap_body (CSw: hc4nb_hs_csw) :
  @semax_body [] hc4_G_hnodes_snap CS4nb HI.f_hnodes_snap (hnodes_snap4_spec CSw).
Proof.
  start_function.
  forward_loop (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX PS2: list (val * share * peer), EX l': val,
    PROP (NS = NS1 ++ NS2; PS = PS1 ++ PS2; Zlength NS1 = Zlength PS1)
    LOCAL (temp HI._l l')
    SEP (hc4nb_seg CSw l l' (hnodes_snapped4 T NS1 PS1);
         hnodes_rep4 CSw l' NS2; peers_rep PS1; peers_rep PS2; itable sht tab T))
  continue: (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
             EX shp: share, EX P: peer, EX PS2: list (val * share * peer), EX nx: val,
    PROP (NS = NS1 ++ N :: NS2; PS = PS1 ++ (hn_p N, shp, P) :: PS2; Zlength NS1 = Zlength PS1;
          @field_compatible CKS t_hnode4 [] (hn_addr N))
    LOCAL (temp HI._l (hn_addr N))
    SEP (hc4nb_seg CSw l (hn_addr N) (hnodes_snapped4 T NS1 PS1);
         @malloc_token CSw Ews t_hnode4 (hn_addr N);
         hc4nb_hs_closed T (hn_p N) P (hn_p N) nx (hn_addr N);
         @malloc_token CSw Ews t_peer (hn_p N);
         hnodes_rep4 CSw nx NS2;
         peers_rep PS1; peer_rep shp (hn_p N) P; peers_rep PS2; itable sht tab T))
  break: (PROP () LOCAL ()
    SEP (hnodes_rep4 CSw l (hnodes_snapped4 T NS PS); peers_rep PS; itable sht tab T)).
  - Exists (@nil hnode4) NS (@nil (val * share * peer)) PS l. entailer!.
    sep_apply (hc4nb_seg_nil CSw l). apply derives_refl.
  - Intros NS1 NS2 PS1 PS2 l'.
    forward_if.
    + destruct NS2 as [|N NS2].
      { rewrite hc4nb_rep_nil. Intros. subst l'. contradiction. }
      assert (HP2: hnodes_peers4 (N :: NS2) PS2)
        by (apply (hc4nb_peers_split NS1 _ PS1 PS2); [auto | subst NS PS; auto]).
      destruct (hc4nb_peers_cons _ _ _ HP2) as [x [PS2' [HPS2 [HNx HP2']]]]. subst PS2.
      destruct x as [[p shp] P]. simpl in HNx. subst p.
      assert (HE: In (hs_addr (hn_p N)) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr (hn_p N))) <> Vundef /\
                  hs_sid (p_hs P) <> Vundef /\
                  Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P]).
      { subst PS. rewrite Forall_app in H1. destruct H1 as [_ H1]. inversion H1; subst. auto. }
      destruct HE as [HE1 [HE2 [HE3 HE4]]].
      assert (Hsh: writable_share shp).
      { unfold peers_wf in H0. subst PS. rewrite Forall_app in H0. destruct H0 as [_ H0]. inversion H0; auto. }
      rewrite hc4nb_rep_cons. Intros nx. subst l'.
      rewrite hc4nb2_hn_peers_cons. simpl peer_item_rep.
      sep_apply (hc4nb_hs_split N nx (hn_addr N)). Intros. unfold hc4nb_hs_open. Intros.
      assert_PROP (@field_compatible Noise.CS t_peer [] (hn_p N)) as HFC by (unfold peer_rep; entailer!).
      assert (HPp: isptr (hn_p N)) by (destruct HFC; auto).
      forward.
      forward_call (Ews, offset_val 8 (hn_addr N), shp, hn_p N, P, true, sht, tab, T).
      { simpl hs_mem. entailer!. }
      simpl hs_mem.
      forward.
      sep_apply (hc4nb_hs_refs shp (hn_p N) P). Intros.
      forward.
      forward.
      sep_apply (modus_ponens_wand (@field_at CS4nb shp t_peer (DOT I._refcount) (Vint (p_refs P)) (hn_p N))
                   (peer_rep shp (hn_p N) P)).
      forward.
      forward_call (Ews, offset_val 304 (hn_addr N), shp, hn_p N, P).
      Exists NS1 N NS2 PS1 shp P PS2' nx.
      unfold hc4nb_hs_closed. entailer!.
    + forward. subst l'. assert_PROP (NS2 = []) as HN2.
      { entailer!. match goal with Hn: nullval = nullval <-> _ |- _ => apply (proj1 Hn eq_refl) end. }
      subst NS2.
      assert (PS2 = []) by (apply hc4nb_peers_nil, (hc4nb_peers_split NS1 [] PS1 PS2);
                            [auto | rewrite <- H2, <- H3; auto]).
      subst PS2 NS PS. rewrite !app_nil_r. unfold peers_rep at 2. simpl iter_sepcon.
      sep_apply (hc4nb_seg_rep CSw l nullval (hnodes_snapped4 T NS1 PS1) []).
      rewrite app_nil_r. entailer!.
  - Intros NS1 N NS2 PS1 shp P PS2 nx.
    unfold hc4nb_hs_closed. Intros.
    forward.
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [(hn_p N, shp, P)]) PS2 nx.
    rewrite hc4nb2_hn_peers_app. simpl peer_item_rep.
    entailer!.
    { split; [rewrite <- app_assoc; reflexivity |].
      split; [rewrite <- app_assoc; reflexivity |].
      rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia. }
    rewrite hc4nb_hs_snapped_app by auto.
    sep_apply (hc4nb_hs_join' T N (hn_p N) shp P nx (hn_addr N) H5).
    pose proof (hc4nb_seg_snoc CSw l (hn_addr N) nx (hn_snapshot4 T N (hn_p N, shp, P)) (hnodes_snapped4 T NS1 PS1)
                  (eq_sym (hc4nb_hs_addr_eq _ _ _))) as HSN.
    rewrite (hc4nb_hs_p_eq T N) in HSN.
    sep_apply HSN. cancel.
  - unfold POSTCONDITION, abbreviate. simpl. entailer!. apply andp_left2, derives_refl.
Qed.
End Body.
