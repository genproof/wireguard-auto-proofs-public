(* port of v3's prot3_shim_table2_ilookup.v to the v4 specifications (prot_specs4.v,
   context Gprot4: refcount_t warnings exact). v3 text follows. *)
(* Group shim_table2: the body of wg_index_hashtable_lookup (patch/wg_shim.c).
   Pool lemmas: prot_body3_shim_table1.v (lemmas prot4_shim_table1_...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol4.prot4_shim_table1.
Local Open Scope logic.

(* ---- the model: t_lookup along the list ---- *)
Lemma prot4_ilookup_find_app T L1 L2 idx :
  ~ In idx (t_indices T L1) -> t_find_index T (L1 ++ L2) idx = t_find_index T L2 idx.
Proof.
  induction L1 as [|a L1 IH]; simpl; intros H; auto.
  unfold t_indices in H; simpl in H.
  destruct (t_entry T a) as [E|] eqn:HE.
  - destruct (Int.eq (e_index E) idx) eqn:Hq.
    + apply Int.same_if_eq in Hq. exfalso. apply H. left. auto.
    + apply IH. intro; apply H; right; auto.
  - apply IH. intro; apply H; right; auto.
Qed.

Lemma prot4_ilookup_found T L1 a L2 idx mask sh E :
  t_L T = L1 ++ a :: L2 -> ~ In idx (t_indices T L1) -> sfind (t_D T) a = Some (sh, E) -> e_index E = idx ->
  t_lookup T mask idx = if Int.eq (Int.and (e_type E) mask) Int.zero then None else Some (a, E).
Proof.
  intros HL HI HE Hi. unfold t_lookup. rewrite HL, prot4_ilookup_find_app by auto. simpl.
  rewrite (prot4_shim_table1_tentry _ _ _ _ HE). rewrite Hi, Int.eq_true. reflexivity.
Qed.

Lemma prot4_ilookup_end T mask idx : ~ In idx (t_indices T (t_L T)) -> t_lookup T mask idx = None.
Proof.
  intros H. unfold t_lookup. rewrite <- (app_nil_r (t_L T)), prot4_ilookup_find_app by auto. reflexivity.
Qed.

Lemma prot4_ilookup_find_some T L idx a E :
  t_find_index T L idx = Some (a, E) -> In a L /\ t_entry T a = Some E.
Proof.
  induction L as [|x L IH]; simpl; intros H; [discriminate|].
  destruct (t_entry T x) as [E'|] eqn:HE.
  - destruct (Int.eq (e_index E') idx).
    + inv H. auto.
    + destruct (IH H); auto.
  - destruct (IH H); auto.
Qed.

Lemma prot4_ilookup_some T mask idx a E :
  t_lookup T mask idx = Some (a, E) -> In a (t_L T) /\ exists sh, sfind (t_D T) a = Some (sh, E).
Proof.
  unfold t_lookup. destruct (t_find_index T (t_L T) idx) as [[a' E']|] eqn:HF; [|discriminate].
  destruct (Int.eq _ _); [discriminate|]. intros H; inv H.
  destruct (prot4_ilookup_find_some _ _ _ _ _ HF) as [Hin HE]. split; auto.
  unfold t_entry in HE. destruct (sfind (t_D T) a) as [[sh E'']|]; inv HE. eauto.
Qed.

(* ---- the peer: refcount and device fields ---- *)
Definition prot4_ilookup_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma prot4_ilookup_peer_split sh p P r :
  peer_rep sh p (p_set_refs P r) =
  peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
  prot4_ilookup_prest sh p P.
Proof.
  unfold peer_rep, peer_refs_rep, prot4_ilookup_prest, p_set_refs; simpl.
  apply pred_ext; entailer!; cancel.
Qed.

Lemma prot4_ilookup_peer_eta P : P = p_set_refs P (p_refs P).
Proof. destruct P; reflexivity. Qed.

Lemma prot4_ilookup_prest_ptr sh p P : prot4_ilookup_prest sh p P |-- !! isptr p.
Proof. unfold prot4_ilookup_prest. entailer!. Qed.

Lemma prot4_ilookup_item a sh P : peer_item_rep (a, sh, P) = peer_rep sh a P.
Proof. reflexivity. Qed.

Lemma prot4_ilookup_peers_ref PS p shp P :
  sfind PS p = Some (shp, P) ->
  peer_refs_rep shp p (rc_add1 (p_refs P)) *
  @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) p * prot4_ilookup_prest shp p P *
  iter_sepcon peer_item_rep (sdel PS p)
  |-- peers_rep (peers_ref PS p).
Proof.
  intros H. unfold peers_ref. rewrite H. unfold peers_rep.
  rewrite (prot4_shim_table1_split (supd PS p (p_set_refs P (rc_add1 (p_refs P)))) p shp
             (p_set_refs P (rc_add1 (p_refs P))) peer_item_rep)
    by (eapply prot4_shim_table1_supd_sfind_same; eauto).
  rewrite prot4_shim_table1_supd_sdel, prot4_ilookup_item.
  rewrite prot4_ilookup_peer_split. cancel.
Qed.

Lemma prot4_ilookup_peers_open PS p shp P :
  sfind PS p = Some (shp, P) ->
  peers_rep PS =
  peer_refs_rep shp p (p_refs P) *
  @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) p * prot4_ilookup_prest shp p P *
  iter_sepcon peer_item_rep (sdel PS p).
Proof.
  intros H. unfold peers_rep. rewrite (prot4_shim_table1_split PS p shp P peer_item_rep H).
  rewrite prot4_ilookup_item, (prot4_ilookup_peer_eta P) at 1.
  rewrite prot4_ilookup_peer_split. reflexivity.
Qed.

Lemma prot4_ilookup_pp_S sh v p :
  @data_at Noise.CS sh (tptr t_peer) v p = @data_at Shim.CS sh (tptr t_peer) v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

(* the peers' counts are below INT_MAX (peers_refs_ok) *)
Lemma prot4_ilookup_refs_bnd PS a sh P :
  peers_refs_ok PS -> sfind PS a = Some (sh, P) -> 0 < Int.unsigned (p_refs P) < 2147483647.
Proof.
  intros HR Hf. apply prot4_shim_table1_sfind_In in Hf. unfold peers_refs_ok in HR.
  rewrite Forall_forall in HR. exact (HR _ Hf).
Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Lemma prot4_shim_table2_body_ilookup :
  @semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_lookup wg_index_hashtable_lookup_spec.
Proof.
  start_function.
  match goal with Hx: peers_refs_ok PS |- _ => rename Hx into Hrefs end.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))).
  { sep_apply (prot4_shim_table1_hd sht tab T [] (t_L T) eq_refl). entailer!. }
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  rewrite prot4_shim_table1_open0 by auto. Intros.
  unfold Sfor. forward. gather_SEP 0 1. rewrite <- prot4_shim_table1_open0 by auto.
  forward_loop (EX L1: list val, EX L2: list val,
    PROP (t_L T = L1 ++ L2; ~ In idx (t_indices T L1))
    LOCAL (temp Sh._iter_entry (hd nullval L2); temp Sh._entry nullval; temp Sh._table tab;
           temp Sh._type_mask (Vint mask); temp Sh._index (Vint idx); temp Sh._peer q; gvars gv)
    SEP (itable sht tab T; peers_rep PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2; ~ In idx (t_indices T (L1 ++ [a])))
    LOCAL (temp Sh._iter_entry a; temp Sh._entry nullval; temp Sh._table tab;
           temp Sh._type_mask (Vint mask); temp Sh._index (Vint idx); temp Sh._peer q; gvars gv)
    SEP (itable sht tab T; peers_rep PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w))
  break: (PROP ()
    LOCAL (temp Sh._entry (match t_lookup T mask idx with Some (a, _) => a | None => nullval end);
           temp Sh._table tab; temp Sh._peer q; gvars gv)
    SEP (itable sht tab T; peers_rep PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w)).
  { Exists (@nil val) (t_L T). entailer!. }
  { Intros L1 L2. rename H2 into HL, H3 into HI.
    destruct L2 as [|a L2].
    { forward_if.
      { simpl in *. contradiction. }
      forward. entailer!. rewrite app_nil_r in HL. rewrite prot4_ilookup_end; [reflexivity|]. rewrite HL; auto. }
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
    assert (VP := prot4_shim_table1_valid sht tab T a Ha).
    assert_PROP (isptr a) as Hpa by (sep_apply (prot4_shim_table1_isptr sht tab T a Ha); entailer!).
    simpl hd.
    forward_if.
    2: { subst a. contradiction. }
    forward.
    destruct (prot4_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
    rewrite (prot4_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. forward.
    gather_SEP 0 1 2. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    rewrite <- (prot4_shim_table1_open sht tab T a sh E) by auto.
    forward_if.
    - rewrite (prot4_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
      unfold entry_val. forward.
      gather_SEP 0 1 2. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
      rewrite <- (prot4_shim_table1_open sht tab T a sh E) by auto.
      forward_if (PROP ()
        LOCAL (temp Sh._entry (match t_lookup T mask idx with Some (a, _) => a | None => nullval end);
               temp Sh._table tab; temp Sh._peer q; gvars gv)
        SEP (itable sht tab T; peers_rep PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w)).
      + forward. rewrite (prot4_ilookup_found T L1 a L2 idx mask sh E HL HI HE H4), Int.eq_false by auto.
        entailer!.
      + forward. rewrite (prot4_ilookup_found T L1 a L2 idx mask sh E HL HI HE H4).
        match goal with Hz: Int.and _ _ = Int.zero |- _ => rewrite Hz, Int.eq_true end.
        entailer!.
      + forward. apply ENTAIL_refl.
    - forward. Exists L1 a L2. entailer!. eapply prot4_shim_table1_ind_snoc; eauto. }
  { Intros L1 a L2. rename H2 into HL, H3 into HI.
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
    destruct (prot4_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
    assert (HS: succ_in (t_L T) a = hd nullval L2).
    { rewrite HL. apply prot4_shim_table1_succ. rewrite <- HL. apply HW. }
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (prot4_shim_table1_hd sht tab T (L1 ++ [a]) L2 ltac:(rewrite <- app_assoc; auto)). entailer!. }
    rewrite (prot4_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. rewrite HS. forward.
    gather_SEP 0 1 2. rewrite <- HS. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    rewrite <- (prot4_shim_table1_open sht tab T a sh E) by auto.
    Exists (L1 ++ [a]) L2. entailer!.
    rewrite <- app_assoc; auto. }
  destruct (t_lookup T mask idx) as [[a E]|] eqn:HLk.
  2: { forward_if (PROP () LOCAL (temp Sh._entry nullval)
         SEP (itable sht tab T; peers_rep PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w)).
       { match goal with Hn: isptr _ |- _ => destruct Hn end. }
       { forward; try entailer!. }
       forward; try entailer!. }
  destruct (prot4_ilookup_some _ _ _ _ _ HLk) as [HinL [she HE]].
  assert (Ha: In a (saddrs (t_D T))) by (apply HW; auto).
  assert (writable_share she) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
  pose proof H as HPP. unfold pool_peers_ok in HPP. rewrite Forall_forall in HPP.
  specialize (HPP _ (prot4_shim_table1_sfind_In _ _ _ _ HE)). simpl in HPP.
  destruct HPP as [(shp & P & HP & Hr) _].
  assert (writable_share shp) by (eapply prot4_shim_table1_sfind_wr; eauto).
  assert (VP := prot4_shim_table1_valid sht tab T a Ha).
  assert_PROP (isptr a) as Hpa by (sep_apply (prot4_shim_table1_isptr sht tab T a Ha); entailer!).
  forward_if (PROP () LOCAL (temp Sh._entry a)
    SEP (itable sht tab T; peers_rep (peers_ref PS (e_peer E)); @data_at Noise.CS shq (tptr t_peer) (e_peer E) q; shim_state4 gv S w)).
  2: { subst a. contradiction. }
  2: { forward; try entailer!. }
  rewrite (prot4_shim_table1_open sht tab T a she E) by auto. repeat flatten_sepcon_in_SEP.
  rewrite (prot4_ilookup_peers_open PS (e_peer E) shp P HP). repeat flatten_sepcon_in_SEP.
  assert_PROP (isptr (e_peer E)) as Hpe.
  { sep_apply (prot4_ilookup_prest_ptr shp (e_peer E) P). entailer!. }
  unfold entry_val. forward.
  forward_call (gv, S, w, shp, e_peer E, p_refs P, p_device P).
  { rewrite if_false by (destruct (e_peer E); try contradiction; discriminate). cancel. }
  destruct (eq_dec (e_peer E) nullval) as [Hn|_]; [rewrite Hn in Hpe; destruct Hpe|].
  rewrite (Int.eq_false _ _ Hr). Intros.
  rewrite (rc_inz_warn_small _ _ (prot4_ilookup_refs_bnd PS _ shp P Hrefs HP)).
  assert (VP2: @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) (e_peer E) |--
               valid_pointer (e_peer E))
    by (apply field_at_valid_ptr0; [auto | reflexivity | reflexivity]).
  forward. forward.
  forward_if.
  2: { match goal with Hz: _ = nullval |- _ => change (e_peer E = nullval) in Hz; rewrite Hz in Hpe end.
       destruct Hpe. }
  forward.
  rewrite prot4_ilookup_pp_S. forward.
  rewrite <- prot4_ilookup_pp_S. rewrite (prot4_shim_table1_open sht tab T a she E) by auto.
  sep_apply (prot4_ilookup_peers_ref PS (e_peer E) shp P HP). unfold entry_val. entailer!.
Qed.

End Bodies.
