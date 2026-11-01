(* The bodies of the shim's two lookups (wg_pubkey_hashtable_lookup, wg_index_hashtable_lookup) against their
   v5 specifications (prot_specs5.v), in the context Gprot5 (prot_prog5.v).  The v5 specifications differ from
   v4's only in the peers: peers_rep5, whose peers have last_sent_handshake, latest_cookie and internal_id
   any (field_at_).  The lookups read a peer's pubkey_next and remote static key and take a reference
   (refcount, device): the lemmas below cut a peer_rep5 into those fields and a rest the lookups carry as a
   frame; the scripts are those of prot4_shim_table2_pklookup.v and prot4_shim_table2_ilookup.v over them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol4.prot4_shim_table1.
Require Import WgNoise.proof.protocol4.prot4_shim_table2_pklookup.
Require Import WgNoise.proof.protocol4.prot4_shim_table2_ilookup.
Local Open Scope logic.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma prot5_shim_peers_app PS1 PS2 : peers_rep5 (PS1 ++ PS2) = peers_rep5 PS1 * peers_rep5 PS2.
Proof. unfold peers_rep5. apply iter_sepcon_app. Qed.

Lemma prot5_shim_peers_cons a sh P PS : peers_rep5 ((a, sh, P) :: PS) = peer_rep5 sh a P * peers_rep5 PS.
Proof. reflexivity. Qed.

Lemma prot5_shim_item a sh P : peer_item_rep5 (a, sh, P) = peer_rep5 sh a P.
Proof. reflexivity. Qed.

(* two writable peers at the same address overlap *)
Lemma prot5_shim_conflict2 sh1 sh2 a P Q : writable_share sh1 -> writable_share sh2 ->
  peer_rep5 sh1 a P * peer_rep5 sh2 a Q |-- FF.
Proof.
  intros. unfold peer_rep5. Intros.
  sep_apply (prot4_shim_table2_pkl_conflict sh1 sh2 a (p_device P) (p_device Q)); auto.
  rewrite FF_sepcon. apply FF_left.
Qed.

(* a writable peer is not at any address of a list of writable peers it is separate from *)
Lemma prot5_shim_notin PS1 sh a P : peers_wf PS1 -> writable_share sh ->
  peers_rep5 PS1 * peer_rep5 sh a P |-- !! (~ In a (saddrs PS1)).
Proof.
  induction PS1 as [|[[x shx] Q] PS1 IH]; intros W Wsh.
  - apply prop_right. simpl. auto.
  - apply prot4_shim_table2_pkl_wf_cons in W. destruct W as [Wx W].
    rewrite prot5_shim_peers_cons.
    destruct (eq_dec x a) as [<-|NE].
    + sep_apply (prot5_shim_conflict2 shx sh x Q P); auto.
      rewrite FF_sepcon. apply FF_left.
    + rewrite sepcon_assoc. sep_apply (IH W Wsh). normalize. apply prop_right.
      simpl. intros [E|E]; auto.
Qed.

Lemma prot5_shim_isptr sh a P : peer_rep5 sh a P |-- !! isptr a.
Proof. unfold peer_rep5. entailer!. Qed.

Lemma prot5_shim_chain_ptr head PS : pk_chain head PS -> peers_rep5 PS |-- !! is_pointer_or_null head.
Proof.
  destruct PS as [|[[a sh] P] PS]; intros H; simpl in H.
  - subst. apply prop_right. simpl. auto.
  - destruct H as [-> _]. rewrite prot5_shim_peers_cons.
    sep_apply (prot5_shim_isptr sh a P). entailer!.
Qed.

Lemma prot5_shim_valid sh a P : writable_share sh -> peer_rep5 sh a P |-- valid_pointer a.
Proof.
  intros. unfold peer_rep5. Intros.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | reflexivity | reflexivity].
Qed.

(* everything of peer_rep5 but pubkey_next and the handshake's remote_static (what the pubkey lookup's
   comparison does not read) *)
Definition prot5_shim_pkl_rest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer [StructField I._device] (p_device P) p *
  field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  prot4_shim_table2_pkl_hrest sh (hs_addr p) (p_hs P) *
  field_at_ sh t_peer [StructField I._last_sent_handshake] p *
  field_at_ sh t_peer [StructField I._latest_cookie] p *
  field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  field_at_ sh t_peer [StructField I._internal_id] p *
  spacer sh 9 16 p * spacer sh 476 480 p.

(* everything of peer_rep5 but refcount and device (what taking a reference does not touch); it does not
   depend on the peer's count *)
Definition prot5_shim_rest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma prot5_shim_split sh p P r :
  peer_rep5 sh p (p_set_refs P r) =
  peer_refs_rep sh p r * field_at sh t_peer [StructField I._device] (p_device P) p * prot5_shim_rest sh p P.
Proof.
  unfold peer_rep5, peer_refs_rep, prot5_shim_rest, p_set_refs; simpl.
  apply pred_ext; entailer!; cancel.
Qed.

Lemma prot5_shim_split2 sh p P :
  peer_rep5 sh p P =
  peer_refs_rep sh p (p_refs P) * field_at sh t_peer [StructField I._device] (p_device P) p *
  prot5_shim_rest sh p P.
Proof. rewrite (prot4_ilookup_peer_eta P) at 1. apply prot5_shim_split. Qed.

Lemma prot5_shim_rest_refs sh p P r : prot5_shim_rest sh p (p_set_refs P r) = prot5_shim_rest sh p P.
Proof. reflexivity. Qed.

Lemma prot5_shim_rest_ptr sh p P : prot5_shim_rest sh p P |-- !! isptr p.
Proof. unfold prot5_shim_rest. entailer!. Qed.
End NoiseCS.

Lemma prot5_shim_pkl_open sh p P :
  peer_rep5 sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  (@field_at Shim.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   @data_at Shim.CS sh (tarray tuchar 32) (bytes (hs_rstatic (p_hs P))) (offset_val 136 p) *
   prot5_shim_pkl_rest sh p P).
Proof.
  unfold peer_rep5, hs_rep, prot5_shim_pkl_rest, prot4_shim_table2_pkl_hrest.
  apply pred_ext; Intros; rewrite <- prot4_shim_table2_pkl_pkn, <- prot4_shim_table2_pkl_rs by auto;
    entailer!.
Qed.

(* the peers after one more reference to the peer at p (peers_ref), and the peers opened at p *)
Lemma prot5_shim_peers_ref PS p shp P :
  sfind PS p = Some (shp, P) ->
  peer_refs_rep shp p (rc_add1 (p_refs P)) *
  @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) p * prot5_shim_rest shp p P *
  iter_sepcon peer_item_rep5 (sdel PS p)
  |-- peers_rep5 (peers_ref PS p).
Proof.
  intros H. unfold peers_ref. rewrite H. unfold peers_rep5.
  rewrite (prot4_shim_table1_split (supd PS p (p_set_refs P (rc_add1 (p_refs P)))) p shp
             (p_set_refs P (rc_add1 (p_refs P))) peer_item_rep5)
    by (eapply prot4_shim_table1_supd_sfind_same; eauto).
  rewrite prot4_shim_table1_supd_sdel, prot5_shim_item.
  rewrite prot5_shim_split. cancel.
Qed.

Lemma prot5_shim_peers_open PS p shp P :
  sfind PS p = Some (shp, P) ->
  peers_rep5 PS =
  peer_refs_rep shp p (p_refs P) *
  @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) p * prot5_shim_rest shp p P *
  iter_sepcon peer_item_rep5 (sdel PS p).
Proof.
  intros H. unfold peers_rep5. rewrite (prot4_shim_table1_split PS p shp P peer_item_rep5 H).
  rewrite prot5_shim_item, prot5_shim_split2. reflexivity.
Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Lemma prot5_shim_body_pklookup :
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_pubkey_hashtable_lookup wg_pubkey_hashtable_lookup_spec.
Proof.
  start_function.
  match goal with Hx: peers_refs_ok PS |- _ => rename Hx into Hrefs end.
  rewrite (prot4_shim_table2_pkl_bytes shk pub pk H0), prot4_shim_table2_pkl_ptab.
  forward.
  forward_loop (EX PS1: list (val * share * peer), EX PS2: list (val * share * peer), EX it: val,
    PROP (PS = PS1 ++ PS2; pk_find PS1 pub = None; pk_chain it PS2)
    LOCAL (temp WgNoise.shim.code._iter_peer it; temp WgNoise.shim.code._peer nullval;
           temp WgNoise.shim.code._table tab; temp WgNoise.shim.code._pubkey pk; gvars gv)
    SEP (@data_at Shim.CS sht t_ptab head tab; peers_rep5 PS;
         @data_at Shim.CS shk (tarray tuchar 32) (map Vubyte pub) pk; shim_state4 gv S w))
  continue: (EX PS1: list (val * share * peer), EX a: val, EX sh: share, EX P: peer,
    EX PS2: list (val * share * peer),
    PROP (PS = PS1 ++ (a, sh, P) :: PS2; pk_find (PS1 ++ [(a, sh, P)]) pub = None; pk_chain (p_pknext P) PS2)
    LOCAL (temp WgNoise.shim.code._iter_peer a; temp WgNoise.shim.code._peer nullval;
           temp WgNoise.shim.code._table tab; temp WgNoise.shim.code._pubkey pk; gvars gv)
    SEP (@data_at Shim.CS sht t_ptab head tab; peers_rep5 PS;
         @data_at Shim.CS shk (tarray tuchar 32) (map Vubyte pub) pk; shim_state4 gv S w))
  break: (PROP ()
    LOCAL (temp WgNoise.shim.code._peer (match pk_find PS pub with Some (a, _) => a | None => nullval end);
           temp WgNoise.shim.code._table tab; temp WgNoise.shim.code._pubkey pk; gvars gv)
    SEP (@data_at Shim.CS sht t_ptab head tab; peers_rep5 PS;
         @data_at Shim.CS shk (tarray tuchar 32) (map Vubyte pub) pk; shim_state4 gv S w)).
  { assert_PROP (is_pointer_or_null head).
    { sep_apply (prot5_shim_chain_ptr head PS H1). entailer!. }
    forward. Exists (@nil (val * share * peer)) PS head. entailer!. }
  { Intros PS1 PS2 it. rename H2 into HPS, H3 into HF1, H4 into HC.
    destruct PS2 as [|[[a sh] P] PS2].
    - simpl in HC. subst it. rewrite app_nil_r in HPS. subst PS.
      forward_if.
      { contradiction. }
      forward. entailer!. rewrite HF1. auto.
    - simpl in HC. destruct HC as [-> HC]. subst PS.
      destruct (prot4_shim_table2_pkl_wf_app _ _ H) as [W1 W2].
      destruct (prot4_shim_table2_pkl_wf_cons _ _ _ _ W2) as [Wsh W3].
      rewrite prot5_shim_peers_app, prot5_shim_peers_cons.
      repeat flatten_sepcon_in_SEP.
      assert_PROP (isptr a) as Pa.
      { sep_apply (prot5_shim_isptr sh a P). entailer!. }
      forward_if.
      { apply denote_tc_test_eq_split; [|auto with valid_pointer].
        pull_left (peer_rep5 sh a P). repeat apply sepcon_valid_pointer1.
        apply prot5_shim_valid; auto. }
      2: { subst a. contradiction. }
      forward.
      rewrite (prot5_shim_pkl_open sh a P). Intros.
      repeat flatten_sepcon_in_SEP.
      match goal with HO: hs_ok _ |- _ => pose proof HO as HO'; destruct HO' as (_ & Lrs & _) end.
      unfold bytes.
      forward_call (shk, sh, pk, offset_val 136 a, 32, pub, hs_rstatic (p_hs P)).
      forward_if.
      + forward. forward.
        match goal with HM: Int.repr (WgNoise.proof.libc.spec.memcmp_Z _ _) = Int.zero |- _ =>
          apply prot4_shim_table2_pkl_memcmp_int in HM; [|congruence] end.
        assert (HF: pk_find (PS1 ++ (a, sh, P) :: PS2) pub = Some (a, P)).
        { rewrite prot4_shim_table2_pkl_find_app by auto. simpl.
          rewrite (proj2 (prot4_shim_table2_pkl_eqb _ _)) by auto. reflexivity. }
        rewrite HF.
        rewrite prot5_shim_peers_app, prot5_shim_peers_cons,
          (prot5_shim_pkl_open sh a P).
        entailer!.
      + forward.
        match goal with HM: Int.repr (WgNoise.proof.libc.spec.memcmp_Z _ _) <> Int.zero |- _ =>
          assert (HE: bytes_eqb (hs_rstatic (p_hs P)) pub = false) end.
        { destruct (bytes_eqb (hs_rstatic (p_hs P)) pub) eqn:E; auto.
          apply prot4_shim_table2_pkl_eqb in E. exfalso. 
          match goal with HM: Int.repr (WgNoise.proof.libc.spec.memcmp_Z _ _) <> Int.zero |- _ => apply HM end.
          apply prot4_shim_table2_pkl_memcmp_int; [congruence | auto]. }
        Exists PS1 a sh P PS2.
        rewrite prot5_shim_peers_app, prot5_shim_peers_cons,
          (prot5_shim_pkl_open sh a P).
        entailer!.
        apply prot4_shim_table2_pkl_find_snoc; auto.
  }
  { Intros PS1 a sh P PS2. rename H2 into HPS, H3 into HF1, H4 into HC. subst PS.
    destruct (prot4_shim_table2_pkl_wf_app _ _ H) as [W1 W2].
    destruct (prot4_shim_table2_pkl_wf_cons _ _ _ _ W2) as [Wsh W3].
    rewrite prot5_shim_peers_app, prot5_shim_peers_cons.
    repeat flatten_sepcon_in_SEP.
    assert_PROP (is_pointer_or_null (p_pknext P)).
    { sep_apply (prot5_shim_chain_ptr (p_pknext P) PS2 HC). entailer!. }
    rewrite (prot5_shim_pkl_open sh a P). Intros.
    repeat flatten_sepcon_in_SEP.
    forward.
    Exists (PS1 ++ [(a, sh, P)]) PS2 (p_pknext P).
    rewrite prot5_shim_peers_app, prot5_shim_peers_cons,
      (prot5_shim_pkl_open sh a P).
    entailer!.
    rewrite <- app_assoc. reflexivity. }
  rewrite <- (prot4_shim_table2_pkl_bytes shk pub pk H0), <- prot4_shim_table2_pkl_ptab.
  destruct (pk_find PS pub) as [[a P]|] eqn:HF.
  - destruct (prot4_shim_table2_pkl_find_split _ _ _ _ HF) as (PS1 & sh & PS2 & -> & HF1).
    destruct (prot4_shim_table2_pkl_wf_app _ _ H) as [W1 W2].
    destruct (prot4_shim_table2_pkl_wf_cons _ _ _ _ W2) as [Wsh W3].
    rewrite prot5_shim_peers_app, prot5_shim_peers_cons.
    repeat flatten_sepcon_in_SEP.
    assert_PROP (~ In a (saddrs PS1)) as NI.
    { sep_apply (prot5_shim_notin PS1 sh a P W1 Wsh). entailer!. }
    assert_PROP (isptr a) as Pa.
    { sep_apply (prot5_shim_isptr sh a P). entailer!. }
    rewrite (prot5_shim_split2 sh a P). repeat flatten_sepcon_in_SEP.
    assert (Hb: 0 < Int.unsigned (p_refs P) < 2147483647).
    { unfold peers_refs_ok in Hrefs. rewrite Forall_forall in Hrefs.
      exact (Hrefs (a, sh, P) ltac:(apply in_or_app; right; left; reflexivity)). }
    forward_call (gv, S, w, sh, a, p_refs P, p_device P).
    { destruct (eq_dec a nullval) as [E|_]; [subst; contradiction|]. cancel. }
    destruct (eq_dec a nullval) as [E|_]; [subst; contradiction|].
    rewrite (rc_inz_warn_small _ _ Hb).
    forward.
    unfold pk_lookup. rewrite HF. unfold peer_get.
    destruct (Int.eq (p_refs P) Int.zero) eqn:Hr.
    + simpl. rewrite prot5_shim_peers_app, prot5_shim_peers_cons,
        (prot5_shim_split2 sh a P).
      entailer!.
    + simpl. rewrite prot4_shim_table2_pkl_supd by auto.
      rewrite prot5_shim_peers_app, prot5_shim_peers_cons,
        (prot5_shim_split2 sh a (p_set_refs P _)), prot5_shim_rest_refs.
      simpl p_refs. simpl p_device.
      entailer!.
  - forward_call (gv, S, w, Ews, nullval, Int.zero, nullval).
    { destruct (eq_dec nullval nullval) as [_|NN]; [|congruence]. cancel. }
    destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    forward.
    unfold pk_lookup. rewrite HF. entailer!.
    apply derives_refl.
Qed.

Lemma prot5_shim_body_ilookup :
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
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
    SEP (itable sht tab T; peers_rep5 PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2; ~ In idx (t_indices T (L1 ++ [a])))
    LOCAL (temp Sh._iter_entry a; temp Sh._entry nullval; temp Sh._table tab;
           temp Sh._type_mask (Vint mask); temp Sh._index (Vint idx); temp Sh._peer q; gvars gv)
    SEP (itable sht tab T; peers_rep5 PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w))
  break: (PROP ()
    LOCAL (temp Sh._entry (match t_lookup T mask idx with Some (a, _) => a | None => nullval end);
           temp Sh._table tab; temp Sh._peer q; gvars gv)
    SEP (itable sht tab T; peers_rep5 PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w)).
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
        SEP (itable sht tab T; peers_rep5 PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w)).
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
         SEP (itable sht tab T; peers_rep5 PS; @data_at Noise.CS shq (tptr t_peer) oldq q; shim_state4 gv S w)).
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
    SEP (itable sht tab T; peers_rep5 (peers_ref PS (e_peer E)); @data_at Noise.CS shq (tptr t_peer) (e_peer E) q; shim_state4 gv S w)).
  2: { subst a. contradiction. }
  2: { forward; try entailer!. }
  rewrite (prot4_shim_table1_open sht tab T a she E) by auto. repeat flatten_sepcon_in_SEP.
  rewrite (prot5_shim_peers_open PS (e_peer E) shp P HP). repeat flatten_sepcon_in_SEP.
  assert_PROP (isptr (e_peer E)) as Hpe.
  { sep_apply (prot5_shim_rest_ptr shp (e_peer E) P). entailer!. }
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
  sep_apply (prot5_shim_peers_ref PS (e_peer E) shp P HP). unfold entry_val. entailer!.
Qed.

End Bodies.
