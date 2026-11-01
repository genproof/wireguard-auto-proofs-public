(* Group shim_table2: the body of wg_pubkey_hashtable_lookup (patch/wg_shim.c).
   Pool lemmas: prot_body3_shim_table1.v (lemmas prot3_shim_table1_...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Local Open Scope logic.

(* ---- helpers (prefix prot3_shim_table2_pkl_) ---- *)
Lemma prot3_shim_table2_pkl_memcmp_eq a b : Zlength a = Zlength b -> (WgNoise.proof.libc.spec.memcmp_Z a b = 0 <-> a = b).
Proof.
  revert b; induction a as [|x a IH]; intros [|y b] L.
  - simpl; tauto.
  - rewrite Zlength_nil, Zlength_cons in L. pose proof (Zlength_nonneg b). lia.
  - rewrite Zlength_nil, Zlength_cons in L. pose proof (Zlength_nonneg a). lia.
  - rewrite !Zlength_cons in L. simpl.
    destruct (Byte.eq_dec x y) as [<-|NE].
    + rewrite IH by lia. split; [intros ->; auto | intros E; inversion E; auto].
    + split; [intros E; exfalso; apply NE | intros E; inversion E; contradiction].
      rewrite <- (Byte.repr_unsigned x), <- (Byte.repr_unsigned y). f_equal. lia.
Qed.

Lemma prot3_shim_table2_pkl_memcmp_range a b : -256 < WgNoise.proof.libc.spec.memcmp_Z a b < 256.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; simpl; try lia.
  destruct (Byte.eq_dec x y); auto.
  pose proof (Byte.unsigned_range_2 x); pose proof (Byte.unsigned_range_2 y).
  change Byte.max_unsigned with 255 in *. lia.
Qed.

Lemma prot3_shim_table2_pkl_memcmp_int a b : Zlength a = Zlength b ->
  (Int.repr (WgNoise.proof.libc.spec.memcmp_Z a b) = Int.zero <-> a = b).
Proof.
  intros L. rewrite <- (prot3_shim_table2_pkl_memcmp_eq a b L).
  pose proof (prot3_shim_table2_pkl_memcmp_range a b).
  split; intros E.
  - apply (f_equal Int.signed) in E. rewrite Int.signed_repr in E by rep_lia. exact E.
  - rewrite E. reflexivity.
Qed.

Lemma prot3_shim_table2_pkl_eqb a b : bytes_eqb a b = true <-> a = b.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b); split; congruence. Qed.

Lemma prot3_shim_table2_pkl_find_app PS1 PS2 pub :
  pk_find PS1 pub = None -> pk_find (PS1 ++ PS2) pub = pk_find PS2 pub.
Proof.
  induction PS1 as [|[[x sh] Q] PS1 IH]; simpl; intros H; auto.
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) pub); [discriminate | auto].
Qed.

Lemma prot3_shim_table2_pkl_find_snoc PS1 a sh P pub :
  pk_find PS1 pub = None -> bytes_eqb (hs_rstatic (p_hs P)) pub = false ->
  pk_find (PS1 ++ [(a, sh, P)]) pub = None.
Proof.
  intros H1 H2. rewrite prot3_shim_table2_pkl_find_app by auto. simpl. rewrite H2. reflexivity.
Qed.

Lemma prot3_shim_table2_pkl_find_split PS pub a P : pk_find PS pub = Some (a, P) ->
  exists PS1 sh PS2, PS = PS1 ++ (a, sh, P) :: PS2 /\ pk_find PS1 pub = None.
Proof.
  induction PS as [|[[x sh] Q] PS IH]; simpl; intros H; [discriminate|].
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) pub) eqn:E.
  - inversion H; subst. exists [], sh, PS. auto.
  - destruct (IH H) as (PS1 & sh' & PS2 & -> & H1). exists ((x, sh, Q) :: PS1), sh', PS2.
    split; auto. simpl. rewrite E. auto.
Qed.

Lemma prot3_shim_table2_pkl_supd (PS1: list (val * share * peer)) a sh P PS2 P' : ~ In a (saddrs PS1) ->
  supd (PS1 ++ (a, sh, P) :: PS2) a P' = PS1 ++ (a, sh, P') :: PS2.
Proof.
  induction PS1 as [|[[x shx] Q] PS1 IH]; simpl; intros H.
  - destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [subst; exfalso; apply H; left; reflexivity|].
    rewrite IH; auto.
Qed.

Lemma prot3_shim_table2_pkl_peers_app PS1 PS2 : peers_rep (PS1 ++ PS2) = peers_rep PS1 * peers_rep PS2.
Proof. unfold peers_rep. apply iter_sepcon_app. Qed.

Lemma prot3_shim_table2_pkl_peers_cons a sh P PS : peers_rep ((a, sh, P) :: PS) = peer_rep sh a P * peers_rep PS.
Proof. reflexivity. Qed.

Lemma prot3_shim_table2_pkl_wf_app PS1 PS2 : peers_wf (PS1 ++ PS2) -> peers_wf PS1 /\ peers_wf PS2.
Proof. unfold peers_wf. rewrite Forall_app. auto. Qed.

Lemma prot3_shim_table2_pkl_wf_cons a sh P PS : peers_wf ((a, sh, P) :: PS) -> writable_share sh /\ peers_wf PS.
Proof. unfold peers_wf. intros H. inversion H; subst. auto. Qed.

Lemma prot3_shim_table2_pkl_glb sh1 sh2 :
  writable_share sh1 -> writable_share sh2 -> sepalg.nonidentity (Share.glb sh1 sh2).
Proof.
  intros [_ HW] HW2 N. apply writable_readable_share in HW2.
  apply HW2.
  apply leq_join_sub, Share.ord_spec1 in HW.
  apply identity_share_bot in N.
  rewrite HW, Share.glb_assoc, N, Share.glb_bot.
  apply bot_identity.
Qed.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma prot3_shim_table2_pkl_conflict sh1 sh2 a d1 d2 : writable_share sh1 -> writable_share sh2 ->
  field_at sh1 t_peer [StructField I._device] d1 a * field_at sh2 t_peer [StructField I._device] d2 a |-- FF.
Proof.
  intros. rewrite !field_at_data_at. apply data_at_conflict_glb.
  - apply prot3_shim_table2_pkl_glb; auto.
  - simpl. lia.
Qed.

Lemma prot3_shim_table2_pkl_conflict2 sh1 sh2 a P Q : writable_share sh1 -> writable_share sh2 ->
  peer_rep sh1 a P * peer_rep sh2 a Q |-- FF.
Proof.
  intros. unfold peer_rep. Intros.
  sep_apply (prot3_shim_table2_pkl_conflict sh1 sh2 a (p_device P) (p_device Q)); auto.
  rewrite FF_sepcon. apply FF_left.
Qed.

Lemma prot3_shim_table2_pkl_notin PS1 sh a P : peers_wf PS1 -> writable_share sh ->
  peers_rep PS1 * peer_rep sh a P |-- !! (~ In a (saddrs PS1)).
Proof.
  induction PS1 as [|[[x shx] Q] PS1 IH]; intros W Wsh.
  - apply prop_right. simpl. auto.
  - apply prot3_shim_table2_pkl_wf_cons in W. destruct W as [Wx W].
    rewrite prot3_shim_table2_pkl_peers_cons.
    destruct (eq_dec x a) as [<-|NE].
    + sep_apply (prot3_shim_table2_pkl_conflict2 shx sh x Q P); auto.
      rewrite FF_sepcon. apply FF_left.
    + rewrite sepcon_assoc. sep_apply (IH W Wsh). normalize. apply prop_right.
      simpl. intros [E|E]; auto.
Qed.

Lemma prot3_shim_table2_pkl_isptr sh a P : peer_rep sh a P |-- !! isptr a.
Proof. unfold peer_rep. entailer!. Qed.

Lemma prot3_shim_table2_pkl_chain_ptr head PS : pk_chain head PS -> peers_rep PS |-- !! is_pointer_or_null head.
Proof.
  destruct PS as [|[[a sh] P] PS]; intros H; simpl in H.
  - subst. apply prop_right. simpl. auto.
  - destruct H as [-> _]. rewrite prot3_shim_table2_pkl_peers_cons.
    sep_apply (prot3_shim_table2_pkl_isptr sh a P). entailer!.
Qed.

Lemma prot3_shim_table2_pkl_valid sh a P : writable_share sh -> peer_rep sh a P |-- valid_pointer a.
Proof.
  intros. unfold peer_rep. Intros.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | reflexivity | reflexivity].
Qed.

Definition prot3_shim_table2_pkl_hrest (sh: share) (h: val) (H: handshake) : mpred :=
  field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
  field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
  field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
  field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
  field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
  field_at sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
  field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
  field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
  field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
  field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
  (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

(* everything of peer_rep except pubkey_next and the handshake's remote_static *)
Definition prot3_shim_table2_pkl_rest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer [StructField I._device] (p_device P) p *
  field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  prot3_shim_table2_pkl_hrest sh (hs_addr p) (p_hs P) *
  field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

(* everything of peer_rep except refcount and device: independent of p_refs *)
Definition prot3_shim_table2_pkl_rest2 (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma prot3_shim_table2_pkl_split2 sh p P :
  peer_rep sh p P =
  peer_refs_rep sh p (p_refs P) * field_at sh t_peer [StructField I._device] (p_device P) p *
  prot3_shim_table2_pkl_rest2 sh p P.
Proof.
  unfold peer_rep, peer_refs_rep, prot3_shim_table2_pkl_rest2.
  apply pred_ext; entailer!.
Qed.

Lemma prot3_shim_table2_pkl_rest2_refs sh p P r :
  prot3_shim_table2_pkl_rest2 sh p (p_set_refs P r) = prot3_shim_table2_pkl_rest2 sh p P.
Proof. reflexivity. Qed.
End NoiseCS.

Lemma prot3_shim_table2_pkl_rs sh p (v: list val) : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField I._remote_static] v (hs_addr p) =
  @data_at Shim.CS sh (tarray tuchar 32) v (offset_val 136 p).
Proof.
  intros FC.
  assert (FH: @field_compatible Noise.CS (@nested_field_type Noise.CS t_peer (DOT I._handshake)) []
     (offset_val (@nested_field_offset Noise.CS t_peer (DOT I._handshake)) p)).
  { apply (@field_compatible_nested_field Noise.CS t_peer [StructField I._handshake] p).
    auto with field_compatible. }
  change (@nested_field_type Noise.CS t_peer (DOT I._handshake)) with t_hs in FH.
  change (offset_val (@nested_field_offset Noise.CS t_peer (DOT I._handshake)) p) with (hs_addr p) in FH.
  rewrite (@field_at_data_at Noise.CS).
  rewrite field_address_offset.
  2: { apply field_compatible_cons. split; auto. unfold in_members; simpl; tauto. }
  unfold hs_addr, OFS_PEER_HANDSHAKE. rewrite offset_offset_val. simpl.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma prot3_shim_table2_pkl_pkn sh p v :
  @field_at Noise.CS sh t_peer [StructField I._pubkey_next] v p =
  @field_at Shim.CS sh t_peer [StructField I._pubkey_next] v p.
Proof. apply field_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_shim_table2_pkl_open sh p P :
  peer_rep sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  (@field_at Shim.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   @data_at Shim.CS sh (tarray tuchar 32) (bytes (hs_rstatic (p_hs P))) (offset_val 136 p) *
   prot3_shim_table2_pkl_rest sh p P).
Proof.
  unfold peer_rep, hs_rep, prot3_shim_table2_pkl_rest, prot3_shim_table2_pkl_hrest.
  apply pred_ext; Intros; rewrite <- prot3_shim_table2_pkl_pkn, <- prot3_shim_table2_pkl_rs by auto;
    entailer!.
Qed.

Lemma prot3_shim_table2_pkl_bytes sh bs p : Zlength bs = 32 ->
  bytes_at sh bs p = @data_at Shim.CS sh (tarray tuchar 32) (map Vubyte bs) p.
Proof.
  intros L. unfold bytes_at, bytes. rewrite L. apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma prot3_shim_table2_pkl_ptab sh v p :
  ptable sh p v = @data_at Shim.CS sh t_ptab v p.
Proof. unfold ptable. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Lemma prot3_shim_table2_body_pklookup :
  @semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_pubkey_hashtable_lookup wg_pubkey_hashtable_lookup_spec.
Proof.
  start_function.
  rewrite (prot3_shim_table2_pkl_bytes shk pub pk H0), prot3_shim_table2_pkl_ptab.
  forward.
  forward_loop (EX PS1: list (val * share * peer), EX PS2: list (val * share * peer), EX it: val,
    PROP (PS = PS1 ++ PS2; pk_find PS1 pub = None; pk_chain it PS2)
    LOCAL (temp WgNoise.shim.code._iter_peer it; temp WgNoise.shim.code._peer nullval;
           temp WgNoise.shim.code._table tab; temp WgNoise.shim.code._pubkey pk; gvars gv)
    SEP (@data_at Shim.CS sht t_ptab head tab; peers_rep PS;
         @data_at Shim.CS shk (tarray tuchar 32) (map Vubyte pub) pk; shim_state gv S))
  continue: (EX PS1: list (val * share * peer), EX a: val, EX sh: share, EX P: peer,
    EX PS2: list (val * share * peer),
    PROP (PS = PS1 ++ (a, sh, P) :: PS2; pk_find (PS1 ++ [(a, sh, P)]) pub = None; pk_chain (p_pknext P) PS2)
    LOCAL (temp WgNoise.shim.code._iter_peer a; temp WgNoise.shim.code._peer nullval;
           temp WgNoise.shim.code._table tab; temp WgNoise.shim.code._pubkey pk; gvars gv)
    SEP (@data_at Shim.CS sht t_ptab head tab; peers_rep PS;
         @data_at Shim.CS shk (tarray tuchar 32) (map Vubyte pub) pk; shim_state gv S))
  break: (PROP ()
    LOCAL (temp WgNoise.shim.code._peer (match pk_find PS pub with Some (a, _) => a | None => nullval end);
           temp WgNoise.shim.code._table tab; temp WgNoise.shim.code._pubkey pk; gvars gv)
    SEP (@data_at Shim.CS sht t_ptab head tab; peers_rep PS;
         @data_at Shim.CS shk (tarray tuchar 32) (map Vubyte pub) pk; shim_state gv S)).
  { assert_PROP (is_pointer_or_null head).
    { sep_apply (prot3_shim_table2_pkl_chain_ptr head PS H1). entailer!. }
    forward. Exists (@nil (val * share * peer)) PS head. entailer!. }
  { Intros PS1 PS2 it. rename H2 into HPS, H3 into HF1, H4 into HC.
    destruct PS2 as [|[[a sh] P] PS2].
    - simpl in HC. subst it. rewrite app_nil_r in HPS. subst PS.
      forward_if.
      { contradiction. }
      forward. entailer!. rewrite HF1. auto.
    - simpl in HC. destruct HC as [-> HC]. subst PS.
      destruct (prot3_shim_table2_pkl_wf_app _ _ H) as [W1 W2].
      destruct (prot3_shim_table2_pkl_wf_cons _ _ _ _ W2) as [Wsh W3].
      rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons.
      repeat flatten_sepcon_in_SEP.
      assert_PROP (isptr a) as Pa.
      { sep_apply (prot3_shim_table2_pkl_isptr sh a P). entailer!. }
      forward_if.
      { apply denote_tc_test_eq_split; [|auto with valid_pointer].
        pull_left (peer_rep sh a P). repeat apply sepcon_valid_pointer1.
        apply prot3_shim_table2_pkl_valid; auto. }
      2: { subst a. contradiction. }
      forward.
      rewrite (prot3_shim_table2_pkl_open sh a P). Intros.
      repeat flatten_sepcon_in_SEP.
      match goal with HO: hs_ok _ |- _ => pose proof HO as HO'; destruct HO' as (_ & Lrs & _) end.
      unfold bytes.
      forward_call (shk, sh, pk, offset_val 136 a, 32, pub, hs_rstatic (p_hs P)).
      forward_if.
      + forward. forward.
        match goal with HM: Int.repr (WgNoise.proof.libc.spec.memcmp_Z _ _) = Int.zero |- _ =>
          apply prot3_shim_table2_pkl_memcmp_int in HM; [|congruence] end.
        assert (HF: pk_find (PS1 ++ (a, sh, P) :: PS2) pub = Some (a, P)).
        { rewrite prot3_shim_table2_pkl_find_app by auto. simpl.
          rewrite (proj2 (prot3_shim_table2_pkl_eqb _ _)) by auto. reflexivity. }
        rewrite HF.
        rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons,
          (prot3_shim_table2_pkl_open sh a P).
        entailer!.
      + forward.
        match goal with HM: Int.repr (WgNoise.proof.libc.spec.memcmp_Z _ _) <> Int.zero |- _ =>
          assert (HE: bytes_eqb (hs_rstatic (p_hs P)) pub = false) end.
        { destruct (bytes_eqb (hs_rstatic (p_hs P)) pub) eqn:E; auto.
          apply prot3_shim_table2_pkl_eqb in E. exfalso. 
          match goal with HM: Int.repr (WgNoise.proof.libc.spec.memcmp_Z _ _) <> Int.zero |- _ => apply HM end.
          apply prot3_shim_table2_pkl_memcmp_int; [congruence | auto]. }
        Exists PS1 a sh P PS2.
        rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons,
          (prot3_shim_table2_pkl_open sh a P).
        entailer!.
        apply prot3_shim_table2_pkl_find_snoc; auto.
  }
  { Intros PS1 a sh P PS2. rename H2 into HPS, H3 into HF1, H4 into HC. subst PS.
    destruct (prot3_shim_table2_pkl_wf_app _ _ H) as [W1 W2].
    destruct (prot3_shim_table2_pkl_wf_cons _ _ _ _ W2) as [Wsh W3].
    rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons.
    repeat flatten_sepcon_in_SEP.
    assert_PROP (is_pointer_or_null (p_pknext P)).
    { sep_apply (prot3_shim_table2_pkl_chain_ptr (p_pknext P) PS2 HC). entailer!. }
    rewrite (prot3_shim_table2_pkl_open sh a P). Intros.
    repeat flatten_sepcon_in_SEP.
    forward.
    Exists (PS1 ++ [(a, sh, P)]) PS2 (p_pknext P).
    rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons,
      (prot3_shim_table2_pkl_open sh a P).
    entailer!.
    rewrite <- app_assoc. reflexivity. }
  rewrite <- (prot3_shim_table2_pkl_bytes shk pub pk H0), <- prot3_shim_table2_pkl_ptab.
  destruct (pk_find PS pub) as [[a P]|] eqn:HF.
  - destruct (prot3_shim_table2_pkl_find_split _ _ _ _ HF) as (PS1 & sh & PS2 & -> & HF1).
    destruct (prot3_shim_table2_pkl_wf_app _ _ H) as [W1 W2].
    destruct (prot3_shim_table2_pkl_wf_cons _ _ _ _ W2) as [Wsh W3].
    rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons.
    repeat flatten_sepcon_in_SEP.
    assert_PROP (~ In a (saddrs PS1)) as NI.
    { sep_apply (prot3_shim_table2_pkl_notin PS1 sh a P W1 Wsh). entailer!. }
    assert_PROP (isptr a) as Pa.
    { sep_apply (prot3_shim_table2_pkl_isptr sh a P). entailer!. }
    rewrite (prot3_shim_table2_pkl_split2 sh a P). repeat flatten_sepcon_in_SEP.
    forward_call (gv, S, sh, a, p_refs P, p_device P).
    { destruct (eq_dec a nullval) as [E|_]; [subst; contradiction|]. cancel. }
    destruct (eq_dec a nullval) as [E|_]; [subst; contradiction|].
    forward.
    unfold pk_lookup. rewrite HF. unfold peer_get.
    destruct (Int.eq (p_refs P) Int.zero) eqn:Hr.
    + simpl. rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons,
        (prot3_shim_table2_pkl_split2 sh a P).
      entailer!.
    + simpl. rewrite prot3_shim_table2_pkl_supd by auto.
      rewrite prot3_shim_table2_pkl_peers_app, prot3_shim_table2_pkl_peers_cons,
        (prot3_shim_table2_pkl_split2 sh a (p_set_refs P _)), prot3_shim_table2_pkl_rest2_refs.
      simpl p_refs. simpl p_device.
      entailer!.
  - forward_call (gv, S, Ews, nullval, Int.zero, nullval).
    { destruct (eq_dec nullval nullval) as [_|NN]; [|congruence]. cancel. }
    destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    forward.
    unfold pk_lookup. rewrite HF. entailer!.
    apply derives_refl.
Qed.

End Bodies.
