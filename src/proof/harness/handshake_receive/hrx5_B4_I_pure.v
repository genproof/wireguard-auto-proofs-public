(* law handshake_receive, phase B4, segment I: the pure facts
   of the harness's model block for an initiation (the first-match loop over the nodes against pk_find over the
   peers, lengths).  Port of consume_initiation_any's hci5_p7_pure.v (the peers are not changed before the block
   here: PS itself). 'B4'. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Local Open Scope Z_scope.

(* the harness's first-match loop `for (it = peers; it; it = it->next) if (p == NULL && bytes_eq(
   it->p->handshake.remote_static, s, 32)) p = it;` over the nodes NS paired with the peers PS (in the same
   order): the first node (and its peer) whose peer's remote static is s *)
Fixpoint hrx5_B4_I_fm (NS: list hnode4) (PS: list (val * share * peer)) (s: list byte)
  : option (hnode4 * (val * share * peer)) :=
  match NS, PS with
  | N :: NS', x :: PS' =>
      match x with (_, _, P) =>
        if bytes_eqb (hs_rstatic (p_hs P)) s then Some (N, x) else hrx5_B4_I_fm NS' PS' s
      end
  | _, _ => None
  end.

(* the value of p *)
Definition hrx5_B4_I_fmv (o: option (hnode4 * (val * share * peer))) : val :=
  match o with Some (N, _) => hn_addr N | None => nullval end.

Lemma hrx5_B4_I_pure_snoc : forall NS1 PS1 N (x: val * share * peer) s, length NS1 = length PS1 ->
     hrx5_B4_I_fm (NS1 ++ [N]) (PS1 ++ [x]) s =
     match hrx5_B4_I_fm NS1 PS1 s with
     | Some r => Some r
     | None => match x with (_, _, P) => if bytes_eqb (hs_rstatic (p_hs P)) s then Some (N, x) else None end
     end.
Proof.
  induction NS1 as [|N1 NS1 IH]; intros PS1 N x s Hl; destruct PS1 as [|x1 PS1]; simpl in Hl; try discriminate.
  - simpl. destruct x as [[? ?] P]. reflexivity.
  - simpl. destruct x1 as [[? ?] P1].
    destruct (bytes_eqb (hs_rstatic (p_hs P1)) s); [reflexivity|].
    apply IH. lia.
Qed.

Lemma hrx5_B4_I_pure_in : forall NS PS s N x, hrx5_B4_I_fm NS PS s = Some (N, x) -> In (hn_addr N) (map hn_addr NS).
Proof.
  induction NS as [|N1 NS IH]; intros PS s N x H; destruct PS as [|x1 PS]; simpl in H; try discriminate.
  destruct x1 as [[? ?] P1].
  destruct (bytes_eqb (hs_rstatic (p_hs P1)) s).
  - inversion H; subst. left; reflexivity.
  - right. eapply IH; eauto.
Qed.

Lemma hrx5_B4_I_pure_split : forall NS1 N NS2 PS1 PS2, hnodes_peers4 (NS1 ++ N :: NS2) (PS1 ++ PS2) ->
  length NS1 = length PS1 -> exists x PS2', PS2 = x :: PS2' /\ hn_p N = peer_addr4 x.
Proof.
  unfold hnodes_peers4.
  induction NS1 as [|N1 NS1 IH]; intros N NS2 PS1 PS2 H Hl; destruct PS1 as [|x1 PS1]; simpl in Hl; try discriminate.
  - simpl in H. destruct PS2 as [|x PS2']; simpl in H; [discriminate|].
    inversion H. eauto.
  - simpl in H. inversion H. eapply IH; eauto.
Qed.

Lemma hrx5_B4_I_pure_end : forall NS1 PS1 PS2, hnodes_peers4 NS1 (PS1 ++ PS2) -> length NS1 = length PS1 -> PS2 = [].
Proof.
  unfold hnodes_peers4. intros NS1 PS1 PS2 H Hl.
  apply (f_equal (@length val)) in H. rewrite !length_map, length_app in H.
  destruct PS2; simpl in *; [reflexivity | lia].
Qed.

(* the peers after the call against the peers before: same address, share and remote static, pointwise *)
Definition hrx5_B4_I_after_R (x y: val * share * peer) : Prop :=
  match x, y with (a, sh, P), (b, sh', Q) => a = b /\ sh = sh' /\ hs_rstatic (p_hs P) = hs_rstatic (p_hs Q) end.

Lemma hrx5_B4_I_after_refl : forall PS, Forall2 hrx5_B4_I_after_R PS PS.
Proof.
  induction PS as [|[[a sh] P] PS IH]; constructor; simpl; auto.
Qed.

Lemma hrx5_B4_I_after_find_in : forall PS s a P, pk_find PS s = Some (a, P) -> exists sh, In (a, sh, P) PS.
Proof.
  induction PS as [|[[x sh] Q] PS IH]; simpl; intros s a P H; [discriminate|].
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) s).
  - inv H. eauto.
  - destruct (IH _ _ _ H) as [sh' Hin]. eauto.
Qed.

Lemma hrx5_B4_I_after_supd : forall PS a sh P Q, NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  hs_rstatic (p_hs Q) = hs_rstatic (p_hs P) -> Forall2 hrx5_B4_I_after_R PS (supd PS a Q).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Q Hnd Hin Hrs; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. constructor; [simpl; auto | apply hrx5_B4_I_after_refl].
  - destruct (eq_dec x a) as [-> | Hne].
    + exfalso. apply H1. change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
    + rewrite if_false by auto. constructor; [simpl; auto | eauto].
Qed.

Lemma hrx5_B4_I_after_addrs : forall PS PS', Forall2 hrx5_B4_I_after_R PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  intros PS PS' H. induction H as [|[[a sh] P] [[b sh'] Q] PS PS' HR _ IH]; simpl; auto.
  destruct HR as (-> & _ & _). f_equal; auto.
Qed.

Lemma hrx5_B4_I_after_shares : forall PS PS', Forall2 hrx5_B4_I_after_R PS PS' ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS'.
Proof.
  intros PS PS' H. induction H as [|[[a sh] P] [[b sh'] Q] PS PS' HR _ IH]; intros Hf; auto.
  inv Hf. destruct HR as (_ & <- & _). constructor; auto.
Qed.

Lemma hrx5_B4_I_after_snapped_cons : forall T N NS x PS,
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hrx5_B4_I_after_fm_cons : forall N NS a sh P PS s,
  hrx5_B4_I_fm (N :: NS) ((a, sh, P) :: PS) s =
  if bytes_eqb (hs_rstatic (p_hs P)) s then Some (N, (a, sh, P)) else hrx5_B4_I_fm NS PS s.
Proof. reflexivity. Qed.

Lemma hrx5_B4_I_after_snap_p : forall T N x, hn_p (hn_snapshot4 T N x) = hn_p N.
Proof. intros T N [[p sh] P]. reflexivity. Qed.

Lemma hrx5_B4_I_after_snap_addr : forall T N x, hn_addr (hn_snapshot4 T N x) = hn_addr N.
Proof. intros T N [[p sh] P]. reflexivity. Qed.

Lemma hrx5_B4_I_after_map : forall T NS PS, map hn_p NS = map peer_addr4 PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  intros T. induction NS as [|N NS IH]; intros [|x PS] H; simpl in H; try discriminate; auto.
  inv H. rewrite hrx5_B4_I_after_snapped_cons. simpl. rewrite hrx5_B4_I_after_snap_p. f_equal; auto.
Qed.

Lemma hrx5_B4_I_after_none : forall T PS NS PS' s, Forall2 hrx5_B4_I_after_R PS PS' -> pk_find PS s = None ->
  hrx5_B4_I_fm (hnodes_snapped4 T NS PS) PS' s = None.
Proof.
  intros T PS NS PS' s H. revert NS.
  induction H as [|[[a sh] P] [[b sh'] Q] PS PS' HR _ IH]; intros NS Hf.
  - destruct NS; reflexivity.
  - destruct NS as [|N NS]; [reflexivity|].
    rewrite hrx5_B4_I_after_snapped_cons. simpl in Hf. destruct HR as (<- & <- & Hrs).
    rewrite hrx5_B4_I_after_fm_cons. rewrite <- Hrs.
    destruct (bytes_eqb (hs_rstatic (p_hs P)) s); [discriminate|]. auto.
Qed.

(* the facts about the node found (kept folded: the snapshot equation compares two reptypes, which the
   kernel re-checks at every occurrence) *)
Definition hrx5_B4_I_after_rest (N: hnode4) (a: val) (P P': peer) (sn: hsnap) : Prop :=
  hn_p N = a /\ hs_rstatic (p_hs P') = hs_rstatic (p_hs P) /\
  hn_snap N = hsnap_val sn /\ sn_hs sn = p_hs P /\
  hs_ok (p_hs P) /\ 0 <= Int64.unsigned (hs_lic (p_hs P)) < 2 ^ 62.

Lemma hrx5_B4_I_after_and6 : forall A B C D E F: Prop, A -> B -> C -> D -> E -> F -> A /\ B /\ C /\ D /\ E /\ F.
Proof. intros. repeat split; assumption. Qed.

Lemma hrx5_B4_I_after_rest_intro : forall T N p sh P P', hn_p N = p ->
  hs_rstatic (p_hs P') = hs_rstatic (p_hs P) -> hs_ok (p_hs P) ->
  0 <= Int64.unsigned (hs_lic (p_hs P)) < 2 ^ 62 ->
  exists sn, hrx5_B4_I_after_rest (hn_snapshot4 T N (p, sh, P)) p P P' sn.
Proof.
  intros T N p sh P P' Hp Hr Hhs Hlic.
  exists (hs_snap_cur T p P).
  apply hrx5_B4_I_after_and6; auto.
Qed.

Definition hrx5_B4_I_after_ok1 (x: val * share * peer) : Prop :=
  match x with (a, sh, P) =>
    sh = Ews /\ hs_ok (p_hs P) /\ 0 <= Int64.unsigned (hs_lic (p_hs P)) < 2 ^ 62
  end.

Lemma hrx5_B4_I_after_some : forall T PS NS PS' s a P,
  map hn_p NS = map peer_addr4 PS -> Forall2 hrx5_B4_I_after_R PS PS' -> NoDup (map peer_addr4 PS) ->
  Forall hrx5_B4_I_after_ok1 PS -> pk_find PS s = Some (a, P) ->
  exists NS1 N NS2 P' sn,
    hrx5_B4_I_fm (hnodes_snapped4 T NS PS) PS' s = Some (N, (a, Ews, P')) /\
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
    In (a, Ews, P') PS' /\
    hn_addr N = hrx5_nfind NS a /\ hrx5_B4_I_after_rest N a P P' sn.
Proof.
  intros T PS NS PS' s a P Hmap HR. revert NS Hmap.
  induction HR as [|[[x sh] Q] [[x' sh'] Q'] PS PS' HR1 HR IH]; intros NS Hmap Hnd Hok Hf;
    [discriminate|].
  destruct NS as [|N0 NS]; [discriminate|]. simpl in Hmap. inv Hmap.
  destruct HR1 as (<- & <- & Hrs). inv Hok. inv Hnd.
  rename H2 into Hok1. rename H3 into Hok. rename H4 into Hnin. rename H5 into Hnd. rename H1 into Hmap.
  rewrite hrx5_B4_I_after_snapped_cons. simpl in Hf.
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) s) eqn:Hb.
  - inv Hf. destruct Hok1 as (-> & Hhs & Hlic).
    destruct (hrx5_B4_I_after_rest_intro T N0 (hn_p N0) Ews P Q' eq_refl (eq_sym Hrs) Hhs Hlic) as [sn Hrest].
    exists [], (hn_snapshot4 T N0 (hn_p N0, Ews, P)), (hnodes_snapped4 T NS PS), Q', sn.
    rewrite hrx5_B4_I_after_fm_cons. rewrite <- Hrs, Hb.
    rewrite hrx5_B4_I_after_snap_addr.
    split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|].
    split; [simpl; rewrite if_true by auto; reflexivity|]. exact Hrest.
  - destruct (IH NS Hmap Hnd Hok Hf) as (NS1 & N & NS2 & P' & sn & Hfm & Hsn & Hin & Hna & Hrest).
    exists (hn_snapshot4 T N0 (hn_p N0, sh, Q) :: NS1), N, NS2, P', sn.
    rewrite hrx5_B4_I_after_fm_cons. rewrite <- Hrs, Hb.
    split; [exact Hfm|]. split; [rewrite Hsn; reflexivity|]. split; [right; exact Hin|].
    split; [|exact Hrest].
    simpl. rewrite if_false; auto.
    intros <-. apply Hnin. destruct (hrx5_B4_I_after_find_in _ _ _ _ Hf) as [sh0 Hin0].
    change (hn_p N0) with (peer_addr4 (hn_p N0, sh0, P)). apply in_map; auto.
Qed.

Lemma hrx5_B4_I_after_and4 : forall A B C D: Prop, A -> B -> C -> D -> A /\ B /\ C /\ D.
Proof. auto. Qed.

(* the nodes after the snapshot against the peers (the model block runs before the kernel's call: the peers are
   PS), against the harness's model *)
Definition hrx5_B4_I_after_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall R L NS PS KE T head nk,
    hrx5_inv x25519 R L NS PS KE T head nk ->
    hnodes_peers4 (hnodes_snapped4 T NS PS) PS /\
    Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS /\
    (forall s, pk_find PS s = None -> hrx5_B4_I_fm (hnodes_snapped4 T NS PS) PS s = None) /\
    (forall s a P, pk_find PS s = Some (a, P) ->
       exists NS1 N NS2 P' sn,
         hrx5_B4_I_fm (hnodes_snapped4 T NS PS) PS s = Some (N, (a, Ews, P')) /\
         hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
         In (a, Ews, P') PS /\
         hn_addr N = hrx5_nfind NS a /\ hrx5_B4_I_after_rest N a P P' sn).

Lemma hrx5_B4_I_after_ok x25519 : hrx5_B4_I_after_stmt x25519.
Proof.
  intros R L NS PS KE T head nk Hl.
  destruct Hl as (Hpok & _ & Hnd & _ & Hnp & _). unfold hnodes_peers4 in Hnp.
  pose proof (hrx5_B4_I_after_refl PS) as HR.
  assert (Hok: Forall hrx5_B4_I_after_ok1 PS).
  { rewrite Forall_forall in Hpok |- *. intros [[a sh] P] Hin.
    specialize (Hpok _ Hin). simpl in Hpok |- *.
    destruct Hpok as (? & _ & _ & ? & _ & _ & ? & _). auto. }
  apply hrx5_B4_I_after_and4.
  - unfold hnodes_peers4. rewrite hrx5_B4_I_after_map by auto. rewrite Hnp. reflexivity.
  - rewrite Forall_forall in Hok |- *. intros [[a sh] P] Hin. apply (Hok _ Hin).
  - intros s Hf. apply hrx5_B4_I_after_none; auto.
  - intros s a P Hf. exact (hrx5_B4_I_after_some T PS NS PS s a P Hnp HR Hnd Hok Hf).
Qed.

(* lengths of the model's values *)
Lemma hrx5_B4_I_len_blake2s key m : Zlength (blake2s key 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma hrx5_B4_I_len_hmac k d : Zlength (hmac k d) = 32.
Proof. unfold hmac, HASH. apply hrx5_B4_I_len_blake2s. Qed.

Lemma hrx5_B4_I_kdf2_len ck d : Zlength (kdf2 ck d) = 32.
Proof. unfold kdf2. apply hrx5_B4_I_len_hmac. Qed.

Definition hrx5_B4_I_len_stmt (x25519: list byte -> list byte -> list byte)
  (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) : Prop :=
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  (forall R, hrx5_run_ok R ->
     Zlength (mi_priv (hrx5_ID x25519 R)) = 32 /\ Zlength (mi_pub (hrx5_ID x25519 R)) = 32) /\
  (forall I EPH ENCS s key ck h, Zlength ENCS = 48 ->
     m_consume_init1_model x25519 aead_dec I EPH ENCS = Some (s, key, ck, h) ->
     Zlength s = 32 /\ Zlength key = 32 /\ Zlength ck = 32 /\ Zlength h = 32) /\
  (forall I PUB, Zlength (m_precomputed_model x25519 I PUB) = 32) /\
  (forall SS CK H ENCT t ck h, Zlength ENCT = 28 ->
     m_consume_init2_model aead_dec SS CK H ENCT = Some (t, ck, h) ->
     Zlength t = 12 /\ Zlength ck = 32 /\ Zlength h = 32).

Lemma hrx5_B4_I_len_ok x25519 aead_enc aead_dec : hrx5_B4_I_len_stmt x25519 aead_enc aead_dec.
Proof.
  intros HX HA. split; [| split; [| split]].
  - intros R (HB & _). unfold hrx5_ID, mident_of; cbn [mi_priv mi_pub]. split; [| apply HX].
    unfold clamp. rewrite !upd_Znth_Zlength; auto; try rewrite upd_Znth_Zlength; lia.
  - intros I EPH ENCS s key ck h HL H.
    unfold m_consume_init1_model, consume_init_stage1 in H; cbn [im_eph im_encs id_priv id_pub] in H.
    destruct (negb _); [discriminate |].
    destruct (aead_dec _ _ _ _) eqn:E; inv H.
    apply (aead_dec_length _ _ HA) in E. cbn [im_encs] in E.
    unfold kdf1, kdf2, mix_hash, HASH. rewrite !hrx5_B4_I_len_hmac, hrx5_B4_I_len_blake2s. lia.
  - intros I PUB. unfold m_precomputed_model. destruct (andb _ _); [apply HX | reflexivity].
  - intros SS CK H ENCT t ck h HL H0.
    unfold m_consume_init2_model, consume_init_stage2 in H0.
    destruct (negb _); [discriminate |].
    destruct (aead_dec _ _ _ _) eqn:E; inv H0.
    apply (aead_dec_length _ _ HA) in E. cbn [im_enct] in E.
    unfold kdf1, mix_hash, HASH. rewrite hrx5_B4_I_len_hmac, hrx5_B4_I_len_blake2s. lia.
Qed.
