(* law cookie_reply, phase P7: the pure facts of the loop over the peers: the peers' facts survive peer_randomize_rest
   (hcy5_p7_upd), the handshake entry is in A's pool, an insert keeps hcy5_T_ok (fresh index), a pushed
   cnode keeps hcy5_cl_nodes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p7_defs.

Local Open Scope Z_scope.

(* 1. main's updates keep the addresses *)
Lemma hcy5_p7_pure_addrs PS PS' : Forall2 hcy5_p7_upd PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; simpl; auto.
  destruct x as [[a sh] P], y as [[a' sh'] P']. destruct Hxy as [-> _]. simpl. f_equal; auto.
Qed.

(* 2. .. and the peers' facts *)
Lemma hcy5_p7_pure_pok L KS PS PS' :
  Forall2 hcy5_p7_upd PS PS' -> Forall (hcy5_pok L KS) PS -> Forall (hcy5_pok L KS) PS'.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; intros HF; auto.
  inversion HF as [| ? ? Hx HF']; subst. constructor; auto.
  destruct x as [[a sh] P], y as [[a' sh'] P'].
  destruct Hxy as [-> [-> (dead & lsh & valid & birth & ck & sent & mac1 & ->)]].
  exact Hx.
Qed.

Lemma hcy5_p7_pure_chain PS PS' : Forall2 hcy5_p7_upd PS PS' -> forall h, pk_chain h PS -> pk_chain h PS'.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; intros h Hc; auto.
  destruct x as [[a sh] P], y as [[a' sh'] P'].
  destruct Hxy as [-> [-> (dead & lsh & valid & birth & ck & sent & mac1 & ->)]].
  destruct Hc as [Hh Hc]. split; [exact Hh |]. apply IH. exact Hc.
Qed.

(* 5. the head *)
Lemma hcy5_p7_pure_phead PS PS' : map peer_addr4 PS' = map peer_addr4 PS -> hcy5_phead PS' = hcy5_phead PS.
Proof.
  destruct PS as [| [[a sh] P] PS], PS' as [| [[a' sh'] P'] PS']; simpl; intros H; try discriminate; auto.
  inversion H; auto.
Qed.

Lemma hcy5_p7_pure_lists L KS NS PS PS' :
  Forall2 hcy5_p7_upd PS PS' -> hcy5_lists_ok L KS NS PS -> hcy5_lists_ok L KS NS PS'.
Proof.
  intros H (HF & Hnp & Hd1 & Hd2 & Hc). pose proof (hcy5_p7_pure_addrs _ _ H) as Ha.
  split; [eapply hcy5_p7_pure_pok; eauto |].
  unfold hnodes_peers4 in *. rewrite Ha.
  split; [exact Hnp | split; [exact Hd1 | split; [exact Hd2 |]]].
  rewrite (hcy5_p7_pure_phead _ _ Ha). eapply hcy5_p7_pure_chain; eauto.
Qed.

(* 3. np *)
Lemma hcy5_p7_pure_combine PS PS' : Forall2 hcy5_p7_upd PS PS' ->
  forall (NS: list hnode4) N a sh P, In (N, (a, sh, P)) (combine NS PS) ->
  exists P', In (N, (a, sh, P')) (combine NS PS') /\ p_hs P' = p_hs P.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; intros NS N a sh P Hin.
  - destruct NS; simpl in Hin; contradiction.
  - destruct NS as [| M NS]; simpl in Hin; [contradiction |].
    destruct Hin as [Heq | Hin].
    + destruct x as [[b shb] Q], y as [[b' shb'] Q'].
      destruct Hxy as [-> [-> (dead & lsh & valid & birth & ck & sent & mac1 & ->)]].
      inversion Heq; subst. eexists. split; [left; reflexivity | reflexivity].
    + destruct (IH NS N a sh P Hin) as [P' [HP' HH]]. exists P'. split; [right; exact HP' | exact HH].
Qed.

Lemma hcy5_p7_pure_np pubB NS PS PS' np :
  Forall2 hcy5_p7_upd PS PS' -> hcy5_np_ok pubB NS PS np -> hcy5_np_ok pubB NS PS' np.
Proof.
  intros H [Hn | (N & a & P & Hin & Ha & Hk)]; [left; exact Hn | right].
  destruct (hcy5_p7_pure_combine _ _ H _ _ _ _ _ Hin) as [P' [HP' HH]].
  exists N, a, P'. split; [exact HP' | split; [exact Ha | rewrite HH; exact Hk]].
Qed.

(* 4. the table *)
Lemma hcy5_p7_pure_Tok PS PS' KE T :
  map peer_addr4 PS' = map peer_addr4 PS -> hcy5_T_ok PS KE T -> hcy5_T_ok PS' KE T.
Proof. intros Ha. unfold hcy5_T_ok. rewrite Ha. auto. Qed.

(* the pool of the handshake entries *)
Lemma hcy5_p7_pure_saddrs ix AS : saddrs (map (hcy5_hent ix) AS) = map hs_addr AS.
Proof. induction AS as [| x AS IH]; simpl; auto. f_equal; auto. Qed.

(* 6. a peer's handshake entry is in the pool *)
Lemma hcy5_p7_pure_in PS T a :
  hcy5_T_ok PS [] T -> In a (map peer_addr4 PS) -> In (hs_addr a) (saddrs (t_D T)).
Proof.
  intros [(own & ix & HD & _) _] Hin. rewrite HD. unfold hcy5_pool. simpl. rewrite hcy5_p7_pure_saddrs.
  apply in_map; exact Hin.
Qed.

(* 7. insert *)
Lemma hcy5_p7_pure_sfind_ix AS ix1 ix2 b : ix1 b = ix2 b ->
  sfind (map (hcy5_hent ix1) AS) b = sfind (map (hcy5_hent ix2) AS) b.
Proof.
  intros Hb. induction AS as [| x AS IH]; simpl; auto.
  destruct (eq_dec (hs_addr x) b) as [e | n]; [| rewrite !if_false by exact n; exact IH].
  rewrite !if_true by exact e. rewrite e, Hb. reflexivity.
Qed.

Lemma hcy5_p7_pure_sfind_in AS ix a : NoDup (map hs_addr AS) -> In a AS ->
  sfind (map (hcy5_hent ix) AS) (hs_addr a) = Some (Ews, mkEntry a IDX_HANDSHAKE (ix (hs_addr a))).
Proof.
  induction AS as [| x AS IH]; simpl; intros Hd Hin; [contradiction |].
  inversion Hd as [| ? ? Hx Hd']; subst.
  destruct (EqDec_val (hs_addr x) (hs_addr a)) as [e | n].
  - destruct Hin as [-> | Hin]; [reflexivity |].
    exfalso. apply Hx. rewrite e. apply in_map; exact Hin.
  - destruct Hin as [-> | Hin]; [congruence |]. apply IH; auto.
Qed.

Lemma hcy5_p7_pure_supd AS ix a idx : NoDup (map hs_addr AS) -> In a AS ->
  supd (map (hcy5_hent ix) AS) (hs_addr a) (mkEntry a IDX_HANDSHAKE idx) =
  map (hcy5_hent (fun v => if eq_dec v (hs_addr a) then idx else ix v)) AS.
Proof.
  induction AS as [| x AS IH]; simpl; intros Hd Hin; [contradiction |].
  inversion Hd as [| ? ? Hx Hd']; subst.
  destruct (EqDec_val (hs_addr x) (hs_addr a)) as [e | n].
  - destruct Hin as [-> | Hin]; [| exfalso; apply Hx; rewrite e; apply in_map; exact Hin].
    unfold hcy5_hent at 2. rewrite if_true by reflexivity. f_equal.
    apply map_ext_in. intros y Hy. unfold hcy5_hent.
    rewrite if_false; [reflexivity |]. intros E. apply Hx. rewrite <- E. apply in_map; exact Hy.
  - destruct Hin as [-> | Hin]; [congruence |].
    unfold hcy5_hent at 2. rewrite if_false by exact n. f_equal. apply IH; auto.
Qed.

Lemma hcy5_p7_pure_nodup_vremove {B: Type} (f: val -> B) h L : NoDup (map f L) -> NoDup (map f (vremove h L)).
Proof.
  induction L as [| x L IH]; simpl; intros Hd; auto.
  inversion Hd as [| ? ? Hx Hd']; subst.
  destruct (EqDec_val x h); auto. simpl. constructor; auto.
  intros Hin. apply Hx. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
  rewrite <- Hy. apply in_map.
  clear - Hiny. induction L as [| z L IH]; simpl in *; auto.
  destruct (EqDec_val z h); [right; auto |]. destruct Hiny as [-> | H]; [left; auto | right; auto].
Qed.

Lemma hcy5_p7_pure_vremove_ne h L x : In x (vremove h L) -> x <> h.
Proof.
  induction L as [| y L IH]; simpl; [contradiction |].
  destruct (EqDec_val y h) as [e | n]; auto. intros [-> | H]; auto.
Qed.

Lemma hcy5_p7_pure_insert PS T a idx :
  hcy5_T_ok PS [] T -> itable_wf T -> In a (map peer_addr4 PS) -> t_fresh T (hs_addr a) idx ->
  hcy5_T_ok PS [] (t_insert T (hs_addr a) idx).
Proof.
  intros [(own & ix & HD & _) Hidx] (_ & _ & HdD & _) Hin Hfr.
  set (AS := map peer_addr4 PS) in *.
  unfold hcy5_pool in HD. simpl in HD.
  assert (Hd: NoDup (map hs_addr AS)) by (rewrite HD, hcy5_p7_pure_saddrs in HdD; exact HdD).
  set (ix' := fun v => if eq_dec v (hs_addr a) then idx else ix v).
  assert (HE: t_entry T (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE (ix (hs_addr a)))).
  { unfold t_entry. rewrite HD, hcy5_p7_pure_sfind_in; auto. }
  assert (HD': t_D (t_insert T (hs_addr a) idx) = map (hcy5_hent ix') AS).
  { unfold t_insert, t_set_index. rewrite HE. unfold t_upd. simpl. rewrite HD.
    apply hcy5_p7_pure_supd; auto. }
  split.
  - exists own, ix'. split; [rewrite HD'; reflexivity | constructor].
  - assert (HL: t_L (t_insert T (hs_addr a) idx) = hs_addr a :: vremove (hs_addr a) (t_L T)).
    { unfold t_insert, t_set_index. rewrite HE. reflexivity. }
    assert (Hb: forall b, In b (vremove (hs_addr a) (t_L T)) ->
      t_entry (t_insert T (hs_addr a) idx) b = t_entry T b).
    { intros b Hb. unfold t_entry. rewrite HD', HD.
      rewrite (hcy5_p7_pure_sfind_ix AS ix' ix b); [reflexivity |].
      unfold ix'. rewrite if_false; [reflexivity |]. eapply hcy5_p7_pure_vremove_ne; eauto. }
    assert (Ha: t_entry (t_insert T (hs_addr a) idx) (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx)).
    { unfold t_entry. rewrite HD'. rewrite hcy5_p7_pure_sfind_in by auto.
      unfold ix'. rewrite if_true by reflexivity. reflexivity. }
    unfold t_indices. rewrite HL. cbn [map]. rewrite Ha. cbn [e_index].
    rewrite (map_ext_in _ (fun b => match t_entry T b with Some E => e_index E | None => Int.zero end))
      by (intros b Hin'; rewrite Hb by exact Hin'; reflexivity).
    constructor.
    + exact Hfr.
    + apply hcy5_p7_pure_nodup_vremove. exact Hidx.
Qed.

(* 8. a pushed cnode *)
Lemma hcy5_p7_pure_cl_push CL NS1 cn N :
  hcy5_cl_nodes CL NS1 -> ~ In cn (map (fun x => fst (fst x)) CL) ->
  hcy5_cl_nodes ((cn, hn_addr N, None) :: CL) (NS1 ++ [N]).
Proof.
  intros [Hm Hd] Hn. split.
  - simpl. rewrite Hm, map_app, rev_app_distr. reflexivity.
  - simpl. constructor; auto.
Qed.

(* every fact at once *)
Lemma hcy5_p7_pure_all :
  (* 1. peer_randomize_rest keeps the addresses *)
  (forall PS PS', Forall2 hcy5_p7_upd PS PS' -> map peer_addr4 PS' = map peer_addr4 PS) /\
  (* 2. .. and the peers' facts (device, identity, references, cookie keys, slots, pubkey_next) *)
  (forall L KS NS PS PS',
     Forall2 hcy5_p7_upd PS PS' -> hcy5_lists_ok L KS NS PS -> hcy5_lists_ok L KS NS PS') /\
  (* 3. .. and the handshakes *)
  (forall pubB NS PS PS' np,
     Forall2 hcy5_p7_upd PS PS' -> hcy5_np_ok pubB NS PS np -> hcy5_np_ok pubB NS PS' np) /\
  (* 4. the table *)
  (forall PS PS' KE T,
     map peer_addr4 PS' = map peer_addr4 PS -> hcy5_T_ok PS KE T -> hcy5_T_ok PS' KE T) /\
  (* 5. the head *)
  (forall PS PS', map peer_addr4 PS' = map peer_addr4 PS -> hcy5_phead PS' = hcy5_phead PS) /\
  (* 6. a peer's handshake entry is in A's pool *)
  (forall PS T a, hcy5_T_ok PS [] T -> In a (map peer_addr4 PS) -> In (hs_addr a) (saddrs (t_D T))) /\
  (* 7. wg_index_hashtable_insert of a peer's handshake entry (raw = None) with a fresh index *)
  (forall PS T a idx,
     hcy5_T_ok PS [] T -> itable_wf T -> In a (map peer_addr4 PS) -> t_fresh T (hs_addr a) idx ->
     hcy5_T_ok PS [] (t_insert T (hs_addr a) idx)) /\
  (* 8. a new cnode (its address not yet a cnode's) for the next node *)
  (forall CL NS1 cn N,
     hcy5_cl_nodes CL NS1 -> ~ In cn (map (fun x => fst (fst x)) CL) ->
     hcy5_cl_nodes ((cn, hn_addr N, None) :: CL) (NS1 ++ [N])).
Proof.
  split; [exact hcy5_p7_pure_addrs |].
  split; [exact hcy5_p7_pure_lists |].
  split; [exact hcy5_p7_pure_np |].
  split; [exact hcy5_p7_pure_Tok |].
  split; [exact hcy5_p7_pure_phead |].
  split; [exact hcy5_p7_pure_in |].
  split; [exact hcy5_p7_pure_insert |].
  exact hcy5_p7_pure_cl_push.
Qed.

Lemma hcy5_p7_addrs PS PS' : Forall2 hcy5_p7_upd PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_lists L KS NS PS PS' :
  Forall2 hcy5_p7_upd PS PS' -> hcy5_lists_ok L KS NS PS -> hcy5_lists_ok L KS NS PS'.
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_np pubB NS PS PS' np :
  Forall2 hcy5_p7_upd PS PS' -> hcy5_np_ok pubB NS PS np -> hcy5_np_ok pubB NS PS' np.
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_Tok PS PS' KE T :
  map peer_addr4 PS' = map peer_addr4 PS -> hcy5_T_ok PS KE T -> hcy5_T_ok PS' KE T.
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_phead PS PS' : map peer_addr4 PS' = map peer_addr4 PS -> hcy5_phead PS' = hcy5_phead PS.
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_in PS T a :
  hcy5_T_ok PS [] T -> In a (map peer_addr4 PS) -> In (hs_addr a) (saddrs (t_D T)).
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_insert PS T a idx :
  hcy5_T_ok PS [] T -> itable_wf T -> In a (map peer_addr4 PS) -> t_fresh T (hs_addr a) idx ->
  hcy5_T_ok PS [] (t_insert T (hs_addr a) idx).
Proof. apply hcy5_p7_pure_all. Qed.

Lemma hcy5_p7_cl_push CL NS1 cn N :
  hcy5_cl_nodes CL NS1 -> ~ In cn (map (fun x => fst (fst x)) CL) ->
  hcy5_cl_nodes ((cn, hn_addr N, None) :: CL) (NS1 ++ [N]).
Proof. apply hcy5_p7_pure_all. Qed.
