(* The law hs_session_erases, pure part (prot_model3.v).

   hse_bs_erases is the law in the model: a wg_noise_handshake_begin_session that returns true has replaced the
   handshake by hs_zero of it (state ZEROED, ephemeral private key, remote ephemeral, hash and chaining key all
   zero); add_new_keypair and the table's replace do not touch the handshake.

   The other lemmas give main the facts begin_session's specification asks for after the four handshake steps
   on hs_laws.h's pair: each index table still holds just its peer's handshake entry (now hashed, with a new
   index), the peers keep their device and their empty keypair slots, and a consume step on a one-peer list
   can only return that peer. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------ *)
(* begin_session                                                                                    *)
(* ------------------------------------------------------------------------------------------------ *)

(* add_new_keypair changes only the keypair slots of the peer *)
Lemma hse_add_new_hs P new init W : p_hs (fst (add_new_keypair_model P new init W)) = p_hs P.
Proof.
  unfold add_new_keypair_model. destruct init; [destruct (negb _) |]; reflexivity.
Qed.

(* the law in the model *)
Lemma hse_bs_erases P hs k kc W :
  fst (fst (fst (begin_session_model P hs k kc W))) = true ->
  p_hs (snd (fst (fst (begin_session_model P hs k kc W)))) = hs_zero (p_hs P).
Proof.
  unfold begin_session_model.
  destruct (negb _); [discriminate |].
  destruct (eq_dec k nullval); [discriminate |].
  destruct (p_dead P); [discriminate |].
  match goal with |- context [add_new_keypair_model ?P1 ?k ?i ?W1] =>
    pose proof (hse_add_new_hs P1 k i W1) as E; destruct (add_new_keypair_model P1 k i W1) as [P2 W2] end.
  destruct (t_replace (kw_T W2) hs k) as [ok T3]. simpl in *. intros _. exact E.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The index tables                                                                                 *)
(* ------------------------------------------------------------------------------------------------ *)

(* the table of a device of hs_laws.h after its create step: its peer's handshake entry, hashed, index idx *)
Definition hse_table1 (sh: share) (pa: val) (idx: int) : tstate :=
  mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE idx)] [hs_addr pa].

Lemma hse_insert sh pa idx0 idx :
  t_insert (mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE idx0)] []) (hs_addr pa) idx = hse_table1 sh pa idx.
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd, hse_table1. simpl.
  destruct (EqDec_val (hs_addr pa) (hs_addr pa)) as [_ | n]; [| congruence]. simpl.
  destruct (EqDec_val (hs_addr pa) (hs_addr pa)) as [_ | n]; [reflexivity | congruence].
Qed.

Lemma hse_table1_hs sh pa idx : hs_in_pool (hse_table1 sh pa idx) pa.
Proof.
  exists (mkEntry pa IDX_HANDSHAKE idx). unfold t_entry, hse_table1. simpl.
  destruct (EqDec_val (hs_addr pa) (hs_addr pa)) as [_ | n]; [auto | congruence].
Qed.

Lemma hse_table1_kps sh pa idx : kps_in_pool (hse_table1 sh pa idx) pa [].
Proof. split; constructor. Qed.

Lemma hse_table1_peers sh pa idx P :
  p_refs P <> Int.zero -> pool_peers_ok (hse_table1 sh pa idx) [(pa, sh, P)].
Proof.
  intros Hr. unfold pool_peers_ok, hse_table1. simpl. constructor; [| constructor].
  split; [| left; split; reflexivity].
  exists sh, P. simpl. destruct (EqDec_val pa pa) as [_ | n]; [auto | congruence].
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The consume steps on a one-peer list                                                             *)
(* ------------------------------------------------------------------------------------------------ *)

Section Consume.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* consume_initiation can only accept the one peer; it takes a reference and sets its handshake *)
Lemma hse_cin_one ID a sh P M now b P' :
  consume_initiation_model x25519 aead_dec ID [(a, sh, P)] M now = Some (b, P') ->
  b = a /\ exists H', P' = p_set_hs (p_set_refs P (rc_add1 (p_refs P))) H'.
Proof.
  unfold consume_initiation_model.
  destruct (negb (id_has ID)); [discriminate |].
  destruct (consume_init_stage1 _ _ ID M) as [[[[s x] ck1] h1] |]; [| discriminate].
  simpl pk_find. destruct (bytes_eqb (hs_rstatic (p_hs P)) s); [| discriminate].
  unfold peer_get. destruct (Int.eq (p_refs P) Int.zero); [discriminate |].
  destruct (consume_init_stage2 _ _ _ _ _) as [[[t ck2] h2] |]; [| discriminate].
  destruct (orb _ _); [discriminate |].
  intros E; inv E. split; [reflexivity | eexists; reflexivity].
Qed.

(* consume_response can only accept the one peer; it takes a reference and sets its handshake *)
Lemma hse_cre_one ID T a sh P M b P' :
  consume_response_model x25519 aead_dec ID T [(a, sh, P)] M = Some (b, P') ->
  b = a /\ exists H', P' = p_set_hs (p_set_refs P (rc_add1 (p_refs P))) H'.
Proof.
  unfold consume_response_model.
  destruct (negb (id_has ID)); [discriminate |].
  destruct (t_lookup T IDX_HANDSHAKE (rm_receiver M)) as [[x E] |]; [| discriminate].
  simpl sfind. destruct (EqDec_val a (e_peer E)) as [Ea | ]; [| discriminate].
  unfold peer_get. destruct (Int.eq (p_refs P) Int.zero); [discriminate |].
  destruct (negb _); [discriminate |].
  destruct (consume_resp_crypto _ _ _ _ _) as [[ck h] |]; [| discriminate].
  intros E1; inv E1. split; [reflexivity | eexists; reflexivity].
Qed.

End Consume.

(* a peer with empty slots satisfies begin_session's slot condition with no keypairs *)
Lemma hse_slots_nil P :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval -> slots_ok P [].
Proof.
  intros H1 H2 H3. unfold slots_ok. rewrite H1, H2, H3. split.
  - repeat constructor.
  - simpl. destruct (EqDec_val nullval nullval) as [_ | n]; [constructor | congruence].
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The handshake entry survives begin_session                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma hse_sfind_supd {A: Type} (l: list (val * share * A)) a b v : a <> b -> sfind (supd l a v) b = sfind l b.
Proof.
  intros Hab. induction l as [| [[x sh] w] l IH]; simpl; [reflexivity |].
  destruct (EqDec_val x a) as [-> |]; simpl.
  - destruct (EqDec_val a b); [congruence | reflexivity].
  - destruct (EqDec_val x b); [reflexivity | exact IH].
Qed.

Lemma hse_sfind_saddrs {A: Type} (l: list (val * share * A)) a sh v : sfind l a = Some (sh, v) -> In a (saddrs l).
Proof.
  induction l as [| [[x sh0] w] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a) as [-> |]; [auto | intros E; right; auto].
Qed.

(* a peer with empty keypair slots: begin_session's puts do nothing *)
Lemma hse_add_new_nil P new init W :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  snd (add_new_keypair_model P new init W) = W.
Proof.
  intros Hc Hp Hn. unfold add_new_keypair_model. rewrite Hc, Hp, Hn.
  assert (E0: forall b W', kp_put nullval b W' = W')
    by (intros; unfold kp_put; destruct (eq_dec nullval nullval) as [e | n]; [reflexivity | congruence]).
  destruct init; [destruct (negb _) |]; simpl; rewrite ?E0; reflexivity.
Qed.

(* begin_session on a peer with empty slots and no keypairs, whose table holds its handshake entry (share sh)
   and does not hold the new keypair k: the table still holds the handshake entry, with the same share *)
Lemma hse_bs_find P p k kc T S sh E :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  sfind (t_D T) (hs_addr p) = Some (sh, E) ->
  (k <> nullval -> ~ In k (saddrs (t_D T))) ->
  exists E', sfind (t_D (kw_T (snd (fst (begin_session_model P (hs_addr p) k kc (mkKW [] T S)))))) (hs_addr p)
             = Some (sh, E').
Proof.
  intros Hc Hp Hn HE Hk. unfold begin_session_model. cbn [kw_KS kw_T kw_S].
  destruct (negb _); [eexists; exact HE |].
  destruct (eq_dec k nullval) as [Kn | Kn]; [eexists; exact HE |].
  destruct (p_dead P); [eexists; exact HE |].
  assert (Hkh: k <> hs_addr p).
  { intros ->. apply (Hk Kn). eapply hse_sfind_saddrs; exact HE. }
  match goal with |- context [add_new_keypair_model ?P1 ?k ?i ?W1] =>
    pose proof (hse_add_new_nil P1 k i W1 Hc Hp Hn) as EW; destruct (add_new_keypair_model P1 k i W1) as [P2 W2] end.
  simpl in EW. subst W2.
  destruct (t_replace _ (hs_addr p) k) as [ok T3] eqn:ER. simpl.
  unfold t_replace in ER. destruct (vin _ _); inv ER; simpl.
  - unfold t_set_index. destruct (t_entry _ k) as [E0 |]; simpl.
    + destruct (EqDec_val k k) as [e | n]; [| congruence]. simpl.
      destruct (EqDec_val k (hs_addr p)); [congruence |]. eexists; exact HE.
    + destruct (EqDec_val k (hs_addr p)); [congruence |]. eexists; exact HE.
  - destruct (EqDec_val k (hs_addr p)); [congruence |]. eexists; exact HE.
Qed.
