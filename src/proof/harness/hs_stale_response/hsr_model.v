(* The model facts behind the law hs_stale_response (harness/hs_stale_response.c), pure Coq over
   prot_model3.v.

   A's index table holds one entry, the handshake entry of A's peer.  Each successful create_initiation
   re-inserts it with the index it drew (t_insert), so after the second initiation the table lists that entry
   with the second index only.  B's response names the first index (create_response copies the receiver
   index from the sender index that consume_initiation stored), so when the two indices differ the lookup of
   consume_response finds nothing and A accepts no peer. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

(* A's index table after an insertion with index idx: its peer's handshake entry, hashed, with that index *)
Definition hsr_tab (sh: share) (pa: val) (idx: int) : tstate :=
  mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE idx)] [hs_addr pa].

(* the first insertion, into the table new_pair builds (the entry unhashed, index 0) *)
Lemma hsr_insert0 sh pa idx :
  t_insert (mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE Int.zero)] []) (hs_addr pa) idx = hsr_tab sh pa idx.
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd, hsr_tab. simpl.
  rewrite !if_true by reflexivity. reflexivity.
Qed.

(* a later insertion replaces the index *)
Lemma hsr_insert sh pa i j : t_insert (hsr_tab sh pa i) (hs_addr pa) j = hsr_tab sh pa j.
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd, hsr_tab. cbn.
  rewrite !if_true by reflexivity. cbn. rewrite !if_true by reflexivity. reflexivity.
Qed.

Lemma hsr_in_pool sh pa i : hs_in_pool (hsr_tab sh pa i) pa.
Proof.
  unfold hs_in_pool, hsr_tab, t_entry. simpl. rewrite if_true by reflexivity.
  eexists; split; reflexivity.
Qed.

(* the table's entry belongs to the one peer of the device, which holds a reference *)
Lemma hsr_pool_peers_ok sh pa i shp P :
  p_refs P <> Int.zero -> pool_peers_ok (hsr_tab sh pa i) [(pa, shp, P)].
Proof.
  intros HR. unfold pool_peers_ok, hsr_tab. simpl. constructor; [| constructor].
  split.
  - exists shp, P. simpl. rewrite if_true by reflexivity. split; auto.
  - left. split; reflexivity.
Qed.

(* the lookup of any other index finds nothing *)
Lemma hsr_lookup_other sh pa i j : Int.eq i j = false -> t_lookup (hsr_tab sh pa i) IDX_HANDSHAKE j = None.
Proof.
  intros E. unfold t_lookup, hsr_tab. cbn [t_find_index t_L]. unfold t_entry. cbn [sfind t_D].
  rewrite if_true by reflexivity. cbn [e_index]. rewrite E.
  reflexivity.
Qed.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* a successful create_initiation sends the index it drew *)
Lemma hsr_ci_sender ID H M r ts idx :
  fst (fst (create_initiation_model x25519 aead_enc ID H M r ts idx)) = true ->
  im_sender (snd (fst (create_initiation_model x25519 aead_enc ID H M r ts idx))) = idx.
Proof.
  unfold create_initiation_model.
  destruct (negb (id_has ID)); [discriminate |].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    first [discriminate | reflexivity].
Qed.

(* create_initiation keeps the handshake's static identity pointer *)
Lemma hsr_ci_sid ID H M r ts idx :
  hs_sid (snd (create_initiation_model x25519 aead_enc ID H M r ts idx)) = hs_sid H.
Proof.
  unfold create_initiation_model.
  destruct (negb (id_has ID)); [reflexivity |].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* consume_initiation on a device with one peer: the accepted peer is that one, of the same device, and it
   stores the message's sender index as its remote index *)
Lemma hsr_cin_single ID a sh P M now b P' :
  consume_initiation_model x25519 aead_dec ID [(a, sh, P)] M now = Some (b, P') ->
  b = a /\ p_device P' = p_device P /\ hs_rindex (p_hs P') = im_sender M.
Proof.
  unfold consume_initiation_model.
  destruct (negb (id_has ID)); [discriminate |].
  destruct (consume_init_stage1 x25519 aead_dec ID M) as [[[[s ?] ck1] h1]|]; [| discriminate].
  cbn [pk_find]. destruct (bytes_eqb _ _); [| discriminate].
  unfold peer_get. destruct (Int.eq (p_refs P) Int.zero); [discriminate |].
  destruct (consume_init_stage2 aead_dec _ ck1 h1 M) as [[[t ck2] h2]|]; [| discriminate].
  destruct (orb _ _); [discriminate |].
  intros E; inv E. auto.
Qed.

(* the peers after consume_initiation on one peer: one peer at the same address; if it was accepted, it is of
   the same device and its remote index is the message's sender index *)
Lemma hsr_cin_after ID a sh P M now :
  peers_after [(a, sh, P)] (consume_initiation_model x25519 aead_dec ID [(a, sh, P)] M now) =
  [(a, sh, match consume_initiation_model x25519 aead_dec ID [(a, sh, P)] M now with
           | Some (_, P') => P' | None => P end)].
Proof.
  destruct (consume_initiation_model _ _ _ _ _ _) as [[b P']|] eqn:E; [| reflexivity].
  apply hsr_cin_single in E. destruct E as [-> _]. cbn. rewrite if_true by reflexivity. reflexivity.
Qed.

(* create_response keeps the peer's device and reference count (it changes the handshake only) and a
   successful one answers the remote index *)
Lemma hsr_cr_receiver H M r idx :
  fst (fst (create_response_model x25519 aead_enc H M r idx)) = true ->
  rm_receiver (snd (fst (create_response_model x25519 aead_enc H M r idx))) = hs_rindex H.
Proof.
  unfold create_response_model.
  destruct (negb (Int.eq (hs_state H) HS_CONSUMED_INITIATION)); [discriminate |].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    first [discriminate | reflexivity].
Qed.

(* the law's model: consume_response with A's table after the second insertion, of index j, and a response
   to another index finds no handshake and accepts no peer *)
Lemma hsr_cre_none ID sh pa j PS M :
  Int.eq j (rm_receiver M) = false ->
  consume_response_model x25519 aead_dec ID (hsr_tab sh pa j) PS M = None.
Proof.
  intros E. unfold consume_response_model. rewrite hsr_lookup_other by exact E.
  destruct (negb (id_has ID)); reflexivity.
Qed.

End Model.
