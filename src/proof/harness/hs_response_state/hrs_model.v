(* The model facts behind the law hs_response_state (harness/hs_response_state.c), pure Coq over
   prot_model3.v.

   A's index table holds one entry, the handshake entry of A's peer; create_initiation re-inserts it with the
   index it drew (hrs_insert0).  consume_response looks the response's receiver index up in that table and
   finds at most this entry, whose peer is A's peer: the one peer it is given.  Whatever the table, a peer
   whose handshake is not in the state HANDSHAKE_CREATED_INITIATION accepts no response (hrs_cre_none). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

(* A's index table after an insertion with index idx: its peer's handshake entry, hashed, with that index *)
Definition hrs_tab (sh: share) (pa: val) (idx: int) : tstate :=
  mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE idx)] [hs_addr pa].

(* the insertion into the table new_pair builds (the entry unhashed, index 0) *)
Lemma hrs_insert0 sh pa idx :
  t_insert (mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE Int.zero)] []) (hs_addr pa) idx = hrs_tab sh pa idx.
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd, hrs_tab. simpl.
  rewrite !if_true by reflexivity. reflexivity.
Qed.

(* the table new_pair builds holds the peer's handshake entry *)
Lemma hrs_table0_in_pool sh pa : hs_in_pool (mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE Int.zero)] []) pa.
Proof. unfold hs_in_pool, t_entry. simpl. rewrite if_true by reflexivity. eexists; split; reflexivity. Qed.

(* the table's entry belongs to the one peer of the device, which holds a reference *)
Lemma hrs_pool_peers_ok sh pa i shp P :
  p_refs P <> Int.zero -> pool_peers_ok (hrs_tab sh pa i) [(pa, shp, P)].
Proof.
  intros HR. unfold pool_peers_ok, hrs_tab. simpl. constructor; [| constructor].
  split.
  - exists shp, P. simpl. rewrite if_true by reflexivity. split; auto.
  - left. split; reflexivity.
Qed.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* consume_initiation on a device with one peer: the accepted peer is that one, of the same device *)
Lemma hrs_cin_single ID a sh P M now b P' :
  consume_initiation_model x25519 aead_dec ID [(a, sh, P)] M now = Some (b, P') ->
  b = a /\ p_device P' = p_device P.
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

(* the law's model: with one peer, whose handshake is not waiting for a response, consume_response accepts
   no peer, whatever the index table *)
Lemma hrs_cre_none ID T a sh P M :
  Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = false ->
  consume_response_model x25519 aead_dec ID T [(a, sh, P)] M = None.
Proof.
  intros Hs. unfold consume_response_model.
  destruct (negb (id_has ID)); [reflexivity |].
  destruct (t_lookup T IDX_HANDSHAKE (rm_receiver M)) as [[? E]|]; [| reflexivity].
  cbn [sfind]. destruct (eq_dec a (e_peer E)); [| reflexivity].
  destruct (peer_get P); [| reflexivity].
  rewrite Hs. reflexivity.
Qed.

End Model.
