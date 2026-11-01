(* The model facts behind the law hs_reject_response (harness/hs_reject_response.c), pure Coq over
   prot_model3.v:
   - create_initiation keeps the handshake's static identity pointer (same_peer reads it through the
     identity of A's device);
   - consume_initiation on a device with one peer leaves one peer at the same address and of the same
     device (B's peer, for the create_response that follows);
   - consume_response on a device with one peer at a non-NULL address accepts that peer or none, so a NULL
     result means no peer changed: the law's "nothing changes on rejection". *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* create_initiation changes no static identity pointer *)
Lemma hrr_ci_sid ID H M r ts idx :
  hs_sid (snd (create_initiation_model x25519 aead_enc ID H M r ts idx)) = hs_sid H.
Proof.
  unfold create_initiation_model.
  destruct (negb (id_has ID)); [reflexivity |].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* the peers after a step on a one-peer list: one peer, same address, same device *)
Lemma hrr_after_single a sh P res :
  (forall b P', res = Some (b, P') -> p_device P' = p_device P) ->
  exists P', peers_after [(a, sh, P)] res = [(a, sh, P')] /\ p_device P' = p_device P.
Proof.
  intros Hd. destruct res as [[b P']|]; cbn [peers_after supd].
  - destruct (eq_dec a b); [exists P'; split; [reflexivity | eapply Hd; reflexivity] |].
    exists P; split; reflexivity.
  - exists P; split; reflexivity.
Qed.

(* consume_initiation on one peer: the accepted peer is that one, with its device *)
Lemma hrr_cin_single ID a sh P M now b P' :
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
  intros E; inv E. split; reflexivity.
Qed.

(* B's peers after consume_initiation: one peer, at the same address, of the same device *)
Lemma hrr_cin_after ID a sh P M now :
  exists P', peers_after [(a, sh, P)] (consume_initiation_model x25519 aead_dec ID [(a, sh, P)] M now) =
             [(a, sh, P')] /\ p_device P' = p_device P.
Proof.
  apply hrr_after_single. intros b P' E. apply (hrr_cin_single _ _ _ _ _ _ _ _ E).
Qed.

(* consume_response on one peer: the accepted peer is that one *)
Lemma hrr_cre_single ID T a sh P M b P' :
  consume_response_model x25519 aead_dec ID T [(a, sh, P)] M = Some (b, P') -> b = a.
Proof.
  unfold consume_response_model.
  destruct (negb (id_has ID)); [discriminate |].
  destruct (t_lookup T IDX_HANDSHAKE (rm_receiver M)) as [[? E]|]; [| discriminate].
  cbn [sfind]. destruct (eq_dec a (e_peer E)) as [Ea|]; [| discriminate].
  destruct (peer_get P); [| discriminate].
  destruct (negb _); [discriminate |].
  destruct (consume_resp_crypto _ _ _ _ _) as [[? ?]|]; [| discriminate].
  intros Ee; inv Ee. reflexivity.
Qed.

(* the law's model: if consume_response returns NULL on one peer at a pointer, it accepted nothing, and
   the peers are as they were *)
Lemma hrr_cre_null ID T a sh P M :
  isptr a ->
  peer_result (consume_response_model x25519 aead_dec ID T [(a, sh, P)] M) = nullval ->
  consume_response_model x25519 aead_dec ID T [(a, sh, P)] M = None.
Proof.
  intros Ha. destruct (consume_response_model _ _ _ _ _ _) as [[b P']|] eqn:E; [| reflexivity].
  apply hrr_cre_single in E. subst b. cbn [peer_result]. intros ->. inv Ha.
Qed.

(* an index table whose pool is one entry keeps one entry, at the same address and of the same peer and type,
   through an insert (create_initiation, create_response) *)
Lemma hrr_insert_single a sh E L b idx :
  exists E', t_D (t_insert (mkT [(a, sh, E)] L) b idx) = [(a, sh, E')] /\
             e_peer E' = e_peer E /\ e_type E' = e_type E.
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd. cbn [t_D sfind supd].
  destruct (eq_dec a b); cbn [t_D supd].
  - exists (mkEntry (e_peer E) (e_type E) idx). auto.
  - exists E. auto.
Qed.

(* in a table whose pool is the one entry at a, the entry has no successor *)
Lemma hrr_succ_single (L: list val) (a: val) :
  NoDup L -> incl L [a] -> succ_in L a = nullval.
Proof.
  intros HN HI. destruct L as [|x [|y L]]; cbn [succ_in]; [reflexivity | |].
  - destruct (eq_dec x a); reflexivity.
  - exfalso. assert (x = a) by (destruct (HI x (or_introl eq_refl)) as [->|[]]; reflexivity).
    assert (y = a) by (destruct (HI y (or_intror (or_introl eq_refl))) as [->|[]]; reflexivity).
    subst. inv HN. apply H1. left. reflexivity.
Qed.

End Model.
