(* law hs_replay_initiation: the model argument (plain Coq over prot_model3.v).

   consume_initiation_model accepts a message only if its decrypted timestamp t is greater (memcmp) than the
   peer's latest timestamp, and on acceptance stores t as the new latest timestamp.  The responder's first
   steps (stage1: DH with its static key, decryption of the initiator's static key; stage2: decryption of the
   timestamp from the peer's precomputed static-static DH) are functions of the identity, the message and the
   peer's precomputed DH only.  create_response and begin_session keep the peer's remote static key, its
   precomputed DH and its latest timestamp (handshake_zero clears neither), so the same message given again
   decrypts to the same t, which is not greater than itself: the replay is rejected. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

Local Open Scope Z_scope.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the three fields of a peer's handshake that decide whether an initiation is a replay *)
Definition hri_key (H: handshake) : list byte * list byte * list byte := (hs_rstatic H, hs_ss H, hs_ts H).

(* an accepted initiation: the peer found is the one whose remote static key the message carries; its new
   handshake keeps that key and the precomputed DH, and stores the timestamp the message decrypts to *)
Lemma hri_accept ID PS M now a P' :
  consume_initiation_model x25519 aead_dec ID PS M now = Some (a, P') ->
  exists s key ck1 h1 P t ck2 h2,
    id_has ID = true /\
    consume_init_stage1 x25519 aead_dec ID M = Some (s, key, ck1, h1) /\
    pk_find PS s = Some (a, P) /\
    hs_rstatic (p_hs P) = s /\
    consume_init_stage2 aead_dec (hs_ss (p_hs P)) ck1 h1 M = Some (t, ck2, h2) /\
    hri_key (p_hs P') = (hs_rstatic (p_hs P), hs_ss (p_hs P), t).
Proof.
  unfold consume_initiation_model. intros HC.
  destruct (id_has ID) eqn:Hid; [|discriminate]. cbn [negb] in HC.
  destruct (consume_init_stage1 x25519 aead_dec ID M) as [[[[s key] ck1] h1]|] eqn:H1; [|discriminate].
  destruct (pk_find PS s) as [[b P]|] eqn:Hf; [|discriminate].
  destruct (peer_get P) as [P1|] eqn:Hg; [|discriminate].
  destruct (consume_init_stage2 aead_dec (hs_ss (p_hs P)) ck1 h1 M) as [[[t ck2] h2]|] eqn:H2; [|discriminate].
  destruct (_ || _)%bool; [discriminate|]. inversion HC; subst a P'; clear HC.
  exists s, key, ck1, h1, P, t, ck2, h2. repeat split; auto.
  - clear - Hf. induction PS as [|[[c sh] Q] PS IH]; cbn in Hf; [discriminate|].
    unfold bytes_eqb in Hf. destruct (list_eq_dec Byte.eq_dec (hs_rstatic (p_hs Q)) s) as [E|].
    + inversion Hf; subst; auto.
    + auto.
Qed.

(* the accepted peer's new state: one more reference, a new handshake (keeping the remote static key and the
   precomputed DH) whose last consumption time is the clock or the old one; the other fields as before *)
Lemma hri_accept_peer ID PS M now a P' :
  consume_initiation_model x25519 aead_dec ID PS M now = Some (a, P') ->
  exists sh P H', In (a, sh, P) PS /\ Int.eq (p_refs P) Int.zero = false /\
    P' = p_set_hs (p_set_refs P (rc_add1 (p_refs P))) H' /\
    hs_rstatic H' = hs_rstatic (p_hs P) /\ hs_ss H' = hs_ss (p_hs P) /\
    (hs_lic H' = now \/ hs_lic H' = hs_lic (p_hs P)).
Proof.
  unfold consume_initiation_model. intros HC.
  destruct (id_has ID); [|discriminate]. cbn [negb] in HC.
  destruct (consume_init_stage1 x25519 aead_dec ID M) as [[[[s key] ck1] h1]|]; [|discriminate].
  destruct (pk_find PS s) as [[b P]|] eqn:Hf; [|discriminate].
  destruct (peer_get P) as [P1|] eqn:Hg; [|discriminate].
  destruct (consume_init_stage2 aead_dec (hs_ss (p_hs P)) ck1 h1 M) as [[[t ck2] h2]|]; [|discriminate].
  destruct (_ || _)%bool; [discriminate|]. inversion HC; subst a P'; clear HC.
  assert (HIn: exists sh, In (b, sh, P) PS).
  { clear - Hf. induction PS as [|[[c sh] Q] PS IH]; cbn in Hf; [discriminate|].
    destruct (bytes_eqb _ _).
    - inversion Hf; subst. exists sh; left; auto.
    - destruct (IH Hf) as [sh' H]. exists sh'; right; auto. }
  destruct HIn as [sh HIn]. unfold peer_get in Hg.
  destruct (Int.eq (p_refs P) Int.zero) eqn:Hz; [discriminate|]. inversion Hg; subst P1.
  eexists sh, P, _. split; [exact HIn|]. split; [exact Hz|]. split; [reflexivity|].
  cbn. split; [reflexivity|]. split; [reflexivity|].
  destruct (Int64.lt _ _); auto.
Qed.

(* the same message again, to a single peer at a whose handshake keeps the key of the accepted one: None *)
Lemma hri_replay ID PS M now a P' sh Q now2 :
  consume_initiation_model x25519 aead_dec ID PS M now = Some (a, P') ->
  hri_key (p_hs Q) = hri_key (p_hs P') ->
  consume_initiation_model x25519 aead_dec ID [(a, sh, Q)] M now2 = None.
Proof.
  intros HA HK. destruct (hri_accept _ _ _ _ _ _ HA) as (s & key & ck1 & h1 & P & t & ck2 & h2 & Hid & H1 & Hf & Hs & H2 & HK').
  rewrite HK' in HK. unfold hri_key in HK. inversion HK as [[Hr Hss Ht]].
  unfold consume_initiation_model. rewrite Hid, H1. cbn [negb pk_find].
  unfold bytes_eqb. rewrite Hr, Hs. destruct (list_eq_dec Byte.eq_dec s s) as [_|NE]; [|congruence].
  destruct (peer_get Q); [|reflexivity]. rewrite Hss, H2, Ht, memcmp_Z_refl. reflexivity.
Qed.

(* create_response keeps the key (and the last consumption time) *)
Lemma hri_cr_keeps H M r idx :
  let H' := snd (create_response_model x25519 aead_enc H M r idx) in
  hri_key H' = hri_key H /\ hs_lic H' = hs_lic H.
Proof.
  unfold create_response_model. cbv zeta.
  repeat match goal with |- context [if negb ?b then _ else _] => destruct (negb b) end; split; reflexivity.
Qed.

(* add_new_keypair only moves the keypair slots *)
Lemma hri_ank_keeps P new init W :
  let P' := fst (add_new_keypair_model P new init W) in
  p_hs P' = p_hs P /\ p_refs P' = p_refs P /\ p_device P' = p_device P /\ p_pknext P' = p_pknext P.
Proof.
  unfold add_new_keypair_model. cbv zeta.
  destruct init; [destruct (negb _)|]; repeat split; reflexivity.
Qed.

(* begin_session leaves the handshake as it was or zeroes it (handshake_zero): the key, the last consumption
   time, the reference count and the device are kept *)
Lemma hri_bs_keeps P hs k kc W :
  let P' := snd (fst (fst (begin_session_model P hs k kc W))) in
  hri_key (p_hs P') = hri_key (p_hs P) /\ hs_lic (p_hs P') = hs_lic (p_hs P) /\
  p_refs P' = p_refs P /\ p_device P' = p_device P /\ p_pknext P' = p_pknext P.
Proof.
  unfold begin_session_model.
  destruct (negb _); [cbn; auto|]. destruct (eq_dec k nullval); [cbn; auto|].
  destruct (p_dead P); [cbn; auto|].
  match goal with |- context [add_new_keypair_model ?P1 ?n ?i ?W1] =>
    destruct (hri_ank_keeps P1 n i W1) as (E1 & E2 & E3 & E4); destruct (add_new_keypair_model P1 n i W1) as [P2 W2] end.
  destruct (t_replace _ _ _). cbn in *. rewrite E1, E2, E3, E4. cbn. auto.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The index table of B: its handshake entry stays in the pool, with the same share                  *)
(* ------------------------------------------------------------------------------------------------ *)

(* the entry at a is in the pool of T, with share sh *)
Definition hri_in_pool (T: tstate) (a: val) (sh: share) : Prop := exists E, sfind (t_D T) a = Some (sh, E).

Lemma hri_sfind_supd (D: list (val * share * entry)) a b v sh E :
  sfind D b = Some (sh, E) -> exists E', sfind (supd D a v) b = Some (sh, E').
Proof.
  induction D as [|[[x shx] w] D IH]; cbn; [discriminate|]. intros H.
  destruct (EqDec_val x b) as [Exb|Nxb].
  - subst x. inversion H; subst.
    destruct (EqDec_val b a); cbn; destruct (EqDec_val b b); try congruence; eauto.
  - destruct (EqDec_val x a); cbn; destruct (EqDec_val x b); try congruence; eauto.
Qed.

Lemma hri_in_pool_insert T a idx b sh : hri_in_pool T b sh -> hri_in_pool (t_insert T a idx) b sh.
Proof.
  intros [E H]. unfold hri_in_pool, t_insert, t_set_index, t_upd. cbn.
  destruct (t_entry T a); cbn; [eapply hri_sfind_supd; eauto | eauto].
Qed.

Lemma hri_sfind_supd_same (D: list (val * share * entry)) a v sh E :
  sfind D a = Some (sh, E) -> sfind (supd D a v) a = Some (sh, v).
Proof.
  induction D as [|[[x shx] w] D IH]; cbn; [discriminate|]. intros H.
  destruct (EqDec_val x a) as [->|N]; cbn.
  - inversion H; subst. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | auto].
Qed.

Lemma hri_sfind_supd_other (D: list (val * share * entry)) a b v sh E :
  b <> a -> sfind D b = Some (sh, E) -> sfind (supd D a v) b = Some (sh, E).
Proof.
  intros Nba. induction D as [|[[x shx] w] D IH]; cbn; [discriminate|]. intros H.
  destruct (EqDec_val x a) as [->|N]; cbn.
  - destruct (EqDec_val a b); [congruence | auto].
  - destruct (EqDec_val x b); auto.
Qed.

(* t_insert keeps the handshake entry's peer (it changes the index only) *)
Lemma hri_hs_in_pool_insert T q a idx : hs_in_pool T q -> hs_in_pool (t_insert T a idx) q.
Proof.
  intros (E & HE & HP). unfold hs_in_pool, t_insert, t_set_index, t_upd, t_entry in *. cbn.
  destruct (sfind (t_D T) (hs_addr q)) as [[shq Eq]|] eqn:Hq; [|discriminate]. inversion HE; subst Eq.
  destruct (sfind (t_D T) a) as [[sha Ea]|] eqn:Ha; cbn; [|rewrite Hq; eauto].
  destruct (EqDec_val (hs_addr q) a) as [Eqa|Nqa].
  - rewrite <- Eqa in *. rewrite (hri_sfind_supd_same _ _ _ _ _ Hq). rewrite Ha in Hq. inversion Hq; subst.
    eexists; split; [reflexivity|]. cbn. auto.
  - rewrite (hri_sfind_supd_other _ _ _ _ _ _ Nqa Hq). eauto.
Qed.

(* begin_session on a peer without keypairs (its three slots NULL): the pool keeps the entry at a, provided
   kzalloc's keypair k is not an address of the pool *)
Lemma hri_in_pool_bs P hs k kc T S a sh :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  (k <> nullval -> ~ In k (saddrs (t_D T))) ->
  hri_in_pool T a sh ->
  hri_in_pool (kw_T (snd (fst (begin_session_model P hs k kc (mkKW [] T S))))) a sh.
Proof.
  intros Hc Hp Hn Hk [E HE]. unfold hri_in_pool, begin_session_model.
  destruct (negb _); [cbn; eauto|]. destruct (eq_dec k nullval) as [|Nk]; [cbn; eauto|].
  destruct (p_dead P); [cbn; eauto|].
  assert (Hka: a <> k).
  { intros ->. apply (Hk Nk). clear - HE. induction (t_D T) as [|[[x shx] w] D IH]; cbn in *; [discriminate|].
    destruct (EqDec_val x k); [left; auto | right; auto]. }
  unfold add_new_keypair_model. cbn [p_prev p_next p_cur p_set_hs]. rewrite Hp, Hn, Hc. unfold kp_put. cbv zeta.
  rewrite !(if_true (nullval = nullval)) by auto.
  match goal with |- context [t_add ?T0 k Ews ?E0] => set (T1 := t_add T0 k Ews E0) end.
  assert (H1: sfind (t_D T1) a = Some (sh, E)).
  { unfold T1, t_add. cbn. destruct (EqDec_val k a); [congruence | exact HE]. }
  clearbody T1.
  destruct (kp_init _); [destruct (negb _)|]; cbn [kw_T kw_KS kw_S snd fst]; unfold t_replace;
    destruct (vin hs _); cbn; unfold t_set_index, t_upd; try destruct (t_entry _ k); cbn;
    eauto using hri_sfind_supd_other.
Qed.

End Model.
