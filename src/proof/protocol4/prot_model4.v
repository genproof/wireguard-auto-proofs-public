(* the refcount_t WARNINGS of the keypair functions, over the same
   arguments as their v3 models (prot_model3.v: kp_get, kp_put, add_new_keypair_model,
   received_with_keypair_model, keypairs_clear_model, begin_session_model).  Each wg_noise_keypair_put is one
   refcount_dec_and_test (rc_dec_warn of the count it finds), each wg_noise_keypair_get one
   refcount_inc_not_zero (rc_inc_warn ... _inz); the chains follow the models' kp_put order exactly.  The counts,
   frees and tables stay those of the v3 models (which already saturate: rc_add1 / rc_sub1). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.

(* wg_noise_keypair_get(k) *)
Definition kp_get_warn (k: val) (KS: list (val * keypair)) (w: list int64) : list int64 :=
  if eq_dec k nullval then w else
  match afind KS k with None => w | Some K => rc_inz_warn (kp_refs K) w end.

(* wg_noise_keypair_put(k, unref) *)
Definition kp_put_warn (k: val) (KS: list (val * keypair)) (w: list int64) : list int64 :=
  if eq_dec k nullval then w else
  match afind KS k with None => w | Some K => rc_dec_warn (kp_refs K) w end.

(* add_new_keypair(&P->keypairs, new), new of role init (add_new_keypair_model) *)
Definition add_new_keypair_warn (P: peer) (new: val) (init: bool) (W: kworld) (w: list int64) : list int64 :=
  let prev := p_prev P in let next := p_next P in let cur := p_cur P in
  if init then
    if negb (eq_dec next nullval) then
      let w1 := kp_put_warn cur (kw_KS W) w in
      let W1 := kp_put cur true W in
      kp_put_warn prev (kw_KS W1) w1
    else kp_put_warn prev (kw_KS W) w
  else
    let w1 := kp_put_warn next (kw_KS W) w in
    let W1 := kp_put next true W in
    kp_put_warn prev (kw_KS W1) w1.

(* wg_noise_received_with_keypair(&P->keypairs, k) (received_with_keypair_model) *)
Definition received_with_keypair_warn (P: peer) (k: val) (W: kworld) (w: list int64) : list int64 :=
  if eq_dec k (p_next P) then kp_put_warn (p_prev P) (kw_KS W) w else w.

(* wg_noise_keypairs_clear(&P->keypairs) (keypairs_clear_model) *)
Definition keypairs_clear_warn (P: peer) (W: kworld) (w: list int64) : list int64 :=
  let w1 := kp_put_warn (p_next P) (kw_KS W) w in
  let W1 := kp_put (p_next P) true W in
  let w2 := kp_put_warn (p_prev P) (kw_KS W1) w1 in
  let W2 := kp_put (p_prev P) true W1 in
  kp_put_warn (p_cur P) (kw_KS W2) w2.

(* wg_noise_handshake_begin_session (begin_session_model): only add_new_keypair puts *)
Definition begin_session_warn (P: peer) (hs k: val) (kc: int64) (W: kworld) (w: list int64) : list int64 :=
  let H := p_hs P in
  if negb (orb (Int.eq (hs_state H) HS_CREATED_RESPONSE) (Int.eq (hs_state H) HS_CONSUMED_RESPONSE))
  then w else
  if eq_dec k nullval then w else
  let kc' := Int64.add kc Int64.one in
  let K := kp_new H kc' (s_boot (kw_S W)) in
  let P1 := p_set_hs P (hs_zero H) in
  let S1 := shim_alloc_ok (kw_S W) in
  if p_dead P then w else
  let W1 := mkKW ((k, K) :: kw_KS W) (t_add (kw_T W) k Ews (mkEntry (e_peer_of_hs W hs) IDX_KEYPAIR Int.zero)) S1 in
  add_new_keypair_warn P1 k (kp_init K) W1 w.

(* below saturation nothing warns *)
Lemma kp_put_warn_small k KS w :
  (forall K, afind KS k = Some K -> 0 < Int.unsigned (kp_refs K) < 2147483648) ->
  kp_put_warn k KS w = w.
Proof.
  intros H. unfold kp_put_warn. destruct (eq_dec k nullval); [reflexivity |].
  destruct (afind KS k) as [K |] eqn:E; [| reflexivity].
  apply rc_dec_warn_small, H; reflexivity.
Qed.

Lemma kp_get_warn_small k KS w :
  (forall K, afind KS k = Some K -> 0 < Int.unsigned (kp_refs K) < 2147483647) ->
  kp_get_warn k KS w = w.
Proof.
  intros H. unfold kp_get_warn. destruct (eq_dec k nullval); [reflexivity |].
  destruct (afind KS k) as [K |] eqn:E; [| reflexivity].
  apply rc_inz_warn_small, H; reflexivity.
Qed.
