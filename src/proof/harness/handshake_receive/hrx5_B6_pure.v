(* law handshake_receive, main's phase B6: the PURE agreement of the
   harness's model block (statements 34..38: the load, the macs with the rotation, the path) with the receive model
   rx_model / hrx5_path (hrx5_model.v, hrx5_hmodel.v). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Local Open Scope Z_scope.

(* helpers *)
Lemma hrx5_b6_fwd_len msg : hrx5_fwd msg = true ->
  (Int.eq (hrx5_tw msg) Int.one = true /\ Zlength msg = 148) \/
  (Int.eq (hrx5_tw msg) (Int.repr 2) = true /\ Zlength msg = 92) \/
  (Int.eq (hrx5_tw msg) (Int.repr 3) = true /\ Zlength msg = 64).
Proof.
  unfold hrx5_fwd. intros H. apply andb_prop in H. destruct H as [_ H].
  apply orb_prop in H. destruct H as [H|H]; [apply orb_prop in H; destruct H as [H|H]|];
    apply andb_prop in H; destruct H as [H1 H2]; apply Z.eqb_eq in H2; auto.
Qed.

Lemma hrx5_b6_rlen M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (A & B & C & D). unfold resp_bytes. rewrite !Zlength_app, A, B, C, D. reflexivity.
Qed.

Lemma hrx5_b6_clen M : cm_ok M -> Zlength (cookie_msg_bytes M) = 64.
Proof.
  intros (A & B). unfold cookie_msg_bytes. rewrite !Zlength_app, A, B. reflexivity.
Qed.

Lemma hrx5_b6_ilen M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (A & B & C & D & E). unfold init_bytes. rewrite !Zlength_app, A, B, C, D, E. reflexivity.
Qed.

Lemma hrx5_b6_fresh now : 0 <= Int64.unsigned now < 2 ^ 62 ->
  birthdate_expired now (Int64.repr 120) now = false.
Proof.
  intros Hn. unfold birthdate_expired, s64_le.
  replace (Int64.mul (Int64.repr 120) (Int64.repr NSEC_PER_SEC)) with (Int64.repr 120000000000)
    by reflexivity.
  unfold Int64.lt. rewrite Int64.add_signed.
  rewrite (Int64.signed_repr 120000000000) by rep_lia.
  rewrite Int64.signed_eq_unsigned by rep_lia.
  rewrite Int64.signed_repr by rep_lia.
  destruct (zlt _ _); [reflexivity | lia].
Qed.

Lemma hrx5_b6_rotate_noop CC now r : checker_rotates CC now = false -> checker_rotate CC now r = CC.
Proof. unfold checker_rotate, checker_rotates. intros ->. reflexivity. Qed.

(* after validate asked for a cookie, the checker does not rotate again at the same time *)
Lemma hrx5_b6_norot2 CC s msg ul now rl r : 0 <= Int64.unsigned now < 2 ^ 62 ->
  rx_needs_cookie ul (fst (validate_model CC s msg ul now rl r)) = true ->
  checker_rotates (snd (validate_model CC s msg ul now rl r)) now = false.
Proof.
  intros Hn. unfold rx_needs_cookie, validate_model.
  destruct ul; [| discriminate].
  destruct (negb (bytes_eqb _ _)); [discriminate |]. cbn [negb].
  intros _.
  assert (E: checker_rotates (checker_rotate CC now r) now = false).
  { unfold checker_rotate. destruct (checker_rotates CC now) eqn:E0; unfold checker_rotates in *; rewrite E0.
    - cbn [cc_birth]. apply hrx5_b6_fresh; auto.
    - exact E0. }
  destruct (negb (bytes_eqb _ _)); [exact E |]. destruct rl; exact E.
Qed.

(* the shim's fields the keypair functions never touch *)
Definition hrx5_b6_sk (S S': shim) : Prop :=
  s_rlallow S' = s_rlallow S /\ s_log S' = s_log S /\ s_logprev S' = s_logprev S.

Lemma hrx5_b6_sk_refl S : hrx5_b6_sk S S.
Proof. split; [|split]; reflexivity. Qed.

Lemma hrx5_b6_sk_trans S1 S2 S3 : hrx5_b6_sk S1 S2 -> hrx5_b6_sk S2 S3 -> hrx5_b6_sk S1 S3.
Proof. intros (A & B & C) (D & E & F). split; [|split]; congruence. Qed.

Lemma hrx5_b6_sk_free S : hrx5_b6_sk S (shim_free S).
Proof. split; [|split]; reflexivity. Qed.

Lemma hrx5_b6_sk_release S : hrx5_b6_sk S (shim_release S).
Proof. split; [|split]; reflexivity. Qed.

Lemma hrx5_b6_sk_put k u W : hrx5_b6_sk (kw_S W) (kw_S (kp_put k u W)).
Proof.
  unfold kp_put. destruct (eq_dec k nullval); [apply hrx5_b6_sk_refl |].
  destruct (afind (kw_KS W) k); [| apply hrx5_b6_sk_refl].
  destruct (Int.eq _ _); [apply hrx5_b6_sk_free | apply hrx5_b6_sk_refl].
Qed.

Lemma hrx5_b6_sk_add P new init W : hrx5_b6_sk (kw_S W) (kw_S (snd (add_new_keypair_model P new init W))).
Proof.
  unfold add_new_keypair_model.
  destruct init; [destruct (eq_dec (p_next P) nullval); cbn [negb proj_sumbool snd] |]; cbn [snd];
    repeat (eapply hrx5_b6_sk_trans; [| apply hrx5_b6_sk_put]); apply hrx5_b6_sk_refl.
Qed.

Lemma hrx5_b6_sk_bs P hs k kc W : hrx5_b6_sk (kw_S W) (kw_S (snd (fst (begin_session_model P hs k kc W)))).
Proof.
  unfold begin_session_model.
  destruct (negb _); [apply hrx5_b6_sk_refl |].
  destruct (eq_dec k nullval); [split; [|split]; reflexivity |].
  destruct (p_dead P); [split; [|split]; reflexivity |].
  match goal with |- context [add_new_keypair_model ?P1 ?k1 ?i1 ?W1] =>
    pose proof (hrx5_b6_sk_add P1 k1 i1 W1) as HA; destruct (add_new_keypair_model P1 k1 i1 W1) as [P2 W2] end.
  destruct (t_replace (kw_T W2) hs k) as [ok T3]. cbn [snd fst kw_S] in *.
  eapply hrx5_b6_sk_trans; [| exact HA]. split; [|split]; reflexivity.
Qed.

Lemma hrx5_b6_log_draw S r : Zlength r = 32 -> s_log (shim_draw S r) = r.
Proof.
  intros Hr. unfold shim_draw. cbn [s_log]. rewrite Hr. change (Z.min 32 32) with 32.
  rewrite sublist_same by lia. rewrite sublist_nil. apply app_nil_r.
Qed.

(* the message objects: a forwarded one has 64..148 bytes; kinds 1 / 2 are not cookie replies, kind 3 is *)
Lemma hrx5_b6_obj (o: hrx5_obj) :
  obj_ok o -> hrx5_fwd (obj_bytes o) = true ->
  64 <= Zlength (obj_bytes o) <= 148 /\
  ((obj_kind o = 1 \/ obj_kind o = 2) -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = false) /\
  (obj_kind o <> 1 -> obj_kind o <> 2 -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = true).
Proof.
  intros Ho Hf. pose proof (hrx5_b6_fwd_len _ Hf) as HL.
  destruct o as [b|M|M|M]; cbn [obj_ok obj_bytes obj_kind] in *.
  - destruct Ho as (A & B & C & _). destruct HL as [[_ X]|[[_ X]|[_ X]]]; lia.
  - pose proof (hrx5_b6_ilen _ Ho) as L. rewrite L in HL.
    destruct HL as [[X _]|[[_ X]|[_ X]]]; try lia. apply Int.same_if_eq in X. rewrite X, L.
    split; [lia |]. split; [reflexivity | intros H1; exfalso; lia].
  - pose proof (hrx5_b6_rlen _ Ho) as L. rewrite L in HL.
    destruct HL as [[_ X]|[[X _]|[_ X]]]; try lia. apply Int.same_if_eq in X. rewrite X, L.
    split; [lia |]. split; [reflexivity | intros H1 H2; exfalso; lia].
  - pose proof (hrx5_b6_clen _ Ho) as L. rewrite L in HL.
    destruct HL as [[_ X]|[[_ X]|[X _]]]; try lia. apply Int.same_if_eq in X. rewrite X, L.
    split; [lia |]. split; [intros [H1|H1]; discriminate | intros; reflexivity].
Qed.

(* validate's checker after the call *)
Lemma hrx5_b6_vm_snd CC s msg ul now rl r :
  snd (validate_model CC s msg ul now rl r) =
  if validate_rotates CC msg ul now then checker_rotate CC now r else CC.
Proof.
  unfold validate_model, validate_rotates.
  destruct (bytes_eqb _ _); cbn [negb andb]; [| reflexivity].
  destruct ul; cbn [negb andb]; [| reflexivity].
  destruct (checker_rotates CC now) eqn:E.
  - destruct (negb _); [reflexivity | destruct rl; reflexivity].
  - rewrite (hrx5_b6_rotate_noop _ _ _ E). destruct (negb _); [reflexivity | destruct rl; reflexivity].
Qed.

Section Rx.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Notation rxm := (rx_model x25519 aead_dec xaead_enc xaead_dec).

(* not forwarded: nothing *)
Lemma hrx5_b6_nofwd W q sp s msg d :
  hrx5_fwd msg = false -> rxm W q sp s msg d = W /\ hrx5_path W q s msg d = 0.
Proof.
  intros Hf. unfold rx_model, hrx5_path. rewrite Hf. auto.
Qed.

(* a forwarded cookie reply: the device and last_under_load unchanged, path 1 *)
Lemma hrx5_b6_cookie W q sp s msg d :
  hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = true ->
  rw_lul (rxm W q sp s msg d) = rw_lul W /\ rw_D (rxm W q sp s msg d) = rw_D W /\ hrx5_path W q s msg d = 1.
Proof.
  intros Hf Ht. unfold rx_model, hrx5_path. rewrite Hf. unfold rx_packet. cbv zeta. rewrite Ht.
  cbn [rw_lul rw_D]. auto.
Qed.

(* a forwarded initiation / response: last_under_load = the load model's, the device = validate's checker (a cookie
   reply's create never rotates again: the clock is below 2^62), the rate limiter's flag unchanged, and the path *)
Lemma hrx5_b6_hs W q sp s msg d :
  hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
  0 <= Int64.unsigned (s_boot (rw_S W)) < 2 ^ 62 ->
  let now := s_boot (rw_S W) in
  let ul := fst (load_model q (rw_lul W) now) in
  let vm := validate_model (d_cc (rw_D W)) s msg ul now (s_rlallow (rw_S W)) (rd_r d) in
  rw_lul (rxm W q sp s msg d) = snd (load_model q (rw_lul W) now) /\
  rw_D (rxm W q sp s msg d) = dev_set_cc (rw_D W) (snd vm) /\
  s_rlallow (rw_S (rxm W q sp s msg d)) = s_rlallow (rw_S W) /\
  hrx5_path W q s msg d =
    (if rx_consumes ul (fst vm) then 1 else if rx_needs_cookie ul (fst vm) then 2 else 0).
Proof.
  intros Hf Ht Hb. cbv zeta. unfold rx_model, hrx5_path. rewrite Hf. unfold rx_packet. cbv zeta. rewrite Ht.
  set (now := s_boot (rw_S W)) in *.
  set (ul := fst (load_model q (rw_lul W) now)) in *.
  set (vm := validate_model (d_cc (rw_D W)) s msg ul now (s_rlallow (rw_S W)) (rd_r d)) in *.
  destruct (validate_rotates (d_cc (rw_D W)) msg ul now) eqn:Ev.
  all: destruct (rx_consumes ul (fst vm)) eqn:Ec;
    [| destruct (rx_needs_cookie ul (fst vm)) eqn:En].
  all: try (destruct (Int.eq (hrx5_tw msg) Int.one);
    [destruct (cin_res _ _ _ _ _ _) as [[a P1]|] | destruct (cre_res _ _ _ _ _ _) as [[a P1]|]]).
  all: try unfold rx_init_accepted; try unfold rx_resp_accepted; cbv zeta.
  all: try match goal with |- context [bs_res ?P ?p ?k ?kc ?KS ?T ?S0] =>
    pose proof (hrx5_b6_sk_bs P (hs_addr p) k kc (mkKW KS T S0)) as HB;
    change (bs_res P p k kc KS T S0) with (begin_session_model P (hs_addr p) k kc (mkKW KS T S0));
    destruct (begin_session_model P (hs_addr p) k kc (mkKW KS T S0)) as [[[ok P2] W2] kc2];
    cbn [fst snd kw_S] in HB |- *; destruct HB as (HB1 & HB2 & HB3) end.
  all: cbn [rw_lul rw_D rw_S].
  all: split; [reflexivity |]; split; [| split; [| reflexivity]].
  all: try reflexivity.
  all: try (destruct (Int.eq _ Int.zero); cbn [s_rlallow shim_release shim_draw]; try rewrite HB1;
            cbn [s_rlallow shim_release shim_draw]; reflexivity).
  all: try (destruct (checker_rotates _ _); cbn [s_rlallow shim_release shim_draw]; reflexivity).
  all: unfold mc_res, message_create_model; cbn [snd]; f_equal; cbn [s_boot shim_draw];
    apply hrx5_b6_rotate_noop; apply hrx5_b6_norot2; auto.
Qed.

(* the rotation's draw is the shim's last draw, or the one before when a cookie reply drew its nonce after it *)
Lemma hrx5_b6_log W q sp s msg d :
  hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
  0 <= Int64.unsigned (s_boot (rw_S W)) < 2 ^ 62 ->
  Zlength (rd_r d) = 32 -> Zlength (rd_nonce d) = 24 ->
  let now := s_boot (rw_S W) in
  let ul := fst (load_model q (rw_lul W) now) in
  validate_rotates (d_cc (rw_D W)) msg ul now = true ->
  (hrx5_path W q s msg d = 2 -> s_logprev (rw_S (rxm W q sp s msg d)) = rd_r d) /\
  (hrx5_path W q s msg d <> 2 -> s_log (rw_S (rxm W q sp s msg d)) = rd_r d).
Proof.
  intros Hf Ht Hb Hr Hn. cbv zeta. intros Hv.
  unfold rx_model, hrx5_path. rewrite Hf. unfold rx_packet. cbv zeta. rewrite Ht, Hv.
  set (now := s_boot (rw_S W)) in *.
  set (ul := fst (load_model q (rw_lul W) now)) in *.
  set (vm := validate_model (d_cc (rw_D W)) s msg ul now (s_rlallow (rw_S W)) (rd_r d)) in *.
  destruct (rx_consumes ul (fst vm)) eqn:Ec;
    [| destruct (rx_needs_cookie ul (fst vm)) eqn:En].
  - split; [discriminate | intros _].
    destruct (Int.eq (hrx5_tw msg) Int.one);
      [destruct (cin_res _ _ _ _ _ _) as [[a P1]|] | destruct (cre_res _ _ _ _ _ _) as [[a P1]|]].
    all: try unfold rx_init_accepted; try unfold rx_resp_accepted; cbv zeta.
    all: try match goal with |- context [bs_res ?P ?p ?k ?kc ?KS ?T ?S0] =>
      pose proof (hrx5_b6_sk_bs P (hs_addr p) k kc (mkKW KS T S0)) as HB;
      change (bs_res P p k kc KS T S0) with (begin_session_model P (hs_addr p) k kc (mkKW KS T S0));
      destruct (begin_session_model P (hs_addr p) k kc (mkKW KS T S0)) as [[[ok P2] W2] kc2];
      cbn [fst snd kw_S] in HB |- *; destruct HB as (HB1 & HB2 & HB3) end.
    all: cbn [rw_S].
    all: try (destruct (Int.eq _ Int.zero); cbn [s_log shim_release]; try rewrite HB2).
    all: apply hrx5_b6_log_draw; auto.
  - split; [intros _ | intros H; exfalso; apply H; reflexivity].
    cbn [rw_S]. replace (checker_rotates (snd vm) now) with false by (symmetry; apply hrx5_b6_norot2; auto). cbn [s_logprev shim_draw].
    apply hrx5_b6_log_draw; auto.
  - split; [discriminate | intros _]. cbn [rw_S]. apply hrx5_b6_log_draw; auto.
Qed.

End Rx.

(* the conjunction of this file's lemmas *)
Lemma hrx5_b6_pure_a :
  (forall o, obj_ok o -> hrx5_fwd (obj_bytes o) = true ->
     64 <= Zlength (obj_bytes o) <= 148 /\
     ((obj_kind o = 1 \/ obj_kind o = 2) -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = false) /\
     (obj_kind o <> 1 -> obj_kind o <> 2 -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = true)) /\
  (forall CC s msg ul now rl r, snd (validate_model CC s msg ul now rl r) =
     if validate_rotates CC msg ul now then checker_rotate CC now r else CC) /\
  (forall x25519 aead_dec xaead_enc xaead_dec W q sp s msg d,
     hrx5_fwd msg = false -> rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d = W /\
     hrx5_path W q s msg d = 0) /\
  (forall x25519 aead_dec xaead_enc xaead_dec W q sp s msg d,
     hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = true ->
     rw_lul (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = rw_lul W /\
     rw_D (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = rw_D W /\
     hrx5_path W q s msg d = 1).
Proof.
  split; [exact hrx5_b6_obj |]. split; [exact hrx5_b6_vm_snd |].
  split; [exact hrx5_b6_nofwd | exact hrx5_b6_cookie].
Qed.

Lemma hrx5_b6_pure_b x25519 aead_dec xaead_enc xaead_dec :
  (forall W q sp s msg d,
    hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
    0 <= Int64.unsigned (s_boot (rw_S W)) < 2 ^ 62 ->
    let now := s_boot (rw_S W) in
    let ul := fst (load_model q (rw_lul W) now) in
    let vm := validate_model (d_cc (rw_D W)) s msg ul now (s_rlallow (rw_S W)) (rd_r d) in
    rw_lul (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = snd (load_model q (rw_lul W) now) /\
    rw_D (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = dev_set_cc (rw_D W) (snd vm) /\
    s_rlallow (rw_S (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = s_rlallow (rw_S W) /\
    hrx5_path W q s msg d =
      (if rx_consumes ul (fst vm) then 1 else if rx_needs_cookie ul (fst vm) then 2 else 0)) /\
  (forall W q sp s msg d,
    hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
    0 <= Int64.unsigned (s_boot (rw_S W)) < 2 ^ 62 ->
    Zlength (rd_r d) = 32 -> Zlength (rd_nonce d) = 24 ->
    let now := s_boot (rw_S W) in
    let ul := fst (load_model q (rw_lul W) now) in
    validate_rotates (d_cc (rw_D W)) msg ul now = true ->
    (hrx5_path W q s msg d = 2 ->
       s_logprev (rw_S (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = rd_r d) /\
    (hrx5_path W q s msg d <> 2 ->
       s_log (rw_S (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = rd_r d)).
Proof.
  split; [exact (hrx5_b6_hs x25519 aead_dec xaead_enc xaead_dec) | exact (hrx5_b6_log x25519 aead_dec xaead_enc xaead_dec)].
Qed.

Lemma hrx5_b6_pure_ok :
  ((forall o, obj_ok o -> hrx5_fwd (obj_bytes o) = true ->
     64 <= Zlength (obj_bytes o) <= 148 /\
     ((obj_kind o = 1 \/ obj_kind o = 2) -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = false) /\
     (obj_kind o <> 1 -> obj_kind o <> 2 -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = true)) /\
  (forall CC s msg ul now rl r, snd (validate_model CC s msg ul now rl r) =
     if validate_rotates CC msg ul now then checker_rotate CC now r else CC) /\
  (forall x25519 aead_dec xaead_enc xaead_dec W q sp s msg d,
     hrx5_fwd msg = false -> rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d = W /\
     hrx5_path W q s msg d = 0) /\
  (forall x25519 aead_dec xaead_enc xaead_dec W q sp s msg d,
     hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = true ->
     rw_lul (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = rw_lul W /\
     rw_D (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = rw_D W /\
     hrx5_path W q s msg d = 1)) /\
  (forall x25519 aead_dec xaead_enc xaead_dec, (forall W q sp s msg d,
    hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
    0 <= Int64.unsigned (s_boot (rw_S W)) < 2 ^ 62 ->
    let now := s_boot (rw_S W) in
    let ul := fst (load_model q (rw_lul W) now) in
    let vm := validate_model (d_cc (rw_D W)) s msg ul now (s_rlallow (rw_S W)) (rd_r d) in
    rw_lul (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = snd (load_model q (rw_lul W) now) /\
    rw_D (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d) = dev_set_cc (rw_D W) (snd vm) /\
    s_rlallow (rw_S (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = s_rlallow (rw_S W) /\
    hrx5_path W q s msg d =
      (if rx_consumes ul (fst vm) then 1 else if rx_needs_cookie ul (fst vm) then 2 else 0)) /\
  (forall W q sp s msg d,
    hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
    0 <= Int64.unsigned (s_boot (rw_S W)) < 2 ^ 62 ->
    Zlength (rd_r d) = 32 -> Zlength (rd_nonce d) = 24 ->
    let now := s_boot (rw_S W) in
    let ul := fst (load_model q (rw_lul W) now) in
    validate_rotates (d_cc (rw_D W)) msg ul now = true ->
    (hrx5_path W q s msg d = 2 ->
       s_logprev (rw_S (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = rd_r d) /\
    (hrx5_path W q s msg d <> 2 ->
       s_log (rw_S (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = rd_r d))).
Proof. split; [exact hrx5_b6_pure_a | exact hrx5_b6_pure_b]. Qed.
