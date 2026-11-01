(* law handshake_receive: COPY of consume_initiation_any's hci5_model.v: the harness's model
   of the call (common.h's m_consume_initiation_1 / _2, the first-match loop over the nodes, m_precomputed,
   m_ts_newer, m_not_flood, m_last_consumption), and its agreement with the kernel's consume_initiation (prot_model3's
   consume_initiation_model through prot_specs4's cin_res).  Pure Coq; port of v1's hci3_model.v / hci3_defs.v
   (hci3_tgt, hci3_new, hci3_agree): the peers hold ANY count of references below INT_MAX (the model's
   peer_get is refcount_inc_not_zero, rc_add1), so the accepted peer's count is rc_add1 of the old one.
*)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the harness's model (the target block): the accepted peer (address, its state before the call), the decrypted
   timestamp, chaining key and hash; the peer found by the first-match loop over the nodes (= pk_find over the
   peers, same order), the timestamp and the last consumption from the node's snapshot (= the peer's state before
   the call) *)
Definition hrx5ci_tgt (IB: mident) (PS: list (val * share * peer)) (M: init_msg) (now: int64)
  : option (val * peer * list byte * list byte * list byte) :=
  if mi_ok IB then
    match m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) with
    | None => None
    | Some (s, _, ck1, h1) =>
      match pk_find PS s with
      | None => None
      | Some (a, P) =>
        match m_consume_init2_model aead_dec (m_precomputed_model x25519 IB (hs_rstatic (p_hs P))) ck1 h1
                (im_enct M) with
        | None => None
        | Some (t, ck2, h2) =>
          if (ts_newer t (hs_ts (p_hs P)) && not_flood (hs_lic (p_hs P)) now)%bool
          then Some (a, P, t, ck2, h2) else None
        end
      end
    end
  else None.

(* the accepted peer's new state (the kernel's, in the harness's terms): one more reference (refcount_t) *)
Definition hrx5ci_new (P: peer) (M: init_msg) (now: int64) (t ck2 h2: list byte) : peer :=
  let H := p_hs P in
  p_set_hs (p_set_refs P (rc_add1 (p_refs P)))
    (mkHS HS_CONSUMED_INITIATION (last_consumption (hs_lic H) now) (hs_sid H) (hs_eph H) (hs_rstatic H)
          (im_eph M) (hs_ss H) (hs_psk H) h2 ck2 t (im_sender M)).

(* the result of the kernel's call, as the harness's model predicts it *)
Definition hrx5ci_res (IB: mident) (PS: list (val * share * peer)) (M: init_msg) (now: int64) : option (val * peer) :=
  match hrx5ci_tgt IB PS M now with
  | Some (a, P, t, ck2, h2) => Some (a, hrx5ci_new P M now t ck2 h2)
  | None => None
  end.

(* the pure facts the agreement needs of every peer: the precomputed static-static is that of the device's
   identity, and the peer holds a reference (draw_peer_refs: 1 .. INT_MAX - 1) *)
Definition hrx5ci_peer_pure (ID: identity) (x: val * share * peer) : Prop :=
  match x with (_, _, P) =>
    hs_ss (p_hs P) = precomputed x25519 ID (hs_rstatic (p_hs P)) /\ p_refs P <> Int.zero
  end.

(* memcmp's replay test is the negation of m_ts_newer (any lengths) *)
Lemma hrx5ci_model_replay t ts : Z.leb (WgNoise.proof.libc.spec.memcmp_Z t ts) 0 = negb (ts_newer t ts).
Proof.
  revert ts; induction t as [|x t IH]; intros [|y ts]; simpl; auto.
  destruct (Byte.eq_dec x y) as [<-|n].
  - rewrite Byte.eq_true. apply IH.
  - rewrite Byte.eq_false by auto.
    destruct (Z.leb_spec (Byte.unsigned x - Byte.unsigned y) 0);
      destruct (Z.gtb_spec (Byte.unsigned x) (Byte.unsigned y)); simpl; auto; lia.
Qed.

Lemma hrx5ci_model_pk_find PS s a P :
  pk_find PS s = Some (a, P) -> exists sh, In (a, sh, P) PS.
Proof.
  induction PS as [|[[a0 sh0] P0] PS IH]; simpl; [discriminate |].
  destruct (bytes_eqb _ _).
  - intros H; inversion H; subst; eauto.
  - intros H; destruct (IH H) as [sh Hin]; eauto.
Qed.

Lemma hrx5ci_model_id_has RAW : id_has (identity_of x25519 (mkId zeros32 zeros32 false) RAW) = mi_ok (mident_of x25519 RAW).
Proof. reflexivity. Qed.

Lemma hrx5ci_model_id RAW : mi_ok (mident_of x25519 RAW) = true ->
  identity_of x25519 (mkId zeros32 zeros32 false) RAW =
  mkId (mi_pub (mident_of x25519 RAW)) (mi_priv (mident_of x25519 RAW)) (mi_ok (mident_of x25519 RAW)).
Proof.
  intros H. unfold mident_of in H |- *; simpl in H |- *.
  apply andb_prop in H; destruct H as [H1 H2].
  unfold identity_of. rewrite H1, H2. reflexivity.
Qed.

(* the agreement: B's identity is that of its raw key (setup_device), every peer as hrx5ci_peer_pure *)
Lemma hrx5ci_agree RAWB D PS M S :
  d_id D = identity_of x25519 (mkId zeros32 zeros32 false) RAWB ->
  Forall (hrx5ci_peer_pure (d_id D)) PS ->
  cin_res x25519 aead_dec D PS M S = hrx5ci_res (mident_of x25519 RAWB) PS M (s_boot S).
Proof.
  intros Hd Hall.
  unfold cin_res, hrx5ci_res, hrx5ci_tgt.
  unfold consume_initiation_model. rewrite Hd, hrx5ci_model_id_has.
  destruct (mi_ok (mident_of x25519 RAWB)) eqn:Hok; [| reflexivity].
  cbn [negb].
  pose proof (hrx5ci_model_id _ Hok) as Hid. rewrite Hok in Hid. rewrite Hid.
  unfold m_consume_init1_model.
  replace (consume_init_stage1 x25519 aead_dec _ M) with
    (consume_init_stage1 x25519 aead_dec (mkId (mi_pub (mident_of x25519 RAWB)) (mi_priv (mident_of x25519 RAWB)) true)
       (mkIM Int.zero Int.zero (im_eph M) (im_encs M) [] [] [])) by reflexivity.
  destruct (consume_init_stage1 _ _ _ _) as [[[[s k] ck1] h1]|]; [| reflexivity].
  destruct (pk_find PS s) as [[a P]|] eqn:Hf; [| reflexivity].
  destruct (hrx5ci_model_pk_find _ _ _ _ Hf) as [sh Hin].
  rewrite Forall_forall in Hall. specialize (Hall _ Hin). simpl in Hall.
  destruct Hall as (Hss & Hrefs).
  unfold peer_get. rewrite Int.eq_false by exact Hrefs.
  assert (Hpre: hs_ss (p_hs P) =
    m_precomputed_model x25519 (mident_of x25519 RAWB) (hs_rstatic (p_hs P))).
  { rewrite Hss, Hd, Hid. unfold precomputed, m_precomputed_model. rewrite Hok. reflexivity. }
  replace (consume_init_stage2 aead_dec (hs_ss (p_hs P)) ck1 h1 M) with
    (m_consume_init2_model aead_dec (hs_ss (p_hs P)) ck1 h1 (im_enct M)) by reflexivity.
  rewrite Hpre at 1.
  destruct (m_consume_init2_model _ _ _ _ _) as [[[t ck2] h2]|]; [| reflexivity].
  rewrite hrx5ci_model_replay.
  unfold not_flood, hrx5ci_new, last_consumption.
  destruct (ts_newer t _), (s64_le _ _); reflexivity.
Qed.

End Model.
