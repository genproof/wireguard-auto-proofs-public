(* law replay (harness/replay.c): the harness's shadow model as plain Coq and its agreement with the
   protocol model.

   - hrp3_ts: what the harness's model chain computes for a message (ib.ok && m_consume_initiation_1 &&
     bytes_eq(spub, ia.pub) && m_consume_initiation_2): Some (timestamp, chaining key, hash);
   - hrp3_acc: acc = that AND m_ts_newer(ts, latest) AND m_not_flood(last, now);
   - hrp3_pa_ok: B's peer for A (pa) as the loop keeps it: its setup state PA0 with the handshake's mutable
     fields replaced, latest timestamp = the shadow model's `latest`, last consumption = `last`;
   - hrp3_ta_ok: A's index table holds exactly pb's handshake entry in its pool.
*)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the harness's model chain up to the timestamp: IB = B's m_identity, IApub = ia.pub, ss = ss_b *)
Definition hrp3_ts (IB: mident) (IApub ss: list byte) (M: init_msg)
  : option (list byte * list byte * list byte) :=
  if mi_ok IB then
    match m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) with
    | Some (s, _, ck1, h1) =>
      if bytes_eqb s IApub then
        match m_consume_init2_model aead_dec ss ck1 h1 (im_enct M) with
        | Some (t, ck2, h2) => Some (t, ck2, h2)
        | None => None
        end
      else None
    | None => None
    end
  else None.

(* acc *)
Definition hrp3_acc (IB: mident) (IApub ss latest: list byte) (last now: int64) (M: init_msg)
  : option (list byte * list byte * list byte) :=
  match hrp3_ts IB IApub ss M with
  | Some (t, ck, h) => if ts_newer t latest && not_flood last now then Some (t, ck, h) else None
  | None => None
  end.

(* B's peer for A: PA0 (setup_peer's) with the mutable handshake fields replaced *)
Definition hrp3_pa_ok (PA0 PA: peer) (latest: list byte) (last: int64) : Prop :=
  let H0 := p_hs PA0 in
  exists st reph h ck ri,
    PA = p_set_hs PA0 (mkHS st last (hs_sid H0) (hs_eph H0) (hs_rstatic H0) reph (hs_ss H0) (hs_psk H0)
                            h ck latest ri).

(* B's peer after consume_initiation accepted M with the model's (t, ck, h) at boot time now *)
Definition hrp3_pa_after (PA: peer) (M: init_msg) (t ck h: list byte) (now: int64) : peer :=
  let H := p_hs PA in
  p_set_hs (p_set_refs PA (rc_add1 (p_refs PA)))
    (mkHS HS_CONSUMED_INITIATION (last_consumption (hs_lic H) now) (hs_sid H) (hs_eph H) (hs_rstatic H)
          (im_eph M) (hs_ss H) (hs_psk H) h ck t (im_sender M)).

(* A's index table: its pool is pb's handshake entry *)
Definition hrp3_ta_ok (pb: val) (TA: tstate) : Prop :=
  exists E, t_D TA = [(hs_addr pb, Tsh, E)] /\ e_peer E = pb.

(* B's index table: pa's (unhashed) handshake entry, as setup_peer leaves it *)
Definition hrp3_E0 (pa: val) : entry := mkEntry pa IDX_HANDSHAKE Int.zero.
Definition hrp3_TB0 (pa: val) : tstate := t_add (mkT [] []) (hs_addr pa) Tsh (hrp3_E0 pa).

End Model.

(* ------------------------------------------------------------------------------------------------ *)
(* The lemmas; the segment lemmas of main take *)
(* hrp3_model_facts as a hypothesis                                                                *)
(* ------------------------------------------------------------------------------------------------ *)

Definition hrp3_model_facts : Prop :=
  forall (x25519: list byte -> list byte -> list byte)
         (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
         (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)),
  (* consume_initiation on B's single peer agrees with the harness's acc *)
  (forall (DB: device) (wb pa: val) (RAWA RAWB PSK: list byte) (PA0 PA: peer) (latest: list byte)
          (last: int64) (S: shim) (M: init_msg),
     d_id DB = setup_identity x25519 RAWB ->
     PA0 = setup_peer_val x25519 DB wb pa nullval (x25519 RAWA basepoint9) PSK (Int64.repr 2) ->
     hrp3_pa_ok PA0 PA latest last ->
     cin_res x25519 aead_dec DB [(pa, Tsh, PA)] M S =
       match hrp3_acc x25519 aead_dec (mident_of x25519 RAWB) (x25519 RAWA basepoint9)
               (m_precomputed_model x25519 (mident_of x25519 RAWB) (x25519 RAWA basepoint9))
               latest last (s_boot S) M with
       | Some (t, ck, h) => Some (pa, hrp3_pa_after PA M t ck h (s_boot S))
       | None => None
       end) /\
  (* after the acceptance and wg_peer_put, the invariant holds again with the new latest / last *)
  (forall (PA0 PA: peer) latest last M t ck h now,
     p_refs PA0 = Int.one -> hrp3_pa_ok PA0 PA latest last ->
     hrp3_pa_ok PA0
       (p_set_refs (hrp3_pa_after PA M t ck h now) (Int.sub (Int.add Int.one Int.one) Int.one))
       t (last_consumption last now)) /\
  (* the replay of the last accepted message is rejected *)
  (forall IB IApub ss latest last now M t ck h,
     hrp3_ts x25519 aead_dec IB IApub ss M = Some (t, ck, h) -> ts_newer t latest = false ->
     hrp3_acc x25519 aead_dec IB IApub ss latest last now M = None) /\
  (* an accepted message: its timestamp is newer than the old latest, and not newer than itself *)
  (forall IB IApub ss latest last now M t ck h,
     hrp3_acc x25519 aead_dec IB IApub ss latest last now M = Some (t, ck, h) ->
     hrp3_ts x25519 aead_dec IB IApub ss M = Some (t, ck, h) /\ ts_newer t t = false) /\
  (* A's table after a successful create_initiation *)
  (forall pb TA idx, hrp3_ta_ok pb TA -> hrp3_ta_ok pb (t_insert TA (hs_addr pb) idx)) /\
  (forall pb TA, hrp3_ta_ok pb TA -> hs_in_pool TA pb) /\
  (* create_initiation keeps the handshake's static identity *)
  (forall D P M S r idx,
     hs_sid (snd (ci_res x25519 aead_enc D P M S r idx)) = hs_sid (p_hs P)) /\
  (* the snapshot comparison of an unchanged handshake *)
  (forall sn, snap_eqb sn sn = true) /\
  (* the bounds of the clocks: m_last_consumption keeps last below 2^62 *)
  (forall last now, Int64.unsigned last < 2 ^ 62 -> Int64.unsigned now < 2 ^ 62 ->
     Int64.unsigned (last_consumption last now) < 2 ^ 62).

Lemma hrp3_bytes_eqb_sym (a b: list byte) : bytes_eqb a b = bytes_eqb b a.
Proof.
  unfold bytes_eqb; destruct (list_eq_dec Byte.eq_dec a b), (list_eq_dec Byte.eq_dec b a);
    subst; congruence.
Qed.

Lemma hrp3_bytes_eqb_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb; destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hrp3_memcmp_newer (t l: list byte) : Z.leb (memcmp_Z t l) 0 = negb (ts_newer t l).
Proof.
  revert l; induction t as [|x t IH]; intros [|y l]; simpl; try reflexivity.
  destruct (Byte.eq_dec x y) as [E|E].
  - subst; rewrite Byte.eq_true; apply IH.
  - rewrite Byte.eq_false by exact E.
    destruct (Z.leb_spec (Byte.unsigned x - Byte.unsigned y) 0),
             (Z.gtb_spec (Byte.unsigned x) (Byte.unsigned y)); simpl; auto; lia.
Qed.

Lemma hrp3_ts_newer_irrefl (t: list byte) : ts_newer t t = false.
Proof. induction t as [|x t IH]; simpl; auto. rewrite Byte.eq_true; exact IH. Qed.

Lemma hrp3_snap_eqb_refl (sn: hsnap) : snap_eqb sn sn = true.
Proof.
  destruct sn as [[ep et ei] nx hd [st lic sid eph rs reph ss psk h ck ts ri]];
    unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite !Int.eq_true, !Int64.eq_true, !hrp3_bytes_eqb_refl, Bool.eqb_reflx.
  repeat rewrite (proj2 (eqb_true_iff _ _) eq_refl).
  destruct (EqDec_val ep ep), (EqDec_val nx nx), (EqDec_val sid sid); try congruence.
  reflexivity.
Qed.

Theorem hrp3_model_lemmas : hrp3_model_facts.
Proof.
  intros x25519 aead_enc aead_dec.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - (* (1) *)
    intros DB wb pa RAWA RAWB PSK PA0 PA latest last S M HID HPA0 [st [reph [h [ck [ri HPA]]]]].
    subst PA PA0.
    unfold cin_res, consume_initiation_model, hrp3_acc, hrp3_ts, m_consume_init1_model,
      m_consume_init2_model, mident_of, m_precomputed_model.
    unfold setup_peer_val, hs_initial, precomputed; rewrite HID;
    unfold setup_identity, identity_of; simpl.
    destruct (memneq_bool RAWB zeros32) eqn:HR; simpl; [|reflexivity].
    destruct (memneq_bool (x25519 RAWB basepoint9) zeros32) eqn:HP; simpl; [|reflexivity].
    unfold consume_init_stage1; simpl.
    destruct (negb (dh_ok x25519 (clamp RAWB) (im_eph M))); [reflexivity|].
    destruct (aead_dec _ _ _ (im_encs M)) as [s|]; [|reflexivity].
    rewrite (hrp3_bytes_eqb_sym s).
    destruct (bytes_eqb (x25519 RAWA basepoint9) s); [|reflexivity].
    unfold peer_get; simpl.
    unfold consume_init_stage2; simpl.
    destruct (negb (memneq_bool _ zeros32)); [reflexivity|].
    destruct (aead_dec _ _ _ (im_enct M)) as [t|]; [|reflexivity].
    rewrite hrp3_memcmp_newer.
    unfold not_flood, hrp3_pa_after, last_consumption; simpl.
    destruct (ts_newer t latest), (s64_le _ (s_boot S)); reflexivity.
  - (* (2) *)
    intros PA0 PA latest last M t ck h now HR [st [reph [h0 [ck0 [ri HPA]]]]]; subst PA.
    exists HS_CONSUMED_INITIATION, (im_eph M), h, ck, (im_sender M).
    destruct PA0; simpl in *; subst.
    unfold hrp3_pa_after, p_set_refs, p_set_hs; simpl. reflexivity.
  - (* (3) *)
    intros IB IApub ss latest last now M t ck h HT HN.
    unfold hrp3_acc; rewrite HT, HN; reflexivity.
  - (* (4) *)
    intros IB IApub ss latest last now M t ck h HA.
    unfold hrp3_acc in HA.
    destruct (hrp3_ts x25519 aead_dec IB IApub ss M) as [[[t' ck'] h']|]; [|discriminate].
    destruct (ts_newer t' latest && not_flood last now); inversion HA; subst.
    split; [reflexivity | apply hrp3_ts_newer_irrefl].
  - (* (5) *)
    intros pb TA idx [E [HD HE]].
    unfold hrp3_ta_ok, t_insert, t_set_index, t_upd, t_entry; simpl. rewrite HD; simpl.
    destruct (EqDec_val (hs_addr pb) (hs_addr pb)); [|congruence]; simpl.
    eexists; split; [reflexivity|]; simpl; exact HE.
  - (* (6) *)
    intros pb TA [E [HD HE]].
    exists E; unfold t_entry; rewrite HD; simpl.
    destruct (EqDec_val (hs_addr pb) (hs_addr pb)); [|congruence].
    split; [reflexivity | exact HE].
  - (* (7) *)
    intros D P M S r idx.
    unfold ci_res, create_initiation_model.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
  - (* (8) *)
    apply hrp3_snap_eqb_refl.
  - (* (9) *)
    intros last now HL HN; unfold last_consumption.
    destruct (Int64.lt _ _); assumption.
Qed.
