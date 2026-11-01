(* law cookie_mac: main's body cut into
   phases. *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_cookie_mac.code.

Module HK := WgNoise.harness.x_cookie_mac.code.

Fixpoint hck5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hck5_seqs l' rest) end.

Fixpoint hck5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hck5_seql l') end.

Fixpoint hck5_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hck5_flat_seq b | _ => [s] end.

Lemma hck5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hck5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hck5_unfold_seqs l rest :
  unfold_Ssequence (hck5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hck5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hck5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hck5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hck5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hck5_seql l) rest)).
  - simpl. rewrite hck5_unfold_seql, hck5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the statements below (the last one is `return 0`) *)
Definition hck5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hck5_flat_seq HK.f_main fn_body] in
        (match fn_body HK.f_main with Ssequence s _ => hck5_flat_seq s | s => [s] end) in exact x).

Definition hck5_l (i n: nat) : list statement := firstn n (skipn i hck5_stmts).

Lemma hck5_stmts_length : length hck5_stmts = 95%nat.
Proof. reflexivity. Qed.

(* the phases:
   P1  =  0..19  corrupted = 0, boot clock, wg_noise_init, raw keys, setup_device x2, (v2) CHECK(B's secret = the
                 shim's last draw, born now), m_identity_of, the checker-key CHECKs, CHECK(device == &wb), B's
                 secret and its birthdate, honest_peer, pub, setup_peer, the peer-key CHECKs  (= v1 P1 + the CHECK)
   P1b = 20..27  (v2) hs_randomize(&p.handshake), p.is_dead, p.last_sent_handshake, p.refcount, maybe insert p's
                 entry into ita, kes = kents_add(&ita, NULL, &p, 1), kents_snap(kes), head0 = ita.head
   P2  = 28..33  len = draw_size (too big: return), len += 32, the two mallocs (NULL: frees, return)  (= v1 P2)
   P3  = 34..43  the message bytes, skb (data, len, protocol, addresses, port), now (and its edges),
                 wg_shim_boottime_ns = now  (= v1 P3)
   P4  = 44..51  p's cookie state, cookie_mode (B's secret's rotation, B's cookie)  (= v1 P4)
   P5a = 52..58  ck_take(&cs, ..), (v2) hs_take(&hs0, ..), pr_take(&ps0, &p), refs0, dev_take(&da, &wa),
                 dev_take(&db, &wb), shim_take(&ss)
   P5  = 59..67  copy, add_mac, the harness's model of it, the three CHECKs  (= v1 P5 without ck_take)
   P5c = 68      (v2) CHECK(hs_same && pr_same_but_cookie && refs && dev_same x2 && shim_same && head0 && kents_same)
   P6  = 69..74  the corruption, copy, check_cookie, the rate limiter, secret_birth, secret  (= v1 P6 without validate)
   P6b = 75..80  (v2) hs_take, pr_take, dev_take x2, skb_take, shim_take
   P6c = 81      r = validate  (= v1 P6's last statement)
   P7  = 82..86  the harness's verdict (rotation from wg_shim_random_log) and the three CHECKs  (= v1 P7)
   P7b = 87..89  (v2) db.secret = secret, db.secret_birthdate = secret_birth, CHECK(dev_same x2 && skb_same &&
                 hs_same && pr_same && refs && shim_same && head0 && kents_same)
   P8  = 90..94  the round trips, free(msg), free(copy), (v2) kents_free(kes), return 0 *)

Definition hck5_P1 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 0 20)) in exact x).

Definition hck5_P1b := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 20 8)) in exact x).

Definition hck5_P2 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 28 6)) in exact x).

Definition hck5_P3 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 34 10)) in exact x).

Definition hck5_P4 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 44 8)) in exact x).

Definition hck5_P5a := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 52 7)) in exact x).

Definition hck5_P5 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 59 9)) in exact x).

Definition hck5_P5c := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 68 1)) in exact x).

Definition hck5_P6 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 69 6)) in exact x).

Definition hck5_P6b := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 75 6)) in exact x).

Definition hck5_P6c := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 81 1)) in exact x).

Definition hck5_P7 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 82 5)) in exact x).

Definition hck5_P7b := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 87 3)) in exact x).

Definition hck5_P8 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in (hck5_seql (hck5_l 90 5)) in exact x).

Lemma hck5_body_eq :
  fn_body HK.f_main =
  Ssequence
    (hck5_seqs (hck5_l 0 20) (hck5_seqs (hck5_l 20 8) (hck5_seqs (hck5_l 28 6) (hck5_seqs (hck5_l 34 10) (hck5_seqs (hck5_l 44 8) (hck5_seqs (hck5_l 52 7) (hck5_seqs (hck5_l 59 9) (hck5_seqs (hck5_l 68 1) (hck5_seqs (hck5_l 69 6) (hck5_seqs (hck5_l 75 6) (hck5_seqs (hck5_l 81 1) (hck5_seqs (hck5_l 82 5) (hck5_seqs (hck5_l 87 3) (hck5_seql (hck5_l 90 5)))))))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hck5_phases_eq :
  hck5_P1 = hck5_seql (hck5_l 0 20) /\ hck5_P1b = hck5_seql (hck5_l 20 8) /\ hck5_P2 = hck5_seql (hck5_l 28 6) /\ hck5_P3 = hck5_seql (hck5_l 34 10) /\ hck5_P4 = hck5_seql (hck5_l 44 8) /\ hck5_P5a = hck5_seql (hck5_l 52 7) /\ hck5_P5 = hck5_seql (hck5_l 59 9) /\ hck5_P5c = hck5_seql (hck5_l 68 1) /\ hck5_P6 = hck5_seql (hck5_l 69 6) /\ hck5_P6b = hck5_seql (hck5_l 75 6) /\ hck5_P6c = hck5_seql (hck5_l 81 1) /\ hck5_P7 = hck5_seql (hck5_l 82 5) /\ hck5_P7b = hck5_seql (hck5_l 87 3) /\ hck5_P8 = hck5_seql (hck5_l 90 5).
Proof. repeat split. Qed.
