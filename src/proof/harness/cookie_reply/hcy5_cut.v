(* law cookie_reply: main's body cut into
   phases. *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_cookie_reply.code.

Module HY := WgNoise.harness.x_cookie_reply.code.

Fixpoint hcy5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hcy5_seqs l' rest) end.

Fixpoint hcy5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hcy5_seql l') end.

Fixpoint hcy5_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hcy5_flat_seq b | _ => [s] end.

Lemma hcy5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hcy5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hcy5_unfold_seqs l rest :
  unfold_Ssequence (hcy5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hcy5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hcy5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hcy5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hcy5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hcy5_seql l) rest)).
  - simpl. rewrite hcy5_unfold_seql, hcy5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the statements below (the last one is `return 0`) *)
Definition hcy5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hcy5_flat_seq HY.f_main fn_body] in
        (match fn_body HY.f_main with Ssequence s _ => hcy5_flat_seq s | s => [s] end) in exact x).

Lemma hcy5_stmts_length : length hcy5_stmts = 83%nat.
Proof. reflexivity. Qed.

Definition hcy5_l (i n: nat) : list statement := firstn n (skipn i hcy5_stmts).

(* the phases:
   P1  =  0..10  peers / cns = NULL, boot clock, wg_noise_init, raw keys, setup_device x2, m_identity_of,
                 B's cookie secret and its birthdate
   P2  = 11..17  len = draw_size (too big: return), len += 32, msg / copy / reply = malloc (NULL: frees, return)
   P3  = 18..29  the message bytes, copy, skb fields, now (and its edges), wg_shim_boottime_ns = now, index
   P4  = 30..35  fill_cookie_msg(reply), secret_birth, secret, dev_take(&db, &wb), skb_take(&sks, &skb),
                 wg_cookie_message_create
   P5  = 36..44  the rotation CHECKs, the checker CHECK, m_cookie, k, the key / header CHECKs, the model's
                 encryption, the reply CHECK, the message CHECK
   P5b = 45..47  db.secret = secret, db.secret_birthdate = secret_birth, CHECK(dev_same(&db, &wb) && skb_same)
   P6  = 48..50  np = hnodes_add(B's public key), n = draw_steps, the loop of hnodes_add
   P7  = 51      the loop over the peers: peer_randomize_rest, maybe insert the handshake entry, a cnode
                 (NULL: return)
   P8  = 52      kes = kents_add(&ita, peers, NULL, 1)
   P9  = 53..56  mode, honest, the mode block, cookie_img(img)
   P10 = 57..65  hnodes_snap, the ck_take loop, kents_snap, dev_take(&da, &wa), head0, now, the boot clock,
                 shim_take(&ss), wg_cookie_message_consume
   P11 = 66..69  the harness's model: target, the walk of ita, the cnode search, the decryption CHECK
   P12 = 70..75  the CHECKs: ck_same loop, the target / others CHECKs, dev_same / head0 / kents_same /
                 shim_same, cookie_img(img2), the image, the round trip
   P13 = 76..82  the frees (cnodes, kents_free, hnodes_free, msg, copy, reply), return 0 *)

Definition hcy5_P1 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 0 11)) in exact x).

Definition hcy5_P2 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 11 7)) in exact x).

Definition hcy5_P3 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 18 12)) in exact x).

Definition hcy5_P4 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 30 6)) in exact x).

Definition hcy5_P5 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 36 9)) in exact x).

Definition hcy5_P5b := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 45 3)) in exact x).

Definition hcy5_P6 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 48 3)) in exact x).

Definition hcy5_P7 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 51 1)) in exact x).

Definition hcy5_P8 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 52 1)) in exact x).

Definition hcy5_P9 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 53 4)) in exact x).

Definition hcy5_P10 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 57 9)) in exact x).

Definition hcy5_P11 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 66 4)) in exact x).

Definition hcy5_P12 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 70 6)) in exact x).

Definition hcy5_P13 := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 76 7)) in exact x).

Lemma hcy5_body_eq :
  fn_body HY.f_main =
  Ssequence
    (hcy5_seqs (hcy5_l 0 11) (hcy5_seqs (hcy5_l 11 7) (hcy5_seqs (hcy5_l 18 12) (hcy5_seqs (hcy5_l 30 6) (hcy5_seqs (hcy5_l 36 9) (hcy5_seqs (hcy5_l 45 3) (hcy5_seqs (hcy5_l 48 3) (hcy5_seqs (hcy5_l 51 1) (hcy5_seqs (hcy5_l 52 1) (hcy5_seqs (hcy5_l 53 4) (hcy5_seqs (hcy5_l 57 9) (hcy5_seqs (hcy5_l 66 4) (hcy5_seqs (hcy5_l 70 6) (hcy5_seql (hcy5_l 76 7)))))))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hcy5_phases_eq :
  hcy5_P1 = hcy5_seql (hcy5_l 0 11) /\ hcy5_P2 = hcy5_seql (hcy5_l 11 7) /\ hcy5_P3 = hcy5_seql (hcy5_l 18 12) /\ hcy5_P4 = hcy5_seql (hcy5_l 30 6) /\ hcy5_P5 = hcy5_seql (hcy5_l 36 9) /\ hcy5_P5b = hcy5_seql (hcy5_l 45 3) /\ hcy5_P6 = hcy5_seql (hcy5_l 48 3) /\ hcy5_P7 = hcy5_seql (hcy5_l 51 1) /\ hcy5_P8 = hcy5_seql (hcy5_l 52 1) /\ hcy5_P9 = hcy5_seql (hcy5_l 53 4) /\ hcy5_P10 = hcy5_seql (hcy5_l 57 9) /\ hcy5_P11 = hcy5_seql (hcy5_l 66 4) /\ hcy5_P12 = hcy5_seql (hcy5_l 70 6) /\ hcy5_P13 = hcy5_seql (hcy5_l 76 7).
Proof. repeat split. Qed.
