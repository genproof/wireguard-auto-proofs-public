(* law config_any: the cut of main's body into phases. main's body = S; return 0 (implicit) with S = the 96 statements of hcf5_stmts (the last one the explicit
   `return 0`):
     PA1 =  0..5   boot clock, raw0, setup_device(&w, &it, &pt, raw0), pub, setup_peer(&p, &w, pub, NULL, 1)
     PA2 =  6..16  ANY prior contents: identity bytes and flag, checker keys, p's precomputed DH and cookie keys,
                   hs_randomize(&p.handshake), peer_randomize_rest(&p), maybe wg_index_hashtable_insert(p's entry)
     PK  = 17      kes = kents_add(&it, NULL, &p, 1)
     PS  = 18..24  kents_snap, head0 = it.head, dev_take, hs_take, pr_take, refs0, shim_take
     P1  = 25..30  step 1: raw, m_identity_of, wg_noise_set_static_identity_private_key, ds edits;  C1 = 31 CHECK
     P2  = 32..34  step 2: wg_noise_precompute_static_static, m_precomputed, hs0 edit;            C2 = 35 CHECK
     P3  = 36..37  step 3: wg_cookie_checker_precompute_device_keys, ds edits;                     C3 = 38 CHECK
     P4  = 39..41  step 4: wg_cookie_checker_precompute_peer_keys, ps0 edits;                      C4 = 42 CHECK
     P5a = 43..56  step 5: q's handshake ANY (fields, hs_randomize), qpub, psk, use_psk, wg_noise_handshake_init
     P5b = 57..74  hq = the initial handshake, CHECK(hs_same(&hq, &q.handshake))
     P5c = 75..84  q's cookie ANY, wg_cookie_init, CHECK(zero), CHECK(hs_same(&hq, ..));          C5 = 85 CHECK
     P6  = 86..92  step 6: checker secret/birthdate/device ANY, wg_cookie_checker_init, ds edits;  C6 = 93 CHECK
     PE  = 94..95  kents_free(kes), return 0
   C1..C6 = the frame CHECK(dev_same && hs_same && pr_same && refs && shim_same && kents_same && head0). *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_config_any.code.

Module HF5 := WgNoise.harness.x_config_any.code.

Fixpoint hcf5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hcf5_seqs l' rest) end.

Fixpoint hcf5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hcf5_seql l') end.

Fixpoint hcf5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hcf5_flat b | _ => [s] end.

Lemma hcf5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hcf5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hcf5_unfold_seqs l rest :
  unfold_Ssequence (hcf5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hcf5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hcf5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hcf5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hcf5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hcf5_seql l) rest)).
  - simpl. rewrite hcf5_unfold_seql, hcf5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* a list cut into two consecutive non-empty pieces *)
Lemma hcf5_seql_app {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hcf5_seql l1) (overridePost Q R) -> semax Delta Q (hcf5_seql l2) R ->
  semax Delta P (hcf5_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  assert (H12: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  apply (semax_unfold_Ssequence (Ssequence (hcf5_seql l1) (hcf5_seql l2))).
  - simpl. rewrite (hcf5_unfold_seql _ H12), (hcf5_unfold_seql _ H1), (hcf5_unfold_seql _ H2), map_app, concat_app.
    reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's statements *)
Definition hcf5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hcf5_flat HF5.f_main fn_body] in
        (match fn_body HF5.f_main with Ssequence s _ => hcf5_flat s | s => [s] end) in exact x).

Definition hcf5_l (i n: nat) : list statement := firstn n (skipn i hcf5_stmts).

Lemma hcf5_stmts_length : length hcf5_stmts = 96%nat.
Proof. reflexivity. Qed.

Definition hcf5_PA1 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 0 6)) in exact x).
Definition hcf5_PA2 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 6 11)) in exact x).
Definition hcf5_PK := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 17 1)) in exact x).
Definition hcf5_PS := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 18 7)) in exact x).
Definition hcf5_P1 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 25 6)) in exact x).
Definition hcf5_C1 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 31 1)) in exact x).
Definition hcf5_P2 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 32 3)) in exact x).
Definition hcf5_C2 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 35 1)) in exact x).
Definition hcf5_P3 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 36 2)) in exact x).
Definition hcf5_C3 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 38 1)) in exact x).
Definition hcf5_P4 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 39 3)) in exact x).
Definition hcf5_C4 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 42 1)) in exact x).
Definition hcf5_P5a := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 43 14)) in exact x).
Definition hcf5_P5b := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 57 18)) in exact x).
Definition hcf5_P5c := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 75 10)) in exact x).
Definition hcf5_C5 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 85 1)) in exact x).
Definition hcf5_P6 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 86 7)) in exact x).
Definition hcf5_C6 := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 93 1)) in exact x).
Definition hcf5_PE := ltac:(let x := eval cbv beta iota delta [hcf5_l hcf5_seql firstn skipn hcf5_stmts] in (hcf5_seql (hcf5_l 94 2)) in exact x).

Lemma hcf5_body_eq :
  fn_body HF5.f_main =
  Ssequence
    (hcf5_seqs (hcf5_l 0 6) (hcf5_seqs (hcf5_l 6 11) (hcf5_seqs (hcf5_l 17 1) (hcf5_seqs (hcf5_l 18 7) (hcf5_seqs (hcf5_l 25 6) (hcf5_seqs (hcf5_l 31 1) (hcf5_seqs (hcf5_l 32 3) (hcf5_seqs (hcf5_l 35 1) (hcf5_seqs (hcf5_l 36 2) (hcf5_seqs (hcf5_l 38 1) (hcf5_seqs (hcf5_l 39 3) (hcf5_seqs (hcf5_l 42 1) (hcf5_seqs (hcf5_l 43 14) (hcf5_seqs (hcf5_l 57 18) (hcf5_seqs (hcf5_l 75 10) (hcf5_seqs (hcf5_l 85 1) (hcf5_seqs (hcf5_l 86 7) (hcf5_seqs (hcf5_l 93 1) (hcf5_seql (hcf5_l 94 2))))))))))))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hcf5_phases_eq :
  hcf5_PA1 = hcf5_seql (hcf5_l 0 6) /\
  hcf5_PA2 = hcf5_seql (hcf5_l 6 11) /\
  hcf5_PK = hcf5_seql (hcf5_l 17 1) /\
  hcf5_PS = hcf5_seql (hcf5_l 18 7) /\
  hcf5_P1 = hcf5_seql (hcf5_l 25 6) /\
  hcf5_C1 = hcf5_seql (hcf5_l 31 1) /\
  hcf5_P2 = hcf5_seql (hcf5_l 32 3) /\
  hcf5_C2 = hcf5_seql (hcf5_l 35 1) /\
  hcf5_P3 = hcf5_seql (hcf5_l 36 2) /\
  hcf5_C3 = hcf5_seql (hcf5_l 38 1) /\
  hcf5_P4 = hcf5_seql (hcf5_l 39 3) /\
  hcf5_C4 = hcf5_seql (hcf5_l 42 1) /\
  hcf5_P5a = hcf5_seql (hcf5_l 43 14) /\
  hcf5_P5b = hcf5_seql (hcf5_l 57 18) /\
  hcf5_P5c = hcf5_seql (hcf5_l 75 10) /\
  hcf5_C5 = hcf5_seql (hcf5_l 85 1) /\
  hcf5_P6 = hcf5_seql (hcf5_l 86 7) /\
  hcf5_C6 = hcf5_seql (hcf5_l 93 1) /\
  hcf5_PE = hcf5_seql (hcf5_l 94 2).
Proof. repeat split. Qed.
