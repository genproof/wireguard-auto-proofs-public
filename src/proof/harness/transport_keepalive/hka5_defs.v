(* main of
   harness/transport_keepalive.c: the initial globals, the statements of the body cut into segments, the loop
   invariant and the states between the segments. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Export WgNoise.proof.harness.transport_keepalive.hka5_spec.
Require WgNoise.contracts.x_transport_keepalive.
Require WgNoise.harness.x_transport_keepalive.code.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The initial globals: keep zero_page and minusp                          *)
(* ---------------------------------------------------------------------- *)

Lemma hka5_InitGPred_filter (f: ident * globdef (fundef function) type -> bool) al gv :
  InitGPred al gv |-- (InitGPred (filter f al) gv * TT)%logic.
Proof.
  induction al as [|a al IH]; simpl.
  - unfold InitGPred; simpl. cancel.
  - unfold InitGPred in *; simpl. destruct (f a); simpl.
    + rewrite sepcon_assoc. apply sepcon_derives; auto.
    + eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply IH] |].
      rewrite (sepcon_comm (fold_right _ _ _)), <- sepcon_assoc, TT_sepcon_TT. cancel.
Qed.

Definition hka5_keep (x: ident * globdef (fundef function) type) : bool :=
  Pos.eqb (fst x) hka5_mp || Pos.eqb (fst x) _quickproof_zero_page.

Definition hka5_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter hka5_keep (Vardefs WgNoise.contracts.x_transport_keepalive.whole_prog)) in exact x).

Lemma hka5_vardefs_eq :
  filter hka5_keep (Vardefs WgNoise.contracts.x_transport_keepalive.whole_prog) = hka5_vardefs.
Proof. vm_compute. reflexivity. Qed.

Lemma hka5_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_transport_keepalive.whole_prog) gv |--
    (zero_page gv * ht4_minusp hka5_mp gv * TT)%logic.
Proof.
  intros Hgv. eapply derives_trans; [apply (hka5_InitGPred_filter hka5_keep) |].
  rewrite hka5_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred hka5_vardefs gv |-- (fun g => zero_page g * ht4_minusp hka5_mp g)%logic gv).
  eapply InitGPred_process_globvars; auto.
  let Delta := fresh "Delta" in let Delta' := fresh "Delta'" in
  set (Delta' := vardefs_tycontext _);
  set (Delta := @abbreviate tycontext Delta');
  change Delta' with Delta;
  hnf in Delta'; simpl in Delta'; subst Delta'.
  simpl vardefs_to_globvars.
  eapply derives_trans; [process_globals | ].
  clear Delta. apply finish_process_globvars'. unfold fold_right_sepcon at 1.
  simpl readonly2share. rewrite sepcon_emp.
  match goal with |- data_at ?sh (tarray tuint 17) ?l ?p * _ |-- _ =>
    replace l with (map Vint hrp_minusp) by
      (vm_compute; repeat match goal with |- cons _ _ = cons _ _ => f_equal
                                     | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity end) end.
  rewrite sepcon_comm.
  unfold zero_page, ht4_minusp. apply sepcon_derives; [| apply derives_refl].
  rewrite zero_val_tarray. replace (zero_val tuchar) with (Vubyte Byte.zero) by (rewrite zero_val_eq; reflexivity).
  match goal with |- data_at _ _ _ (gv ?i) |-- data_at _ _ _ (gv ?j) =>
    replace i with j by reflexivity end.
  apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* The states of main                                                      *)
(* ---------------------------------------------------------------------- *)

Definition hka5_Delta : tycontext := func_tycontext KA.f_main hka5_V hka5_Gprog [].

(* the addresses of main's locals and the globals *)
Definition hka5_lv (gv: globals) (vrc vwm vsnap vkey: val) : list localdef :=
  [lvar KA._rc ht4k_trc vrc; lvar KA._wm ht4k_twm vwm; lvar KA._snap ht4k_tsnap vsnap;
   lvar KA._key (tarray tuchar 32) vkey; gvars gv].

(* the resources every state carries: the key, the allocator, the globals, the rest (FR) *)
Definition hka5_fr (gv: globals) (vkey: val) (key: list byte) (FR: mpred) : list mpred :=
  [data_at Tsh (tarray tuchar 32) (map Vubyte key) vkey; mem_mgr gv; zero_page gv; ht4_minusp hka5_mp gv; FR].

(* the loop's temps *)
Definition hka5_tl (i steps ha ln: Z) : list localdef :=
  [temp KA._i (Vlong (Int64.repr i)); temp KA._steps (Vlong (Int64.repr steps));
   temp KA._have_auth (Vint (Int.repr ha)); temp KA._last_nonce (Vlong (Int64.repr ln))].

(* the replay counter (top, bm) and the shadow model (top, S) *)
Definition hka5_cw (vrc vwm: val) (top: Z) (S bm: list Z) : list mpred :=
  [data_at Tsh ht4k_trc (ht4k_rc top bm) vrc; ht4k_wm Tsh top S vwm].

(* the facts of the loop state *)
Definition hka5_facts (i steps: Z) (key: list byte) (top: Z) (S bm: list Z) (ha ln: Z) : Prop :=
  0 <= i <= steps /\ steps <= Int64.max_unsigned /\ Zlength key = 32 /\ cnt_inv top S bm /\
  Int.min_signed <= ha <= Int.max_signed /\ 0 <= ln <= Int64.max_unsigned.

(* the loop invariant (also the state after the increment) *)
Definition hka5_Inv (gv: globals) (vrc vwm vsnap vkey: val) (key: list byte) (steps: Z) (FR: mpred)
  : environ -> mpred :=
  EX i: Z, EX top: Z, EX S: list Z, EX bm: list Z, EX ha: Z, EX ln: Z,
  PROPx [hka5_facts i steps key top S bm ha ln]
  (LOCALx (hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (hka5_cw vrc vwm top S bm ++ data_at_ Tsh ht4k_tsnap vsnap :: hka5_fr gv vkey key FR))).

(* the state before the increment (the loop body's end): i < steps *)
Definition hka5_Cont (gv: globals) (vrc vwm vsnap vkey: val) (key: list byte) (steps: Z) (FR: mpred)
  : environ -> mpred :=
  EX i: Z, EX top: Z, EX S: list Z, EX bm: list Z, EX ha: Z, EX ln: Z,
  PROPx [hka5_facts i steps key top S bm ha ln; i < steps]
  (LOCALx (hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (hka5_cw vrc vwm top S bm ++ data_at_ Tsh ht4k_tsnap vsnap :: hka5_fr gv vkey key FR))).

(* after the loop (normal exit or a break): the counter anything, the model consistent *)
Definition hka5_Brk (gv: globals) (vrc vwm vsnap vkey: val) (key: list byte) (FR: mpred) : environ -> mpred :=
  EX top: Z, EX S: list Z,
  PROPx []
  (LOCALx (hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (data_at_ Tsh ht4k_trc vrc :: ht4k_wm Tsh top S vwm :: data_at_ Tsh ht4k_tsnap vsnap ::
         hka5_fr gv vkey key FR))).

(* a malloc(0) result: NULL, or a token and an empty block *)
Definition hka5_mb (p: val) : mpred :=
  if eq_dec p nullval then emp
  else (malloc_token Ews (tarray tuchar 0) p * data_at_ Ews (tarray tuchar 0) p)%logic.

(* the kind of a packet and the length of its encrypted_data *)
Definition hka5_kind_ok (kind enc: Z) : Prop :=
  0 <= kind <= 3 /\ (kind = 3 -> 0 <= enc < 16) /\ (kind <> 3 -> enc = 16).

(* the packet's temps after segment A *)
Definition hka5_tA (kind enc: Z) (pkt po rp: val) : list localdef :=
  [temp KA._kind (Vint (Int.repr kind)); temp KA._enc_len (Vlong (Int64.repr enc));
   temp KA._tot (Vlong (Int64.repr (16 + enc))); temp KA._pt_len (Vlong (Int64.repr 0));
   temp KA._pkt pkt; temp KA._pt_out po; temp KA._ref_pt rp].

(* the packet's temps after segment B *)
Definition hka5_tB (nonce enc: Z) (pkt po rp: val) : list localdef :=
  [temp KA._nonce (Vlong (Int64.repr nonce)); temp KA._enc_len (Vlong (Int64.repr enc));
   temp KA._pt_len (Vlong (Int64.repr 0)); temp KA._pkt pkt; temp KA._pt_out po; temp KA._ref_pt rp].

(* the packet's buffer after segment B: the header (any bytes) and encrypted_data = c *)
Definition hka5_pkt (pkt: val) (hdr: list val) (c: list byte) : list mpred :=
  [malloc_token Ews (tarray tuchar (16 + Zlength c)) pkt; data_at Ews (tarray tuchar 16) hdr pkt;
   data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) (offset_val 16 pkt)].

(* the AEAD verdict on encrypted_data c (no associated data) *)
Definition hka5_ok (key: list byte) (nonce: Z) (c: list byte) : bool :=
  match aead_dec key nonce [] c with Some _ => true | None => false end.

(* ---------------------------------------------------------------------- *)
(* Cutting the loop body into segments                                     *)
(* ---------------------------------------------------------------------- *)

Fixpoint hka5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hka5_seqs l' rest) end.

Fixpoint hka5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hka5_seql l') end.

Fixpoint hka5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hka5_flat b | _ => [s] end.

Lemma hka5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hka5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hka5_unfold_seqs l rest :
  unfold_Ssequence (hka5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hka5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hka5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hka5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hka5_seql l) rest)).
  - simpl. rewrite hka5_unfold_seql, hka5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body, the 9 top-level statements: last_nonce = 0; have_auth = 0; rc_init; wm_init; nondet_bytes(key);
   steps = draw_steps(); (i = 0; the loop); wm_free; return 0 *)
Definition hka5_top : list statement :=
  ltac:(let x := eval cbv beta iota delta [hka5_flat KA.f_main fn_body] in
        (match fn_body KA.f_main with Ssequence s _ => hka5_flat s | s => [s] end) in exact x).

(* the loop: Sloop (Ssequence (if (!(i < steps)) break) BODY) (i = i + 1) *)
Definition hka5_body : statement :=
  ltac:(let x := eval cbv beta iota delta [hka5_top nth] in (nth 6 hka5_top Sskip) in
        match x with Ssequence _ (Sloop (Ssequence _ ?b) _) => exact b end).

(* BODY's 21 statements *)
Definition hka5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hka5_flat hka5_body] in (hka5_flat hka5_body) in exact x).

Lemma hka5_stmts_length : length hka5_stmts = 21%nat.
Proof. reflexivity. Qed.

Definition hka5_l (i n: nat) : list statement := firstn n (skipn i hka5_stmts).

(* the segments:
   A = 0..7   kind, enc_len, tot, pt_len; the three mallocs; the NULL test (frees + break)
   B = 8..12  nonce; the header (le32_store x2, le64_store); encrypted_data: the AEAD of the empty plaintext
              (kinds 0-2, one byte corrupted for kind 1) or enc_len (< 16) random bytes (kind 3)
   C = 13..16 rc_take; ok = chacha20poly1305_decrypt; ref_ok = ref_aead_decrypt; CHECK(ok == ref_ok)
   D = 17     !ok: CHECK(rc_same); ok: wm_accepts, wg_counter_validate, CHECK(r == pred),
              r: CHECK(pt_len == 0), wm_commit (failure: frees + break); CHECK(rc.counter == wm.top);
              have_auth = 1; last_nonce = nonce
   E = 18..20 the three frees *)
Definition hka5_segA := ltac:(let x := eval cbv beta iota delta [hka5_l hka5_seql firstn skipn hka5_stmts] in
  (hka5_seql (hka5_l 0 8)) in exact x).
Definition hka5_segB := ltac:(let x := eval cbv beta iota delta [hka5_l hka5_seql firstn skipn hka5_stmts] in
  (hka5_seql (hka5_l 8 5)) in exact x).
Definition hka5_segC := ltac:(let x := eval cbv beta iota delta [hka5_l hka5_seql firstn skipn hka5_stmts] in
  (hka5_seql (hka5_l 13 4)) in exact x).
Definition hka5_segD := ltac:(let x := eval cbv beta iota delta [hka5_l hka5_seql firstn skipn hka5_stmts] in
  (hka5_seql (hka5_l 17 1)) in exact x).
Definition hka5_segE := ltac:(let x := eval cbv beta iota delta [hka5_l hka5_seql firstn skipn hka5_stmts] in
  (hka5_seql (hka5_l 18 3)) in exact x).

Lemma hka5_body_eq :
  hka5_body = hka5_seqs (hka5_l 0 8) (hka5_seqs (hka5_l 8 5) (hka5_seqs (hka5_l 13 4)
                (hka5_seqs (hka5_l 17 1) (hka5_seql (hka5_l 18 3))))).
Proof. reflexivity. Qed.

Lemma hka5_segs_eq :
  hka5_segA = hka5_seql (hka5_l 0 8) /\ hka5_segB = hka5_seql (hka5_l 8 5) /\
  hka5_segC = hka5_seql (hka5_l 13 4) /\ hka5_segD = hka5_seql (hka5_l 17 1) /\
  hka5_segE = hka5_seql (hka5_l 18 3).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The states between the segments of the loop body                        *)
(* ---------------------------------------------------------------------- *)

(* main's return, framed by its stack *)
Definition hka5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hka5_post gv)) (stackframe_of KA.f_main).

(* the loop body's ret_assert: normal end -> hka5_Cont, break -> hka5_Brk *)
Definition hka5_LR (gv: globals) (vrc vwm vsnap vkey: val) (key: list byte) (steps: Z) (FR: mpred) : ret_assert :=
  loop1_ret_assert (hka5_Cont gv vrc vwm vsnap vkey key steps FR)
    (overridePost (hka5_Brk gv vrc vwm vsnap vkey key FR) (hka5_R gv)).

Section States.
Variables (gv: globals) (vrc vwm vsnap vkey: val) (key: list byte) (steps: Z) (FR: mpred).

(* before A: the loop state, i < steps *)
Definition hka5_PA (i top: Z) (S bm: list Z) (ha ln: Z) : environ -> mpred :=
  PROPx [hka5_facts i steps key top S bm ha ln; i < steps]
  (LOCALx (hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (hka5_cw vrc vwm top S bm ++ data_at_ Tsh ht4k_tsnap vsnap :: hka5_fr gv vkey key FR))).

(* before B: kind, enc_len drawn; pkt (16 + enc_len bytes, non-NULL), pt_out, ref_pt (malloc(0)) allocated *)
Definition hka5_PB (i top: Z) (S bm: list Z) (ha ln: Z) (kind enc: Z) (pkt po rp: val) : environ -> mpred :=
  PROPx [hka5_facts i steps key top S bm ha ln; i < steps; hka5_kind_ok kind enc; isptr pkt]
  (LOCALx (hka5_tA kind enc pkt po rp ++ hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (malloc_token Ews (tarray tuchar (16 + enc)) pkt :: data_at_ Ews (tarray tuchar (16 + enc)) pkt ::
         hka5_mb po :: hka5_mb rp ::
         hka5_cw vrc vwm top S bm ++ data_at_ Tsh ht4k_tsnap vsnap :: hka5_fr gv vkey key FR))).

Definition hka5_QA (i top: Z) (S bm: list Z) (ha ln: Z) : environ -> mpred :=
  EX kind: Z, EX enc: Z, EX pkt: val, EX po: val, EX rp: val, hka5_PB i top S bm ha ln kind enc pkt po rp.

(* before C: nonce, the header (any 16 values) and encrypted_data c (Zlength c = enc_len <= 16) *)
Definition hka5_PC (i top: Z) (S bm: list Z) (ha ln: Z) (nonce: Z) (hdr: list val) (c: list byte) (pkt po rp: val)
  : environ -> mpred :=
  PROPx [hka5_facts i steps key top S bm ha ln; i < steps; Zlength c <= 16; 0 <= nonce <= Int64.max_unsigned;
         Zlength hdr = 16]
  (LOCALx (hka5_tB nonce (Zlength c) pkt po rp ++ hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (hka5_pkt pkt hdr c ++ hka5_mb po :: hka5_mb rp ::
         hka5_cw vrc vwm top S bm ++ data_at_ Tsh ht4k_tsnap vsnap :: hka5_fr gv vkey key FR))).

Definition hka5_QB (i top: Z) (S bm: list Z) (ha ln: Z) (pkt po rp: val) : environ -> mpred :=
  EX nonce: Z, EX hdr: list val, EX c: list byte, hka5_PC i top S bm ha ln nonce hdr c pkt po rp.

(* before D: ok (any int: D does not depend on it), the snapshot of the counter taken *)
Definition hka5_PD (i top: Z) (S bm: list Z) (ha ln: Z) (nonce: Z) (hdr: list val) (c: list byte) (pkt po rp: val)
  (okv: int) : environ -> mpred :=
  PROPx [hka5_facts i steps key top S bm ha ln; i < steps; Zlength c <= 16; 0 <= nonce <= Int64.max_unsigned;
         Zlength hdr = 16]
  (LOCALx (temp KA._ok (Vint okv) ::
           hka5_tB nonce (Zlength c) pkt po rp ++ hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (hka5_pkt pkt hdr c ++ hka5_mb po :: hka5_mb rp ::
         hka5_cw vrc vwm top S bm ++ data_at Tsh ht4k_tsnap (ht4k_snap top bm) vsnap :: hka5_fr gv vkey key FR))).

(* after C: ok = the AEAD verdict (the CHECK ok == ref_ok passed) *)
Definition hka5_QC (i top: Z) (S bm: list Z) (ha ln: Z) (nonce: Z) (hdr: list val) (c: list byte) (pkt po rp: val)
  : environ -> mpred :=
  hka5_PD i top S bm ha ln nonce hdr c pkt po rp (if hka5_ok key nonce c then Int.one else Int.zero).

(* before E: the new counter / model state (same i), the packet still allocated *)
Definition hka5_PE (i top: Z) (S bm: list Z) (ha ln: Z) (hdr: list val) (c: list byte) (pkt po rp: val)
  : environ -> mpred :=
  PROPx [hka5_facts i steps key top S bm ha ln; i < steps; Zlength c <= 16; Zlength hdr = 16]
  (LOCALx (temp KA._pkt pkt :: temp KA._pt_out po :: temp KA._ref_pt rp ::
           hka5_tl i steps ha ln ++ hka5_lv gv vrc vwm vsnap vkey)
  (SEPx (hka5_pkt pkt hdr c ++ hka5_mb po :: hka5_mb rp ::
         hka5_cw vrc vwm top S bm ++ data_at_ Tsh ht4k_tsnap vsnap :: hka5_fr gv vkey key FR))).

Definition hka5_QD (i: Z) (hdr: list val) (c: list byte) (pkt po rp: val) : environ -> mpred :=
  EX top: Z, EX S: list Z, EX bm: list Z, EX ha: Z, EX ln: Z, hka5_PE i top S bm ha ln hdr c pkt po rp.

End States.
