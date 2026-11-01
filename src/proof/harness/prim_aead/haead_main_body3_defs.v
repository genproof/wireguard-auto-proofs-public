(* law prim_aead: main of prim_aead.h: the initial globals, the segments of the body and the states
   between them.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.contracts.x_prim_aead.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Module HAC := WgNoise.harness.x_prim_aead.code.

(* ---------------------------------------------------------------------- *)
(* The initial globals: keep zero_page and minusp                          *)
(* ---------------------------------------------------------------------- *)

Lemma hm3_InitGPred_filter (f: ident * globdef (fundef function) type -> bool) al gv :
  InitGPred al gv |-- (InitGPred (filter f al) gv * TT)%logic.
Proof.
  induction al as [|a al IH]; simpl.
  - unfold InitGPred; simpl. cancel.
  - unfold InitGPred in *; simpl. destruct (f a); simpl.
    + rewrite sepcon_assoc. apply sepcon_derives; auto.
    + eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply IH] |].
      rewrite (sepcon_comm (fold_right _ _ _)), <- sepcon_assoc, TT_sepcon_TT. cancel.
Qed.

Definition hm3_keep (x: ident * globdef (fundef function) type) : bool :=
  Pos.eqb (fst x) HA._minusp || Pos.eqb (fst x) _quickproof_zero_page.

Definition hm3_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter hm3_keep (Vardefs WgNoise.contracts.x_prim_aead.whole_prog)) in exact x).

Lemma hm3_vardefs_eq :
  filter hm3_keep (Vardefs WgNoise.contracts.x_prim_aead.whole_prog) = hm3_vardefs.
Proof. vm_compute. reflexivity. Qed.

Lemma hm3_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_prim_aead.whole_prog) gv |-- (zero_page gv * haead_globals gv * TT)%logic.
Proof.
  intros Hgv. eapply derives_trans; [apply (hm3_InitGPred_filter hm3_keep) |].
  rewrite hm3_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred hm3_vardefs gv |-- (fun g => zero_page g * haead_globals g)%logic gv).
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
  unfold zero_page, haead_globals. apply sepcon_derives; [| apply derives_refl].
  rewrite zero_val_tarray. replace (zero_val tuchar) with (Vubyte Byte.zero) by (rewrite zero_val_eq; reflexivity).
  match goal with |- data_at _ _ _ (gv ?i) |-- data_at _ _ _ (gv ?j) =>
    replace i with j by reflexivity end.
  apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* Cutting main's body into segments                                       *)
(* ---------------------------------------------------------------------- *)

Fixpoint hm3_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hm3_seqs l' rest) end.

Fixpoint hm3_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hm3_seql l') end.

Fixpoint hm3_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hm3_flat_seq b | _ => [s] end.

Lemma hm3_unfold_seql l : l <> [] ->
  unfold_Ssequence (hm3_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hm3_unfold_seqs l rest :
  unfold_Ssequence (hm3_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hm3_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hm3_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hm3_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hm3_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hm3_seql l) rest)).
  - simpl. rewrite hm3_unfold_seql, hm3_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 35 statements below *)
Definition hm3_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hm3_flat_seq HAC.f_main fn_body] in
        (match fn_body HAC.f_main with Ssequence s _ => hm3_flat_seq s | s => [s] end) in exact x).

Lemma hm3_stmts_length : length hm3_stmts = 35%nat.
Proof. reflexivity. Qed.

Definition hm3_sub (i n: nat) : statement := hm3_seql (firstn n (skipn i hm3_stmts)).
Definition hm3_l (i n: nat) : list statement := firstn n (skipn i hm3_stmts).

(* the segments:
   A = 0..8   x = nondet_u8() & 1, nondet key / xnonce, nonce, adlen, n (the PTRDIFF_MAX returns, LEN_LIMIT test)
   B = 9..16  the seven mallocs and the NULL test (frees + return)
   C = 17..20 nondet ad / pt and their copies
   D = 21..22 kernel + reference encryption, CHECK(bytes_eq(ct, rct, n + 16))
   E = 23..24 kernel decryption of ct, CHECK(ok && bytes_eq(dec, pt, n))
   F = 25..34 check_decrypt_any, CHECK(copies), the seven frees, return 0 *)
Definition hm3_segA := ltac:(let x := eval cbv beta iota delta [hm3_sub hm3_seql firstn skipn hm3_stmts] in (hm3_sub 0 9) in exact x).
Definition hm3_segB := ltac:(let x := eval cbv beta iota delta [hm3_sub hm3_seql firstn skipn hm3_stmts] in (hm3_sub 9 8) in exact x).
Definition hm3_segC := ltac:(let x := eval cbv beta iota delta [hm3_sub hm3_seql firstn skipn hm3_stmts] in (hm3_sub 17 4) in exact x).
Definition hm3_segD := ltac:(let x := eval cbv beta iota delta [hm3_sub hm3_seql firstn skipn hm3_stmts] in (hm3_sub 21 2) in exact x).
Definition hm3_segE := ltac:(let x := eval cbv beta iota delta [hm3_sub hm3_seql firstn skipn hm3_stmts] in (hm3_sub 23 2) in exact x).
Definition hm3_segF := ltac:(let x := eval cbv beta iota delta [hm3_sub hm3_seql firstn skipn hm3_stmts] in (hm3_sub 25 10) in exact x).

Lemma hm3_body_eq :
  fn_body HAC.f_main =
  Ssequence
    (hm3_seqs (hm3_l 0 9) (hm3_seqs (hm3_l 9 8) (hm3_seqs (hm3_l 17 4)
      (hm3_seqs (hm3_l 21 2) (hm3_seqs (hm3_l 23 2) (hm3_seql (hm3_l 25 10)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hm3_segs_eq :
  hm3_segA = hm3_seql (hm3_l 0 9) /\ hm3_segB = hm3_seql (hm3_l 9 8) /\
  hm3_segC = hm3_seql (hm3_l 17 4) /\ hm3_segD = hm3_seql (hm3_l 21 2) /\
  hm3_segE = hm3_seql (hm3_l 23 2) /\ hm3_segF = hm3_seql (hm3_l 25 10).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Definition hm3_Delta : tycontext := func_tycontext HAC.f_main haead_V haead_Gprog [].

Definition hm3_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (haead_post gv)) (stackframe_of HAC.f_main).

(* the kernel's / reference's encryption chosen by x (0: ChaCha20-Poly1305, else XChaCha20-Poly1305) *)
Definition hm3_enc (x: Z) (key: list byte) (nonce: Z) (xn a m: list byte) : list byte :=
  if Z.eq_dec x 0 then aead_enc key nonce a m else xaead_enc key xn a m.

(* the locals' addresses and the globals *)
Definition hm3_lv (gv: globals) (vk vxn: val) : list localdef :=
  [lvar HAC._key (tarray tuchar 32) vk; lvar HAC._xnonce (tarray tuchar 24) vxn; gvars gv].

(* the temps fixed by segment A *)
Definition hm3_tA (x nonce adlen n: Z) : list localdef :=
  [temp HAC._x (Vint (Int.repr x)); temp HAC._nonce (Vlong (Int64.repr nonce));
   temp HAC._adlen (Vlong (Int64.repr adlen)); temp HAC._n (Vlong (Int64.repr n))].

(* the temps fixed by segment B: the seven buffers *)
Definition hm3_tB (ad ad_copy pt pt_copy ct rct dec: val) : list localdef :=
  [temp HAC._ad ad; temp HAC._ad_copy ad_copy; temp HAC._pt pt; temp HAC._pt_copy pt_copy;
   temp HAC._ct ct; temp HAC._rct rct; temp HAC._dec dec].

(* the facts on the drawn values *)
Definition hm3_ranges (x: Z) (key: list byte) (nonce: Z) (xn: list byte) (adlen n: Z) : Prop :=
  0 <= x <= 1 /\ Zlength key = 32 /\ 0 <= nonce <= Int64.max_unsigned /\ Zlength xn = 24 /\
  0 <= adlen <= Int64.max_signed /\ 0 <= n <= Int64.max_signed - 16.

(* a malloc'd byte buffer of len bytes with contents v *)
Definition hm3_buf (len: Z) (v: list val) (p: val) : mpred :=
  (malloc_token Ews (tarray tuchar len) p * data_at Ews (tarray tuchar len) v p)%logic.

(* before segment A (after the prologue) *)
Definition hm3_P0 (gv: globals) (vk vxn: val) (FR: mpred) : environ -> mpred :=
  PROPx [] (LOCALx (hm3_lv gv vk vxn)
  (SEPx [data_at_ Tsh (tarray tuchar 32) vk; data_at_ Tsh (tarray tuchar 24) vxn;
         mem_mgr gv; zero_page gv; haead_globals gv; FR])).

(* after A: x, key, xnonce, nonce, adlen, n drawn (within the guards) *)
Definition hm3_PA (gv: globals) (vk vxn: val) (FR: mpred) : environ -> mpred :=
  EX x: Z, EX key: list byte, EX nonce: Z, EX xn: list byte, EX adlen: Z, EX n: Z,
  PROPx [hm3_ranges x key nonce xn adlen n]
  (LOCALx (hm3_tA x nonce adlen n ++ hm3_lv gv vk vxn)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         mem_mgr gv; zero_page gv; haead_globals gv; FR])).

(* after B: the seven buffers allocated (non-NULL), uninitialised *)
Definition hm3_PB (gv: globals) (vk vxn: val) (FR: mpred) : environ -> mpred :=
  EX x: Z, EX key: list byte, EX nonce: Z, EX xn: list byte, EX adlen: Z, EX n: Z,
  EX ad: val, EX ad_copy: val, EX pt: val, EX pt_copy: val, EX ct: val, EX rct: val, EX dec: val,
  PROPx [hm3_ranges x key nonce xn adlen n]
  (LOCALx (hm3_tB ad ad_copy pt pt_copy ct rct dec ++ hm3_tA x nonce adlen n ++ hm3_lv gv vk vxn)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         hm3_buf adlen (Zrepeat Vundef adlen) ad; hm3_buf adlen (Zrepeat Vundef adlen) ad_copy;
         hm3_buf n (Zrepeat Vundef n) pt; hm3_buf n (Zrepeat Vundef n) pt_copy;
         hm3_buf (n + 16) (Zrepeat Vundef (n + 16)) ct; hm3_buf (n + 16) (Zrepeat Vundef (n + 16)) rct;
         hm3_buf n (Zrepeat Vundef n) dec;
         mem_mgr gv; zero_page gv; haead_globals gv; FR])).

(* after C: a = the associated data, m = the message, both copied *)
Definition hm3_PC (gv: globals) (vk vxn: val) (FR: mpred) : environ -> mpred :=
  EX x: Z, EX key: list byte, EX nonce: Z, EX xn: list byte, EX a: list byte, EX m: list byte,
  EX ad: val, EX ad_copy: val, EX pt: val, EX pt_copy: val, EX ct: val, EX rct: val, EX dec: val,
  PROPx [hm3_ranges x key nonce xn (Zlength a) (Zlength m)]
  (LOCALx (hm3_tB ad ad_copy pt pt_copy ct rct dec ++ hm3_tA x nonce (Zlength a) (Zlength m) ++ hm3_lv gv vk vxn)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         hm3_buf (Zlength a) (map Vubyte a) ad; hm3_buf (Zlength a) (map Vubyte a) ad_copy;
         hm3_buf (Zlength m) (map Vubyte m) pt; hm3_buf (Zlength m) (map Vubyte m) pt_copy;
         hm3_buf (Zlength m + 16) (Zrepeat Vundef (Zlength m + 16)) ct; hm3_buf (Zlength m + 16) (Zrepeat Vundef (Zlength m + 16)) rct;
         hm3_buf (Zlength m) (Zrepeat Vundef (Zlength m)) dec;
         mem_mgr gv; zero_page gv; haead_globals gv; FR])).

(* after D: ct = rct = the encryption, CHECK passed *)
Definition hm3_PD (gv: globals) (vk vxn: val) (FR: mpred) : environ -> mpred :=
  EX x: Z, EX key: list byte, EX nonce: Z, EX xn: list byte, EX a: list byte, EX m: list byte,
  EX ad: val, EX ad_copy: val, EX pt: val, EX pt_copy: val, EX ct: val, EX rct: val, EX dec: val,
  PROPx [hm3_ranges x key nonce xn (Zlength a) (Zlength m)]
  (LOCALx (hm3_tB ad ad_copy pt pt_copy ct rct dec ++ hm3_tA x nonce (Zlength a) (Zlength m) ++ hm3_lv gv vk vxn)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         hm3_buf (Zlength a) (map Vubyte a) ad; hm3_buf (Zlength a) (map Vubyte a) ad_copy;
         hm3_buf (Zlength m) (map Vubyte m) pt; hm3_buf (Zlength m) (map Vubyte m) pt_copy;
         hm3_buf (Zlength m + 16) (map Vubyte (hm3_enc x key nonce xn a m)) ct; hm3_buf (Zlength m + 16) (map Vubyte (hm3_enc x key nonce xn a m)) rct;
         hm3_buf (Zlength m) (Zrepeat Vundef (Zlength m)) dec;
         mem_mgr gv; zero_page gv; haead_globals gv; FR])).

(* after E: dec = m, CHECK passed *)
Definition hm3_PE (gv: globals) (vk vxn: val) (FR: mpred) : environ -> mpred :=
  EX x: Z, EX key: list byte, EX nonce: Z, EX xn: list byte, EX a: list byte, EX m: list byte,
  EX ad: val, EX ad_copy: val, EX pt: val, EX pt_copy: val, EX ct: val, EX rct: val, EX dec: val,
  PROPx [hm3_ranges x key nonce xn (Zlength a) (Zlength m)]
  (LOCALx (hm3_tB ad ad_copy pt pt_copy ct rct dec ++ hm3_tA x nonce (Zlength a) (Zlength m) ++ hm3_lv gv vk vxn)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         hm3_buf (Zlength a) (map Vubyte a) ad; hm3_buf (Zlength a) (map Vubyte a) ad_copy;
         hm3_buf (Zlength m) (map Vubyte m) pt; hm3_buf (Zlength m) (map Vubyte m) pt_copy;
         hm3_buf (Zlength m + 16) (map Vubyte (hm3_enc x key nonce xn a m)) ct; hm3_buf (Zlength m + 16) (map Vubyte (hm3_enc x key nonce xn a m)) rct;
         hm3_buf (Zlength m) (map Vubyte m) dec;
         mem_mgr gv; zero_page gv; haead_globals gv; FR])).

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hm3_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (haead_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
