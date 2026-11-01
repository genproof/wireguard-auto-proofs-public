(* main of law prim_blake2s: the initial globals, the segments of the body and their states. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.contracts.x_prim_blake2s.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Lemma hb2s_InitGPred_filter (f: ident * globdef (fundef function) type -> bool) al gv :
  InitGPred al gv |-- (InitGPred (filter f al) gv * TT)%logic.
Proof.
  induction al as [|a al IH]; simpl.
  - unfold InitGPred; simpl. cancel.
  - unfold InitGPred in *; simpl. destruct (f a); simpl.
    + rewrite sepcon_assoc. apply sepcon_derives; auto.
    + eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply IH] |].
      rewrite (sepcon_comm (fold_right _ _ _)), <- sepcon_assoc, TT_sepcon_TT. cancel.
Qed.

Definition hb2s_keep (x: ident * globdef (fundef function) type) : bool :=
  orb (Pos.eqb (fst x) HB._RB2S_IV) (orb (Pos.eqb (fst x) HB._RB2S_SIGMA) (Pos.eqb (fst x) _blake2s_sigma)).

Definition hb2s_vardefs :=
  ltac:(let x := eval vm_compute in (filter hb2s_keep (Vardefs WgNoise.contracts.x_prim_blake2s.whole_prog)) in exact x).

Lemma hb2s_vardefs_eq : filter hb2s_keep (Vardefs WgNoise.contracts.x_prim_blake2s.whole_prog) = hb2s_vardefs.
Proof. vm_compute. reflexivity. Qed.

(* the two 2-D tables seen as flat byte arrays (globvar2pred ignores gvar_info) *)
Definition hb2s_flat (x: ident * globdef (fundef function) type) : ident * globdef (fundef function) type :=
  match x with
  | (i, Gvar v) => (i, Gvar (mkglobvar (tarray tuchar 160) (gvar_init v) (gvar_readonly v) (gvar_volatile v)))
  | _ => x
  end.

Definition hb2s_vardefs_flat :=
  ltac:(let x := eval vm_compute in
    (match hb2s_vardefs with [a; b; c] => [a; hb2s_flat b; hb2s_flat c] | l => l end) in exact x).

Lemma hb2s_InitGPred_flat gv : InitGPred hb2s_vardefs gv = InitGPred hb2s_vardefs_flat gv.
Proof. reflexivity. Qed.

Lemma hb2s_sigma_flat {cs: compspecs} sh p :
  @data_at cs sh (tarray tuchar 160) (concat blake2s_sigma_val) p =
  @data_at cs sh (tarray (tarray tuchar 16) 10) blake2s_sigma_val p.
Proof.
  rewrite (data_at_2darray_concat sh tuchar 10 16); [reflexivity | reflexivity | | reflexivity].
  repeat constructor.
Qed.

Lemma hb2s_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_prim_blake2s.whole_prog) gv |--
  (hb2s_globals gv * blake2s_globals gv * TT)%logic.
Proof.
  intros Hgv. eapply derives_trans; [apply (hb2s_InitGPred_filter hb2s_keep) |].
  rewrite hb2s_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  rewrite hb2s_InitGPred_flat.
  change (InitGPred hb2s_vardefs_flat gv |-- (fun g => hb2s_globals g * blake2s_globals g)%logic gv).
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
  repeat match goal with |- context [data_at ?sh (tarray tuchar 160) ?l ?p] =>
    lazymatch l with concat _ => fail
    | _ => replace l with (concat blake2s_sigma_val) by (vm_compute; reflexivity) end end.
  match goal with |- context [data_at ?sh (tarray tuint 8) ?l ?p] =>
    replace l with (map Vint b2s_IV) by
      (vm_compute; repeat match goal with |- cons _ _ = cons _ _ => f_equal
                                     | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity end) end.
  change (gv 8363355679093%positive) with (gv HB._RB2S_IV).
  change (gv 1815138450477164917%positive) with (gv HB._RB2S_SIGMA).
  change (gv 351097212369991831168331%positive) with (gv _blake2s_sigma).
  unfold hb2s_globals, blake2s_globals. rewrite <- !hb2s_sigma_flat.
  rewrite (@data_at_tarray_tuchar_cs Blake2s.CS W_prim_blake2s).
  cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* Cutting main's body into segments                                       *)
(* ---------------------------------------------------------------------- *)

Module HC := WgNoise.harness.x_prim_blake2s.code.

(* s1; (s2; (...; rest)) and s1; (s2; (...; sn)) *)
Fixpoint hb2s_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hb2s_seqs l' rest) end.

Fixpoint hb2s_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hb2s_seql l') end.

Fixpoint hb2s_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hb2s_flat_seq b | _ => [s] end.

Lemma hb2s_unfold_seql l : l <> [] ->
  unfold_Ssequence (hb2s_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hb2s_unfold_seqs l rest :
  unfold_Ssequence (hb2s_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hb2s_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hb2s_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hb2s_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hb2s_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hb2s_seql l) rest)).
  - simpl. rewrite hb2s_unfold_seql, hb2s_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 33 statements below *)
Definition hb2s_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hb2s_flat_seq HC.f_main fn_body] in
        (match fn_body HC.f_main with Ssequence s _ => hb2s_flat_seq s | s => [s] end) in exact x).

Definition hb2s_sub (i n: nat) : statement := hb2s_seql (firstn n (skipn i hb2s_stmts)).

(* the segments *)
Definition hb2s_segA := ltac:(let x := eval cbv beta iota delta [hb2s_sub hb2s_seql firstn skipn hb2s_stmts] in (hb2s_sub 0 12) in exact x).
Definition hb2s_segB := ltac:(let x := eval cbv beta iota delta [hb2s_sub hb2s_seql firstn skipn hb2s_stmts] in (hb2s_sub 12 4) in exact x).
Definition hb2s_segC := ltac:(let x := eval cbv beta iota delta [hb2s_sub hb2s_seql firstn skipn hb2s_stmts] in (hb2s_sub 16 1) in exact x).
Definition hb2s_segD := ltac:(let x := eval cbv beta iota delta [hb2s_sub hb2s_seql firstn skipn hb2s_stmts] in (hb2s_sub 17 2) in exact x).
Definition hb2s_segE := ltac:(let x := eval cbv beta iota delta [hb2s_sub hb2s_seql firstn skipn hb2s_stmts] in (hb2s_sub 19 5) in exact x).
Definition hb2s_segF := ltac:(let x := eval cbv beta iota delta [hb2s_sub hb2s_seql firstn skipn hb2s_stmts] in (hb2s_sub 24 9) in exact x).

Definition hb2s_l (i n: nat) : list statement := firstn n (skipn i hb2s_stmts).

Lemma hb2s_body_eq :
  fn_body HC.f_main =
  Ssequence
    (hb2s_seqs (hb2s_l 0 12) (hb2s_seqs (hb2s_l 12 4) (hb2s_seqs (hb2s_l 16 1) (hb2s_seqs (hb2s_l 17 2)
      (hb2s_seqs (hb2s_l 19 5) (hb2s_seql (hb2s_l 24 9)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hb2s_segs_eq :
  hb2s_segA = hb2s_seql (hb2s_l 0 12) /\ hb2s_segB = hb2s_seql (hb2s_l 12 4) /\
  hb2s_segC = hb2s_seql (hb2s_l 16 1) /\ hb2s_segD = hb2s_seql (hb2s_l 17 2) /\
  hb2s_segE = hb2s_seql (hb2s_l 19 5) /\ hb2s_segF = hb2s_seql (hb2s_l 24 9).
Proof. repeat split. Qed.

Lemma hb2s_stmts_length : length hb2s_stmts = 33%nat.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Definition hb2s_Delta : tycontext := func_tycontext HC.f_main hb2s_V hb2s_Gprog [].

Definition hb2s_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hb2s_post gv)) (stackframe_of HC.f_main).

Definition t_hctx : type := Tstruct HC._blake2s_ctx noattr.

(* the locals' addresses and the globals *)
Definition hb2s_lv (gv: globals) (vctx vkey vkc: val) : list localdef :=
  [lvar HC._ctx t_hctx vctx; lvar HC._key (tarray tuchar 32) vkey; lvar HC._key_copy (tarray tuchar 32) vkc;
   gvars gv].

(* the temps fixed after segment A *)
Definition hb2s_tv (outlen keylen n: Z) (msg copy out ref out2: val) : list localdef :=
  [temp HC._outlen (Vlong (Int64.repr outlen)); temp HC._keylen (Vlong (Int64.repr keylen));
   temp HC._n (Vlong (Int64.repr n)); temp HC._msg msg; temp HC._copy copy; temp HC._out out;
   temp HC._ref ref; temp HC._out2 out2].

(* a malloc'd byte buffer of n bytes with contents v *)
Definition hb2s_buf (n: Z) (v: list val) (p: val) : mpred :=
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic.

(* the facts on the drawn values *)
Definition hb2s_ranges (outlen keylen n: Z) (kb: list byte) : Prop :=
  1 <= outlen <= 32 /\ 0 <= keylen <= 32 /\ Zlength kb = 32 /\ 0 <= n <= Int64.max_signed.

(* before segment A (after the prologue) *)
Definition hb2s_P0 (gv: globals) (vctx vkey vkc: val) (FR: mpred) : environ -> mpred :=
  PROPx [] (LOCALx (hb2s_lv gv vctx vkey vkc)
  (SEPx [data_at_ Tsh t_hctx vctx; data_at_ Tsh (tarray tuchar 32) vkey;
         data_at_ Tsh (tarray tuchar 32) vkc; mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR])).

(* after A: inputs drawn, buffers allocated (non-NULL) *)
Definition hb2s_PA (gv: globals) (vctx vkey vkc: val) (FR: mpred) : environ -> mpred :=
  EX outlen: Z, EX keylen: Z, EX n: Z, EX kb: list byte, EX msg: val, EX copy: val, EX out: val,
  EX ref: val, EX out2: val,
  PROPx [hb2s_ranges outlen keylen n kb]
  (LOCALx (hb2s_tv outlen keylen n msg copy out ref out2 ++ hb2s_lv gv vctx vkey vkc)
  (SEPx [data_at_ Tsh t_hctx vctx; data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkc;
         hb2s_buf n (Zrepeat Vundef n) msg; hb2s_buf n (Zrepeat Vundef n) copy;
         hb2s_buf outlen (Zrepeat Vundef outlen) out; hb2s_buf outlen (Zrepeat Vundef outlen) ref;
         hb2s_buf outlen (Zrepeat Vundef outlen) out2;
         mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR])).

(* the state of the chunk loop of segment C (pos bytes absorbed) *)
Definition hb2s_PC (gv: globals) (vctx vkey vkc: val) (FR: mpred)
    (outlen keylen n: Z) (kb mb: list byte) (msg copy out ref out2: val) (pos: Z) : environ -> mpred :=
  PROPx [hb2s_ranges outlen keylen n kb; Zlength mb = n; 0 <= pos <= n]
  (LOCALx (temp HC._pos (Vlong (Int64.repr pos)) :: hb2s_tv outlen keylen n msg copy out ref out2 ++
           hb2s_lv gv vctx vkey vkc)
  (SEPx [blake2s_state Tsh (sublist 0 keylen kb) outlen (sublist 0 pos mb) vctx;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkc;
         hb2s_buf n (map Vubyte mb) msg; hb2s_buf n (map Vubyte mb) copy;
         hb2s_buf outlen (Zrepeat Vundef outlen) out; hb2s_buf outlen (Zrepeat Vundef outlen) ref;
         hb2s_buf outlen (Zrepeat Vundef outlen) out2;
         mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR])).

(* after B: message drawn and copied, context initialised, pos = 0 *)
Definition hb2s_PB (gv: globals) (vctx vkey vkc: val) (FR: mpred) : environ -> mpred :=
  EX outlen: Z, EX keylen: Z, EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val,
  EX out: val, EX ref: val, EX out2: val,
  hb2s_PC gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 0.

(* after C: the whole message absorbed *)
Definition hb2s_PC' (gv: globals) (vctx vkey vkc: val) (FR: mpred) : environ -> mpred :=
  EX outlen: Z, EX keylen: Z, EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val,
  EX out: val, EX ref: val, EX out2: val,
  hb2s_PC gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 n.

(* after D: finalised: the context is zero (in Blake2s.CS, as blake2s_final leaves it), out = the digest *)
Definition hb2s_PD (gv: globals) (vctx vkey vkc: val) (FR: mpred) : environ -> mpred :=
  EX outlen: Z, EX keylen: Z, EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val,
  EX out: val, EX ref: val, EX out2: val,
  PROPx [hb2s_ranges outlen keylen n kb; Zlength mb = n]
  (LOCALx (hb2s_tv outlen keylen n msg copy out ref out2 ++ hb2s_lv gv vctx vkey vkc)
  (SEPx [@data_at Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero vctx;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkc;
         hb2s_buf n (map Vubyte mb) msg; hb2s_buf n (map Vubyte mb) copy;
         hb2s_buf outlen (map Vubyte (blake2s (sublist 0 keylen kb) outlen mb)) out;
         hb2s_buf outlen (Zrepeat Vundef outlen) ref;
         hb2s_buf outlen (Zrepeat Vundef outlen) out2;
         mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR])).

(* after E: the reference computed and compared, the context checked (given back as data_at_) *)
Definition hb2s_PE (gv: globals) (vctx vkey vkc: val) (FR: mpred) : environ -> mpred :=
  EX outlen: Z, EX keylen: Z, EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val,
  EX out: val, EX ref: val, EX out2: val,
  PROPx [hb2s_ranges outlen keylen n kb; Zlength mb = n]
  (LOCALx (hb2s_tv outlen keylen n msg copy out ref out2 ++ hb2s_lv gv vctx vkey vkc)
  (SEPx [data_at_ Tsh t_hctx vctx;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkc;
         hb2s_buf n (map Vubyte mb) msg; hb2s_buf n (map Vubyte mb) copy;
         hb2s_buf outlen (map Vubyte (blake2s (sublist 0 keylen kb) outlen mb)) out;
         hb2s_buf outlen (map Vubyte (blake2s (sublist 0 keylen kb) outlen mb)) ref;
         hb2s_buf outlen (Zrepeat Vundef outlen) out2;
         mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR])).
