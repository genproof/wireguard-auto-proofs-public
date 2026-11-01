(* main of law prim_poly1305: the initial globals, the segments of the body and their states. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require WgNoise.contracts.x_prim_poly1305.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

Module HPC := WgNoise.harness.x_prim_poly1305.code.

Lemma hp1305m_InitGPred_filter (f: ident * globdef (fundef function) type -> bool) al gv :
  InitGPred al gv |-- (InitGPred (filter f al) gv * TT)%logic.
Proof.
  induction al as [|a al IH]; simpl.
  - unfold InitGPred; simpl. cancel.
  - unfold InitGPred in *; simpl. destruct (f a); simpl.
    + rewrite sepcon_assoc. apply sepcon_derives; auto.
    + eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply IH] |].
      rewrite (sepcon_comm (fold_right _ _ _)), <- sepcon_assoc, TT_sepcon_TT. cancel.
Qed.

Definition hp1305m_keep (x: ident * globdef (fundef function) type) : bool := Pos.eqb (fst x) HP._minusp.

Definition hp1305m_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter hp1305m_keep (Vardefs WgNoise.contracts.x_prim_poly1305.whole_prog)) in exact x).

Lemma hp1305m_vardefs_eq :
  filter hp1305m_keep (Vardefs WgNoise.contracts.x_prim_poly1305.whole_prog) = hp1305m_vardefs.
Proof. vm_compute. reflexivity. Qed.

Lemma hp1305m_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_prim_poly1305.whole_prog) gv |-- (hp1305_globals gv * TT)%logic.
Proof.
  intros Hgv. eapply derives_trans; [apply (hp1305m_InitGPred_filter hp1305m_keep) |].
  rewrite hp1305m_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred hp1305m_vardefs gv |-- (fun g => hp1305_globals g)%logic gv).
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
  match goal with |- data_at ?sh (tarray tuint 17) ?l ?p |-- _ =>
    replace l with (map Vint hrp_minusp) by
      (vm_compute; repeat match goal with |- cons _ _ = cons _ _ => f_equal
                                     | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity end) end.
  unfold hp1305_globals. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* Cutting main's body into segments                                       *)
(* ---------------------------------------------------------------------- *)

Fixpoint hp1305m_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hp1305m_seqs l' rest) end.

Fixpoint hp1305m_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hp1305m_seql l') end.

Fixpoint hp1305m_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hp1305m_flat_seq b | _ => [s] end.

Lemma hp1305m_unfold_seql l : l <> [] ->
  unfold_Ssequence (hp1305m_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hp1305m_unfold_seqs l rest :
  unfold_Ssequence (hp1305m_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hp1305m_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hp1305m_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hp1305m_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hp1305m_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hp1305m_seql l) rest)).
  - simpl. rewrite hp1305m_unfold_seql, hp1305m_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 25 statements below *)
Definition hp1305m_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hp1305m_flat_seq HPC.f_main fn_body] in
        (match fn_body HPC.f_main with Ssequence s _ => hp1305m_flat_seq s | s => [s] end) in exact x).

Definition hp1305m_sub (i n: nat) : statement := hp1305m_seql (firstn n (skipn i hp1305m_stmts)).

(* the segments *)
Definition hp1305m_segA := ltac:(let x := eval cbv beta iota delta [hp1305m_sub hp1305m_seql firstn skipn hp1305m_stmts] in (hp1305m_sub 0 8) in exact x).
Definition hp1305m_segB := ltac:(let x := eval cbv beta iota delta [hp1305m_sub hp1305m_seql firstn skipn hp1305m_stmts] in (hp1305m_sub 8 4) in exact x).
Definition hp1305m_segC := ltac:(let x := eval cbv beta iota delta [hp1305m_sub hp1305m_seql firstn skipn hp1305m_stmts] in (hp1305m_sub 12 1) in exact x).
Definition hp1305m_segD := ltac:(let x := eval cbv beta iota delta [hp1305m_sub hp1305m_seql firstn skipn hp1305m_stmts] in (hp1305m_sub 13 3) in exact x).
Definition hp1305m_segE := ltac:(let x := eval cbv beta iota delta [hp1305m_sub hp1305m_seql firstn skipn hp1305m_stmts] in (hp1305m_sub 16 4) in exact x).
Definition hp1305m_segF := ltac:(let x := eval cbv beta iota delta [hp1305m_sub hp1305m_seql firstn skipn hp1305m_stmts] in (hp1305m_sub 20 5) in exact x).

Definition hp1305m_l (i n: nat) : list statement := firstn n (skipn i hp1305m_stmts).

Lemma hp1305m_stmts_length : length hp1305m_stmts = 25%nat.
Proof. reflexivity. Qed.

Lemma hp1305m_body_eq :
  fn_body HPC.f_main =
  Ssequence
    (hp1305m_seqs (hp1305m_l 0 8) (hp1305m_seqs (hp1305m_l 8 4) (hp1305m_seqs (hp1305m_l 12 1)
      (hp1305m_seqs (hp1305m_l 13 3) (hp1305m_seqs (hp1305m_l 16 4) (hp1305m_seql (hp1305m_l 20 5)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hp1305m_segs_eq :
  hp1305m_segA = hp1305m_seql (hp1305m_l 0 8) /\ hp1305m_segB = hp1305m_seql (hp1305m_l 8 4) /\
  hp1305m_segC = hp1305m_seql (hp1305m_l 12 1) /\ hp1305m_segD = hp1305m_seql (hp1305m_l 13 3) /\
  hp1305m_segE = hp1305m_seql (hp1305m_l 16 4) /\ hp1305m_segF = hp1305m_seql (hp1305m_l 20 5).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Definition hp1305m_Delta : tycontext := func_tycontext HPC.f_main hp1305_V hp1305_Gprog [].

Definition hp1305m_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hp1305_post gv)) (stackframe_of HPC.f_main).

(* struct poly1305_desc_ctx (in W) *)
Definition t_hpctx : type := Tstruct HPC._poly1305_desc_ctx noattr.

(* the locals' addresses and the globals *)
Definition hp1305m_lv (gv: globals) (vd vkey vkey0 vref: val) : list localdef :=
  [lvar HPC._d t_hpctx vd; lvar HPC._key (tarray tuchar 32) vkey; lvar HPC._key0 (tarray tuchar 32) vkey0;
   lvar HPC._ref (tarray tuchar 16) vref; gvars gv].

(* the temps fixed after segment A *)
Definition hp1305m_tv (n: Z) (msg copy tag: val) : list localdef :=
  [temp HPC._n (Vlong (Int64.repr n)); temp HPC._msg msg; temp HPC._copy copy; temp HPC._tag tag].

(* a malloc'd byte buffer of n bytes with contents v *)
Definition hp1305m_buf (n: Z) (v: list val) (p: val) : mpred :=
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic.

(* the facts on the drawn values *)
Definition hp1305m_ranges (n: Z) (kb: list byte) : Prop :=
  Zlength kb = 32 /\ 0 <= n <= Int64.max_signed.

(* before segment A (after the prologue) *)
Definition hp1305m_P0 (gv: globals) (vd vkey vkey0 vref: val) (FR: mpred) : environ -> mpred :=
  PROPx [] (LOCALx (hp1305m_lv gv vd vkey vkey0 vref)
  (SEPx [data_at_ Tsh t_hpctx vd; data_at_ Tsh (tarray tuchar 32) vkey;
         data_at_ Tsh (tarray tuchar 32) vkey0; data_at_ Tsh (tarray tuchar 16) vref;
         mem_mgr gv; hp1305_globals gv; FR])).

(* after A: key drawn and copied, n drawn, buffers allocated (non-NULL) *)
Definition hp1305m_PA (gv: globals) (vd vkey vkey0 vref: val) (FR: mpred) : environ -> mpred :=
  EX n: Z, EX kb: list byte, EX msg: val, EX copy: val, EX tag: val,
  PROPx [hp1305m_ranges n kb]
  (LOCALx (hp1305m_tv n msg copy tag ++ hp1305m_lv gv vd vkey vkey0 vref)
  (SEPx [data_at_ Tsh t_hpctx vd;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0;
         data_at_ Tsh (tarray tuchar 16) vref;
         hp1305m_buf n (Zrepeat Vundef n) msg; hp1305m_buf n (Zrepeat Vundef n) copy;
         hp1305m_buf 16 (Zrepeat Vundef 16) tag;
         mem_mgr gv; hp1305_globals gv; FR])).

(* the state of the chunk loop of segment C (pos bytes absorbed); the context is in Poly1305.CS *)
Definition hp1305m_PC (gv: globals) (vd vkey vkey0 vref: val) (FR: mpred)
    (n: Z) (kb mb: list byte) (msg copy tag: val) (pos: Z) : environ -> mpred :=
  PROPx [hp1305m_ranges n kb; Zlength mb = n; 0 <= pos <= n]
  (LOCALx (temp HPC._pos (Vlong (Int64.repr pos)) :: hp1305m_tv n msg copy tag ++
           hp1305m_lv gv vd vkey vkey0 vref)
  (SEPx [p1305_state Tsh kb (sublist 0 pos mb) vd;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0;
         data_at_ Tsh (tarray tuchar 16) vref;
         hp1305m_buf n (map Vubyte mb) msg; hp1305m_buf n (map Vubyte mb) copy;
         hp1305m_buf 16 (Zrepeat Vundef 16) tag;
         mem_mgr gv; hp1305_globals gv; FR])).

(* after B: message drawn and copied, context initialised, pos = 0 *)
Definition hp1305m_PB (gv: globals) (vd vkey vkey0 vref: val) (FR: mpred) : environ -> mpred :=
  EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val, EX tag: val,
  hp1305m_PC gv vd vkey vkey0 vref FR n kb mb msg copy tag 0.

(* after D: finalised (the context zero, in Poly1305.CS, as poly1305_final leaves it), tag = ref = the tag,
   CHECK(tag == ref) passed *)
Definition hp1305m_PD (gv: globals) (vd vkey vkey0 vref: val) (FR: mpred) : environ -> mpred :=
  EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val, EX tag: val,
  PROPx [hp1305m_ranges n kb; Zlength mb = n]
  (LOCALx (hp1305m_tv n msg copy tag ++ hp1305m_lv gv vd vkey vkey0 vref)
  (SEPx [@data_at Poly1305.CS Tsh t_p1305_ctx p1305_ctx_zero vd;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0;
         data_at Tsh (tarray tuchar 16) (map Vubyte (poly1305_tag kb mb)) vref;
         hp1305m_buf n (map Vubyte mb) msg; hp1305m_buf n (map Vubyte mb) copy;
         hp1305m_buf 16 (map Vubyte (poly1305_tag kb mb)) tag;
         mem_mgr gv; hp1305_globals gv; FR])).

(* after E: the context checked (given back as data_at_ in W) *)
Definition hp1305m_PE (gv: globals) (vd vkey vkey0 vref: val) (FR: mpred) : environ -> mpred :=
  EX n: Z, EX kb: list byte, EX mb: list byte, EX msg: val, EX copy: val, EX tag: val,
  PROPx [hp1305m_ranges n kb; Zlength mb = n]
  (LOCALx (hp1305m_tv n msg copy tag ++ hp1305m_lv gv vd vkey vkey0 vref)
  (SEPx [data_at_ Tsh t_hpctx vd;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0;
         data_at Tsh (tarray tuchar 16) (map Vubyte (poly1305_tag kb mb)) vref;
         hp1305m_buf n (map Vubyte mb) msg; hp1305m_buf n (map Vubyte mb) copy;
         hp1305m_buf 16 (map Vubyte (poly1305_tag kb mb)) tag;
         mem_mgr gv; hp1305_globals gv; FR])).

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hp1305m_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hp1305_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
