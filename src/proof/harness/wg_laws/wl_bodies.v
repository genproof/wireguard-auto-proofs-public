(* The bodies of the wg_laws.h helpers (specifications: wl_spec.v), proved once against the copies of
   harness/ae_roundtrip.c, under any compspecs.  Each body has two versions: `wl_body_<f>_ctx`, whose context is
   the function's callees only, is the one a law moves into its program (asm_lib's asm_body_lift: every
   specification of the context must be a function of the law's program, and the program's copy is the same
   Clight); `wl_body_<f>` has the whole environment as context. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import WgNoise.harness.ae_roundtrip.code.
Require WgNoise.proof.assembly.asm_env.
Require WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.

Local Open Scope Z_scope.

Section WgLawsBodies.
Context {cs: compspecs}.

(* any_bytes with its callees only: malloc, and nondet_bytes without its NULL case (the body calls it only
   when the block is not NULL).  This is the version the laws move into their programs: a law's context
   holds these two specifications, or the framework's NULL-tolerant nondet_bytes, a subtype of this one. *)
Lemma wl_body_any_bytes_ctx :
  semax_body nil [(_quickproof_malloc, @malloc_spec' cs); @WgNoise.proof.assembly.asm_env.nondet_bytes_spec cs]
    WgNoise.harness.ae_roundtrip.code.f_any_bytes any_bytes_spec.
Proof.
  start_function.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros p.
  destruct (eq_dec p nullval) as [Hp|Hp].
  - (* malloc failed: no call, the result is NULL *)
    subst p.
    forward_if (PROP () LOCAL (temp _t'2 (Vint Int.zero); temp _bytes nullval; gvars gv;
                               temp _n (Vlong (Int64.repr n)))
                SEP (mem_mgr gv)).
    { discriminate. }
    { forward. entailer!. }
    forward_if (PROP () LOCAL (temp _bytes nullval; gvars gv) SEP (mem_mgr gv)).
    { contradiction. }
    { forward. entailer!. }
    forward.
    Exists nullval (repeat Byte.zero (Z.to_nat n)).
    entailer!.
    rewrite Zlength_repeat; lia.
  - (* malloc succeeded: nondet_bytes fills the block unless n = 0 *)
    Intros.
    forward_if (PROP () LOCAL (temp _t'2 (Vint (if Z.eq_dec n 0 then Int.zero else Int.one));
                               temp _bytes p; gvars gv; temp _n (Vlong (Int64.repr n)))
                SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p; data_at_ Ews (tarray tuchar n) p)).
    { forward. entailer!.
      destruct (Z.eq_dec n 0); [subst; reflexivity |].
      unfold Int64.cmpu. rewrite Int64.eq_false; [reflexivity |].
      intro E; apply repr_inj_unsigned64 in E; rep_lia. }
    { contradiction. }
    destruct (Z.eq_dec n 0) as [Hn|Hn].
    + (* n = 0: no call, the block is empty *)
      subst n.
      forward_if (PROP () LOCAL (temp _bytes p; gvars gv)
                  SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 0) p; data_at_ Ews (tarray tuchar 0) p)).
      { contradiction. }
      { forward. entailer!. }
      forward.
      Exists p (@nil byte).
      rewrite if_false by auto. entailer!.
    + (* n > 0: nondet_bytes fills the block *)
      forward_if (EX bs: list byte,
                  PROP (Zlength bs = n) LOCAL (temp _bytes p; gvars gv)
                  SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p;
                       data_at Ews (tarray tuchar n) (map Vubyte bs) p)).
      { forward_call (p, n, Ews).
        Intros bs.
        Exists (map Byte.repr bs).
        entailer!.
        - rewrite Zlength_map; reflexivity.
        - (* the bytes nondet_bytes returns, as Z in byte range, are the bytes map Byte.repr bs *)
          apply derives_refl'. f_equal. rewrite map_map. apply map_ext_in. intros b Hb.
          match goal with HF: Forall _ bs |- _ => rewrite Forall_forall in HF; specialize (HF b Hb) end.
          unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity. }
      { match goal with HE: Int.one = Int.zero |- _ => inv HE end. }
      Intros bs.
      forward.
      Exists p bs.
      rewrite if_false by auto. entailer!.
Qed.

Lemma wl_body_any_bytes :
  semax_body nil (@wl_imports cs) WgNoise.harness.ae_roundtrip.code.f_any_bytes any_bytes_spec.
Proof.
  (* the environment holds the same malloc and the NULL-tolerant nondet_bytes, a subtype of the one used above *)
  eapply (@WgNoise.proof.assembly.asm_lib.asm_body_lift cs cs nil nil); [ | | | | | apply wl_body_any_bytes_ctx].
  - apply cspecs_sub_refl.
  - constructor.
  - unfold wl_imports, env_specs; simpl. repeat constructor; simpl; intuition discriminate.
  - constructor.
  - repeat constructor.
    + eexists; split; [reflexivity | apply funspec_sub_refl].
    + eexists; split; [reflexivity | apply WgNoise.proof.assembly.asm_env.nondet_bytes_sub].
Qed.

(* A byte stored as a value is an unsigned char, as a load from a tuchar cell requires. *)
Lemma wl_is_int_Vubyte (b: byte) : is_int I8 Unsigned (Vubyte b).
Proof.
  unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(* A cell of a buffer whose first n cells are the bytes x: below n it is the byte of x, as a value. *)
Lemma wl_Znth_prefix_Vubyte (c: list val) (x: list byte) (n i: Z) :
  0 <= i < n -> n <= Zlength c -> sublist 0 n c = map Vubyte x -> Znth i c = Vubyte (Znth i x).
Proof.
  intros Hi Hn E.
  assert (Zlength x = n) as Hx.
  { rewrite <- (Zlength_map _ _ Vubyte), <- E, Zlength_sublist by lia. lia. }
  replace (Znth i c) with (Znth i (sublist 0 n c)) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite E, Znth_map by lia. reflexivity.
Qed.

(* The body of bytes_eq with an empty context (it calls nothing): the version the laws move into their programs,
   whose function contexts need not contain the environment. *)
Lemma wl_body_bytes_eq_ctx :
  semax_body nil nil WgNoise.harness.ae_roundtrip.code.f_bytes_eq bytes_eq_spec.
Proof.
  start_function.
  rename H2 into Ea, H3 into Eb.
  assert (Zlength xa = n) as Hxa.
  { rewrite <- (Zlength_map _ _ Vubyte), <- Ea, Zlength_sublist by lia. lia. }
  assert (Zlength xb = n) as Hxb.
  { rewrite <- (Zlength_map _ _ Vubyte), <- Eb, Zlength_sublist by lia. lia. }
  forward_for_simple_bound n (EX i:Z,
    PROP (sublist 0 i xa = sublist 0 i xb)
    LOCAL (temp _a a; temp _b b; temp _n (Vlong (Int64.repr n)))
    SEP (data_at sha (tarray tuchar (Zlength ca)) ca a;
         data_at shb (tarray tuchar (Zlength cb)) cb b)).
  - entailer!.
  - cbv beta. Intros.
    pose proof (wl_Znth_prefix_Vubyte ca xa n i ltac:(lia) ltac:(lia) Ea) as Ca.
    pose proof (wl_Znth_prefix_Vubyte cb xb n i ltac:(lia) ltac:(lia) Eb) as Cb.
    (* the loads below read the cells with VST's default value Vundef *)
    change (@Znth val Inhabitant_val i ca) with (@Znth val Vundef i ca) in Ca.
    change (@Znth val Inhabitant_val i cb) with (@Znth val Vundef i cb) in Cb.
    forward.
    { entailer!. rewrite Ca. apply wl_is_int_Vubyte. }
    forward.
    { entailer!. rewrite Cb. apply wl_is_int_Vubyte. }
    rewrite Ca, Cb.
    forward_if (PROP (Znth i xa = Znth i xb)
      LOCAL (temp _i (Vlong (Int64.repr i)); temp _a a; temp _b b; temp _n (Vlong (Int64.repr n)))
      SEP (data_at sha (tarray tuchar (Zlength ca)) ca a;
           data_at shb (tarray tuchar (Zlength cb)) cb b)).
    + forward.
      destruct (list_eq_dec Byte.eq_dec xa xb); [subst; contradiction|].
      entailer!.
    + forward. entailer!.
      rewrite <- (Byte.repr_unsigned (Znth i xa)), <- (Byte.repr_unsigned (Znth i xb)). f_equal. assumption.
    + Intros. entailer!.
      rewrite (sublist_split 0 i (i+1) xa), (sublist_split 0 i (i+1) xb), !sublist_len_1 by lia. congruence.
  - forward.
    match goal with H: sublist 0 _ xa = sublist 0 _ xb |- _ =>
      rewrite !sublist_same in H by lia; subst xa end.
    destruct (list_eq_dec Byte.eq_dec xb xb); [|contradiction].
    entailer!.
Qed.

(* The same body with the environment as context: the empty context is included in it. *)
Lemma wl_body_bytes_eq :
  semax_body nil (@wl_imports cs) WgNoise.harness.ae_roundtrip.code.f_bytes_eq bytes_eq_spec.
Proof.
  eapply semax_body_subsumption; [apply wl_body_bytes_eq_ctx|].
  apply tycontext_sub_Gprog_nil.
  unfold wl_imports, QuickProof.Env.env_specs; simpl.
  repeat constructor; simpl; intuition discriminate.
Qed.

(* The body of upto with its only callee, nondet_size, as context: the version the laws move into their
   programs. *)
Lemma wl_body_upto_ctx :
  semax_body nil [nondet_size_spec] WgNoise.harness.ae_roundtrip.code.f_upto upto_spec.
Proof.
  start_function. forward_call. Intros v.
  forward_if (EX r: Z, PROP (0 <= r <= max) LOCAL (temp _t'2 (Vlong (Int64.repr r))) SEP ()).
  - forward. Exists v. entailer!.
  - forward. Exists max. entailer!.
  - Intros r. forward. Exists r. entailer!.
Qed.

(* The body of any_u64 with its only callee, nondet_u32, as context. *)
Lemma wl_body_any_u64_ctx :
  semax_body nil [nondet_u32_spec] WgNoise.harness.ae_roundtrip.code.f_any_u64 any_u64_spec.
Proof.
  start_function.
  (* forward_call cannot fuse a call with the widening cast or the return that follows it: give each call its
     own postcondition *)
  apply semax_seq' with (P' := EX hi: Z,
    PROP (0 <= hi <= Int.max_unsigned) LOCAL (temp _high (Vlong (Int64.repr hi))) SEP ()).
  { apply semax_seq' with (P' := EX hi: Z,
      PROP (0 <= hi <= Int.max_unsigned) LOCAL (temp _t'1 (Vint (Int.repr hi))) SEP ()).
    - forward_call tt. Intros v. Exists v. entailer!.
    - Intros hi. forward. Exists hi. entailer!. }
  Intros hi.
  apply semax_seq' with (P' := EX lo: Z,
    PROP (0 <= lo <= Int.max_unsigned)
    LOCAL (temp _high (Vlong (Int64.repr hi)); temp _t'2 (Vint (Int.repr lo))) SEP ()).
  { forward_call tt. Intros v. Exists v. entailer!. }
  Intros lo. forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. rewrite Int64.repr_unsigned. reflexivity.
Qed.

(* upto and any_u64 with the environment as context: their callees' specifications are the environment's. *)
Lemma wl_body_upto :
  semax_body nil (@wl_imports cs) WgNoise.harness.ae_roundtrip.code.f_upto upto_spec.
Proof.
  eapply (@WgNoise.proof.assembly.asm_lib.asm_body_lift cs cs nil nil); [ | | | | | apply wl_body_upto_ctx].
  - apply cspecs_sub_refl.
  - constructor.
  - unfold wl_imports, env_specs; simpl. repeat constructor; simpl; intuition discriminate.
  - constructor.
  - repeat constructor. eexists; split; [reflexivity | apply funspec_sub_refl].
Qed.

Lemma wl_body_any_u64 :
  semax_body nil (@wl_imports cs) WgNoise.harness.ae_roundtrip.code.f_any_u64 any_u64_spec.
Proof.
  eapply (@WgNoise.proof.assembly.asm_lib.asm_body_lift cs cs nil nil); [ | | | | | apply wl_body_any_u64_ctx].
  - apply cspecs_sub_refl.
  - constructor.
  - unfold wl_imports, env_specs; simpl. repeat constructor; simpl; intuition discriminate.
  - constructor.
  - repeat constructor. eexists; split; [reflexivity | apply funspec_sub_refl].
Qed.

End WgLawsBodies.
