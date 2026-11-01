(* law create_any: main's body cut into phases, and
   the states between them.  The v1 proof is the model: same conventions, same phases where the C did not change.

   Conventions of the states (all phases):
   - main runs in the world compspecs W := W_create_any, with the HARNESS unit's varspecs hca5_V and Delta
     hca5_Delta (imports: hca5_imports = hc4_imports ++ hc4_G_create_any, the shared layers v4).  The SEP items are
     kept in the compspecs of the specifications that consume them: the protocol objects through prot_repr3's
     predicates (device_rep, itable, ptable, peer_rep, init_rep / resp_rep: Noise.CS inside), the shim's state with
     EXACT refcount_t warnings `shim_state4 gv S w` (prot_repr4.v; w never changes: a parameter of every state),
     the harness structs m_identity / m_state / hs_snap as `@data_at(_) HCS`, the snapshots pr_snap /
     dev_snap / shim_snap as `@data_at(_) CKS` (hc4_specs.v), byte buffers as hbytes / hout (HCS), the kents as
     common4's `kents_rep W` (their keypairs' entries are pool items of the index table).
   - main's body = S1; return 0 with S1 = the 35 statements of hca5_stmts (the last one is `return 0`):
       A =  0..7   boot clock, wg_noise_init, raw / pub / psk, use_psk, setup_device, m_identity_of
       B =  8..10  setup_peer (its handshake entry joins the index table's pool), m_precomputed,
                   CHECK(bytes_eq(p.handshake.precomputed_static_static, dh, 32))
       C = 11..14  hs_randomize, peer_randomize_rest, p.refcount.refcount = draw_peer_refs(),
                   maybe wg_index_hashtable_insert(&ita, &p.handshake.entry)
       D = 15..20  kes = kents_add(&ita, NULL, &p, 1), kents_snap(kes), pr_take(&ps, &p),
                   refs0 = p.refcount.refcount, dev_take(&ds, &wa), shim_take(&ss)
       E = 21..24  hs_take(&s), hs_take(&x), op = nondet_u8() & 1, ok = 0
       F = 25      if (op == 0) { create_initiation block } else { create_response block }
                   (hca5_fdefs.v: then-branch F0 from hca5_SEo 0, else-branch F1 from hca5_SEo 1, both to hca5_SF)
       G = 26..27  if (ok) { CHECKs on the reinserted entry; x.next / x.hashed / x.index }; CHECK(hs_same)
       H = 28..31  n = entry.hashed ? 1 : 0; CHECK(kents_same_but_next(kes, &ita)); the kents' CHECK loop;
                   CHECK(table_len(&ita) == n)
       I = 32..34  CHECK(pr_same(&ps, &p) && p.refcount.refcount == refs0 && dev_same(&ds, &wa) && shim_same(&ss));
                   kents_free(kes); return 0
   - The states: hca5_S0 (prologue) -A-> hca5_SA -B-> hca5_SB -C-> hca5_SB -D-> hca5_SK -E-> hca5_SE
     -F-> hca5_SF -G-> hca5_SG -H-> hca5_SG -I-> (returns).
   - The index table: after D its pool is the kents' keypair entries (KD order = list order, the head = the last one
     created; share Ews, KEYPAIR, peer &p, index kd_idx, every one hashed) followed by p's handshake entry (share
     Tsh, HANDSHAKE, peer &p): `hca5_pool`.  T = the table the snapshots (kents_snap) were taken in; after F the
     current table T' is T, or T with p's handshake entry reinserted (hca5_res_ok).
   - `hca5_rest`: what D created and only G..I read: the kents (snapshotted in T) and the three snapshots ps / ds / ss
     (the peer P after C, the device, the shim S0 after D: hca5_cnt S0 = the counters the shim keeps).
   - FR: an opaque frame (TT * has_ext), carried along. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require WgNoise.contracts.x_create_any.
Require WgNoise.harness.x_create_any.code.
Local Open Scope logic.

Module HC := WgNoise.harness.x_create_any.code.

Notation W := W_create_any.

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hca5_V : varspecs := QPvarspecs WgNoise.contracts.x_create_any.Harness.qp.

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the hypotheses of the phase lemmas: the primitives' properties and the agreement of the harness's
   expectation with the kernel's model (hca3_model.v) *)
Definition hca5_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec /\
  hca3_init_agree x25519 aead_enc /\ hca3_resp_agree x25519 aead_enc.

Definition hca5_Gprog : funspecs :=
  hca5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W ++ hca3_G.
Definition hca5_Delta : tycontext := func_tycontext HC.f_main hca5_V hca5_Gprog [].

End Defs.

Definition hca5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hca3_post gv)) (@stackframe_of W HC.f_main).

(* ---------------------------------------------------------------------- *)
(* Cutting main's body                                                     *)
(* ---------------------------------------------------------------------- *)

Fixpoint hca5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hca5_seqs l' rest) end.

Fixpoint hca5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hca5_seql l') end.

Fixpoint hca5_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hca5_flat_seq b | _ => [s] end.

Lemma hca5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hca5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hca5_unfold_seqs l rest :
  unfold_Ssequence (hca5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hca5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hca5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hca5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hca5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hca5_seql l) rest)).
  - simpl. rewrite hca5_unfold_seql, hca5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 35 statements below (the last one is `return 0`) *)
Definition hca5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_flat_seq HC.f_main fn_body] in
        (match fn_body HC.f_main with Ssequence s _ => hca5_flat_seq s | s => [s] end) in exact x).

Lemma hca5_stmts_length : length hca5_stmts = 35%nat.
Proof. reflexivity. Qed.

Definition hca5_l (i n: nat) : list statement := firstn n (skipn i hca5_stmts).

Definition hca5_PA := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 0 8)) in exact x).
Definition hca5_PB := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 8 3)) in exact x).
Definition hca5_PC := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 11 4)) in exact x).
Definition hca5_PD := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 15 6)) in exact x).
Definition hca5_PE := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 21 4)) in exact x).
Definition hca5_PF := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 25 1)) in exact x).
Definition hca5_PG := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 26 2)) in exact x).
Definition hca5_PH := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 28 4)) in exact x).
Definition hca5_PI := ltac:(let x := eval cbv beta iota delta [hca5_l hca5_seql firstn skipn hca5_stmts] in (hca5_seql (hca5_l 32 3)) in exact x).

Lemma hca5_body_eq :
  fn_body HC.f_main =
  Ssequence
    (hca5_seqs (hca5_l 0 8) (hca5_seqs (hca5_l 8 3) (hca5_seqs (hca5_l 11 4) (hca5_seqs (hca5_l 15 6)
      (hca5_seqs (hca5_l 21 4) (hca5_seqs (hca5_l 25 1) (hca5_seqs (hca5_l 26 2) (hca5_seqs (hca5_l 28 4)
        (hca5_seql (hca5_l 32 3))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hca5_phases_eq :
  hca5_PA = hca5_seql (hca5_l 0 8) /\ hca5_PB = hca5_seql (hca5_l 8 3) /\
  hca5_PC = hca5_seql (hca5_l 11 4) /\ hca5_PD = hca5_seql (hca5_l 15 6) /\
  hca5_PE = hca5_seql (hca5_l 21 4) /\ hca5_PF = hca5_seql (hca5_l 25 1) /\
  hca5_PG = hca5_seql (hca5_l 26 2) /\ hca5_PH = hca5_seql (hca5_l 28 4) /\
  hca5_PI = hca5_seql (hca5_l 32 3).
Proof. repeat split. Qed.

(* F = if (op == 0) F0 else F1 *)
Definition hca5_Fcond : expr :=
  ltac:(let x := eval cbv beta iota delta [hca5_PF] in
        (match hca5_PF with Sifthenelse c _ _ => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hca5_F0 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_PF] in
        (match hca5_PF with Sifthenelse _ a _ => a | _ => Sskip end) in exact x).
Definition hca5_F1 : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_PF] in
        (match hca5_PF with Sifthenelse _ _ b => b | _ => Sskip end) in exact x).

Lemma hca5_PF_eq : hca5_PF = Sifthenelse hca5_Fcond hca5_F0 hca5_F1.
Proof. reflexivity. Qed.

Lemma hca5_Fcond_eq :
  hca5_Fcond = Ebinop Oeq (Etempvar HC._op tint) (Econst_int (Int.repr 0) tint) tint.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 26 local variables *)
Record hca5_loc := mkLoc5 {
  l_wa: val; l_ita: val; l_pta: val; l_p: val; l_ia: val; l_s: val; l_x: val; l_st: val;
  l_ps: val; l_ds: val; l_ss: val;
  l_raw: val; l_pub: val; l_psk: val; l_key: val; l_dh: val; l_eph: val; l_E: val; l_ts: val;
  l_nothing: val; l_before: val; l_exp: val; l_img: val; l_before1: val; l_exp1: val; l_img1: val }.

Definition hca5_lvars (gv: globals) (L: hca5_loc) : list localdef :=
  [lvar HC._wa (Tstruct HC._wg_device noattr) (l_wa L);
   lvar HC._ita (Tstruct HC._index_hashtable noattr) (l_ita L);
   lvar HC._pta (Tstruct HC._pubkey_hashtable noattr) (l_pta L);
   lvar HC._p (Tstruct HC._wg_peer noattr) (l_p L);
   lvar HC._ia (Tstruct HC._m_identity noattr) (l_ia L);
   lvar HC._s (Tstruct HC._hs_snap noattr) (l_s L);
   lvar HC._x (Tstruct HC._hs_snap noattr) (l_x L);
   lvar HC._st (Tstruct HC._m_state noattr) (l_st L);
   lvar HC._ps (Tstruct HC._pr_snap noattr) (l_ps L);
   lvar HC._ds (Tstruct HC._dev_snap noattr) (l_ds L);
   lvar HC._ss (Tstruct HC._shim_snap noattr) (l_ss L);
   lvar HC._raw (tarray tuchar 32) (l_raw L); lvar HC._pub (tarray tuchar 32) (l_pub L);
   lvar HC._psk (tarray tuchar 32) (l_psk L); lvar HC._key (tarray tuchar 32) (l_key L);
   lvar HC._dh (tarray tuchar 32) (l_dh L); lvar HC._eph (tarray tuchar 32) (l_eph L);
   lvar HC._E (tarray tuchar 32) (l_E L); lvar HC._ts (tarray tuchar 12) (l_ts L);
   lvar HC._nothing (tarray tuchar 1) (l_nothing L);
   lvar HC._before (tarray tuchar 148) (l_before L); lvar HC._exp (tarray tuchar 148) (l_exp L);
   lvar HC._img (tarray tuchar 148) (l_img L);
   lvar HC._before__1 (tarray tuchar 92) (l_before1 L); lvar HC._exp__1 (tarray tuchar 92) (l_exp1 L);
   lvar HC._img__1 (tarray tuchar 92) (l_img1 L);
   gvars gv].

(* the harness's constants (common.h's M_BASEPOINT, M_CONSTRUCTION, M_IDENTIFIER, renamed in this unit) *)
Definition hca5_consts (gv: globals) : mpred :=
  hc_const gv HC._x_create_any__M_BASEPOINT basepoint9 *
  hc_const gv HC._x_create_any__M_CONSTRUCTION construction_bytes *
  hc_const gv HC._x_create_any__M_IDENTIFIER identifier_bytes.

(* the globals of a state after A: allocator, shim (exact warnings w), noise.c's globals after wg_noise_init
   (no keypair is ever created: keypair_counter stays 0), the read-only tables, the harness's constants *)
Definition hca5_globs (gv: globals) (S: shim) (w: list int64) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S w; noise_globals gv Int64.zero; wg_consts gv; hca5_consts gv; FR].

(* the scratch locals, any contents (st, key, dh, eph, E, ts, nothing and the six message images) *)
Definition hca5_scr (L: hca5_loc) : list mpred :=
  [@data_at_ HCS Tsh t_mstate (l_st L);
   hout Tsh 32 (l_key L); hout Tsh 32 (l_dh L); hout Tsh 32 (l_eph L); hout Tsh 32 (l_E L);
   hout Tsh 12 (l_ts L); hout Tsh 1 (l_nothing L);
   hout Tsh 148 (l_before L); hout Tsh 148 (l_exp L); hout Tsh 148 (l_img L);
   hout Tsh 92 (l_before1 L); hout Tsh 92 (l_exp1 L); hout Tsh 92 (l_img1 L)].

(* raw, pub, psk once the peer is set up (B), any contents *)
Definition hca5_scr0 (L: hca5_loc) : list mpred :=
  [hout Tsh 32 (l_raw L); hout Tsh 32 (l_pub L); hout Tsh 32 (l_psk L)].

(* the three snapshots before D, any contents *)
Definition hca5_snap0 (L: hca5_loc) : list mpred :=
  [@data_at_ CKS Tsh t_prsnap (l_ps L); @data_at_ CKS Tsh t_devsnap (l_ds L);
   @data_at_ CKS Tsh t_shimsnap (l_ss L)].

(* a malloc'd object (the token at the world) *)
Definition hca5_tok (t: type) (p: val) : mpred := @malloc_token W Ews t p.

(* ---------------------------------------------------------------------- *)
(* The index table                                                         *)
(* ---------------------------------------------------------------------- *)

(* a kent's keypair entry in the pool, as kents_add inserted it (owner p) *)
Definition hca5_kpool (p: val) (d: kdraw) : val * share * entry :=
  (kd_addr d, Ews, mkEntry p IDX_KEYPAIR (kd_idx d)).

(* the pool of T: the kents' entries (KD order, every one hashed), then p's handshake entry *)
Definition hca5_pool (p: val) (KD: list kdraw) (T: tstate) : Prop :=
  (exists E, t_D T = map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)] /\
             e_peer E = p /\ e_type E = IDX_HANDSHAKE) /\
  NoDup (hs_addr p :: map kd_addr KD) /\
  incl (map kd_addr KD) (t_L T).

(* the kents after kents_snap(kes) in the table T *)
Definition hca5_kents (T: tstate) (KD: list kdraw) : list kent4 := map (kent_snapped T) (map kd_kent KD).

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws, and the objects they determine              *)
(* ---------------------------------------------------------------------- *)

Record hca5_run := mkRun5 {
  r_raw: list byte;     (* raw: the device's static private key *)
  r_sec: list byte;     (* the cookie secret drawn by setup_device *)
  r_boot: int64 }.      (* the boot clock *)

Definition hca5_run_ok (R: hca5_run) : Prop :=
  Zlength (r_raw R) = 32 /\ Zlength (r_sec R) = 32 /\ 0 <= Int64.unsigned (r_boot R) < 2 ^ 62.

(* the counters of the shim that no call of main after D changes (shim_same compares them, and the warnings) *)
Definition hca5_cnt (S: shim) : int64 * int64 * int64 * int64 :=
  (s_allocs S, s_fails S, s_frees S, s_released S).

Section Run.
Variable x25519: list byte -> list byte -> list byte.

(* the harness's model identity (ia) *)
Definition hca5_I (R: hca5_run) : mident := mident_of x25519 (r_raw R).

(* the device after setup_device *)
Definition hca5_D (R: hca5_run) (L: hca5_loc) : device :=
  setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) (r_raw R) (r_sec R) (r_boot R).

(* the peer p: of device wa, its handshake with wa's static identity, field lengths, not in a public-key chain
   after it, its keypair slots NULL or kents (ks) *)
Definition hca5_pok (L: hca5_loc) (P: peer) (ks: list val) : Prop :=
  p_device P = l_wa L /\ hs_sid (p_hs P) = id_addr (l_wa L) /\ hs_ok (p_hs P) /\ p_pknext P = nullval /\
  Forall (fun v => v = nullval \/ In v ks) [p_cur P; p_prev P; p_next P].

(* the objects that live from the setup to the end: the device, the public-key table (head = p), ia *)
Definition hca5_world (R: hca5_run) (L: hca5_loc) : list mpred :=
  [device_rep Tsh (l_wa L) (hca5_D R L); ptable Tsh (l_pta L) (l_p L);
   @data_at HCS Tsh t_mident (mident_val (hca5_I R)) (l_ia L)].

(* what D created and only G .. I read: the kents KD snapshotted in the table T, the snapshots of the peer P, the
   device and the shim S0 (with the warnings w) *)
Definition hca5_rest (L: hca5_loc) (R: hca5_run) (P: peer) (T: tstate) (KD: list kdraw) (S0: shim)
  (w: list int64) : mpred :=
  kents_rep W (kents_head KD) (hca5_kents T KD) *
  @data_at CKS Tsh t_prsnap (prsnap_val P) (l_ps L) *
  @data_at CKS Tsh t_devsnap (devsnap_val (hca5_D R L) (l_p L)) (l_ds L) *
  @data_at CKS Tsh t_shimsnap (shimsnap_val S0 w) (l_ss L).

End Run.

(* the effect of the op branch on the table and the shim: at success (b) the handshake's entry a is
   reinserted with the fresh index idx = wg_shim_random_u32; else the table is unchanged *)
Definition hca5_res_ok (b: bool) (a: val) (T: tstate) (idx: int) (T': tstate) (S': shim) : Prop :=
  if b then T' = t_insert T a idx /\ t_fresh T a idx /\ s_u32 S' = idx else T' = T.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* after the prologue: the stack frame converted, the initial globals (w: the initial warnings) *)
Definition hca5_S0 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX S: shim,
  PROPx []
  (LOCALx (hca5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wa L); @data_at_ Noise.CS Tsh t_itab (l_ita L);
          @data_at_ Noise.CS Tsh t_ptab (l_pta L); @data_at_ Noise.CS Tsh t_peer (l_p L);
          @data_at_ HCS Tsh t_mident (l_ia L);
          @data_at_ HCS Tsh t_hsnap (l_s L); @data_at_ HCS Tsh t_hsnap (l_x L);
          mem_mgr gv; shim_state4 gv S w; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hca5_consts gv; FR] ++ hca5_snap0 L ++ hca5_scr0 L ++ hca5_scr L))).

(* after A: the device set up from raw, ia = m_identity_of(raw), pub / psk drawn, use_psk in {0, 1} *)
Definition hca5_SA (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX R: hca5_run, EX S: shim, EX PUB: list byte, EX PSK: list byte, EX u: Z,
  PROPx [hca5_run_ok R; Zlength PUB = 32; Zlength PSK = 32; 0 <= u <= 1]
  (LOCALx ([temp HC._use_psk (Vint (Int.repr u))] ++ hca5_lvars gv L)
  (SEPx ([device_rep Tsh (l_wa L) (hca5_D x25519 R L); itable Tsh (l_ita L) (mkT [] []);
          ptable Tsh (l_pta L) nullval;
          @data_at HCS Tsh t_mident (mident_val (hca5_I x25519 R)) (l_ia L);
          @data_at_ Noise.CS Tsh t_peer (l_p L);
          @data_at_ HCS Tsh t_hsnap (l_s L); @data_at_ HCS Tsh t_hsnap (l_x L);
          hbytes Tsh (r_raw R) (l_raw L); hbytes Tsh PUB (l_pub L); hbytes Tsh PSK (l_psk L)] ++
         hca5_globs gv S w FR ++ hca5_snap0 L ++ hca5_scr L))).

(* after B (and after C: the same invariant): p set up (after C: randomized, any reference count, maybe hashed),
   its handshake entry the only entry of the table's pool, its keypair slots NULL *)
Definition hca5_SB (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX R: hca5_run, EX S: shim, EX P: peer, EX T: tstate,
  PROPx [hca5_run_ok R; hca5_pok L P []; hca5_pool (l_p L) [] T]
  (LOCALx (hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T; peer_rep Tsh (l_p L) P;
          @data_at_ HCS Tsh t_hsnap (l_s L); @data_at_ HCS Tsh t_hsnap (l_x L)] ++
         hca5_globs gv S w FR ++ hca5_snap0 L ++ hca5_scr0 L ++ hca5_scr L))).

(* after D: the kents KD, each hashed in the table T and snapshotted there; ps / ds / ss the snapshots of P, the
   device and the shim S; refs0 = P's reference count *)
Definition hca5_SK (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX R: hca5_run, EX S: shim, EX P: peer, EX T: tstate, EX KD: list kdraw,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KD); hca5_pool (l_p L) KD T]
  (LOCALx ([temp HC._kes (kents_head KD); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T; peer_rep Tsh (l_p L) P; hca5_rest x25519 L R P T KD S w;
          @data_at_ HCS Tsh t_hsnap (l_s L); @data_at_ HCS Tsh t_hsnap (l_x L)] ++
         hca5_globs gv S w FR ++ hca5_scr0 L ++ hca5_scr L))).

(* after E with op = o: s = x = the snapshot of p's handshake (entry E of the pool), ok = 0 *)
Definition hca5_SEo (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (o: Z) : environ -> mpred :=
  EX R: hca5_run, EX S: shim, EX P: peer, EX T: tstate, EX KD: list kdraw, EX E: entry,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KD); hca5_pool (l_p L) KD T;
         t_entry T (hs_addr (l_p L)) = Some E]
  (LOCALx ([temp HC._op (Vint (Int.repr o)); temp HC._ok (Vint Int.zero); temp HC._kes (kents_head KD);
            temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T; peer_rep Tsh (l_p L) P; hca5_rest x25519 L R P T KD S w;
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L);
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_x L)] ++
         hca5_globs gv S w FR ++ hca5_scr0 L ++ hca5_scr L))).

Definition hca5_SE (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX o: Z, !! (0 <= o <= 1) && hca5_SEo gv L FR w o.

(* after F (both branches, the message freed): ok = b, p's handshake is H', x = the snapshot taken before the call
   with the handshake fields H' (the harness's expectation, = the kernel's result); the table T' and the shim S'
   as hca5_res_ok says; S' keeps the counters of the snapshot shim S0 *)
Definition hca5_SF (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX R: hca5_run, EX P: peer, EX T: tstate, EX KD: list kdraw, EX E: entry,
  EX b: bool, EX H': handshake, EX idx: int, EX T': tstate, EX S': shim, EX S0: shim,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KD); hca5_pool (l_p L) KD T;
         t_entry T (hs_addr (l_p L)) = Some E;
         hs_sid H' = id_addr (l_wa L); hs_ok H'; hca5_res_ok b (hs_addr (l_p L)) T idx T' S';
         hca5_cnt S' = hca5_cnt S0]
  (LOCALx ([temp HC._ok (Vint (if b then Int.one else Int.zero)); temp HC._kes (kents_head KD);
            temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T'; peer_rep Tsh (l_p L) (p_set_hs P H'); hca5_rest x25519 L R P T KD S0 w;
          @data_at_ HCS Tsh t_hsnap (l_s L);
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E H')) (l_x L)] ++
         hca5_globs gv S' w FR ++ hca5_scr0 L ++ hca5_scr L))).

(* after G (and after H: the same invariant): the handshake checked; the current table T' is the snapshot table T or
   T with p's handshake entry reinserted *)
Definition hca5_SG (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) : environ -> mpred :=
  EX R: hca5_run, EX P: peer, EX T: tstate, EX KD: list kdraw,
  EX H': handshake, EX T': tstate, EX S': shim, EX S0: shim,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KD); hca5_pool (l_p L) KD T;
         hs_sid H' = id_addr (l_wa L); hs_ok H';
         T' = T \/ (exists idx, T' = t_insert T (hs_addr (l_p L)) idx);
         hca5_cnt S' = hca5_cnt S0]
  (LOCALx ([temp HC._kes (kents_head KD); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T'; peer_rep Tsh (l_p L) (p_set_hs P H'); hca5_rest x25519 L R P T KD S0 w;
          @data_at_ HCS Tsh t_hsnap (l_s L); @data_at_ HCS Tsh t_hsnap (l_x L)] ++
         hca5_globs gv S' w FR ++ hca5_scr0 L ++ hca5_scr L))).

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hca5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hca3_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
