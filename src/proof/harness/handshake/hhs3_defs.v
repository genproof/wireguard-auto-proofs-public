(* law handshake (harness/handshake.c): main's body cut into six phases, and the states between them.

   Conventions of the states (all phases):
   - main runs in the world compspecs W_handshake (Delta hhs3_Delta).  The SEP items are kept in the
     compspecs of the specifications that consume them: the protocol objects through prot_repr3's predicates
     (device_rep, peer_rep, itable, ptable, init_rep, resp_rep: Noise.CS inside), the harness structs as
     `@data_at HCS` / `@data_at_ HCS`, the kernel structs not yet set up as `@data_at_ Noise.CS`, byte
     buffers as hbytes / hout (HCS).  The prologue (hhs3_P0) has converted the stack frame (W) to these forms.
   - hhs3_run R: the setup's draws (raw keys, psk, cookie secrets, boot clock).  Locals: the record L.
   - phases P1..P6 = statements 0-36, 37-65, 66-76, 77-100, 101-110, 111-120 of main's body (S1; return 0);
     each phase may return early (free(m1); free(m2); return 0): that is the return part of hhs3_R.
   - states hhs3_S1 .. hhs3_S5 (after P1 .. P5); P6 ends in FF (it returns).
   - FR: an opaque frame (TT * has_ext), carried along. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require WgNoise.contracts.x_handshake.
Require WgNoise.harness.x_handshake.code.
Local Open Scope logic.

Module HC := WgNoise.harness.x_handshake.code.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas                                      *)
(* ---------------------------------------------------------------------- *)

(* the statement of prot_rep_lemmas3 (unproved in the base: a hypothesis here, discharged by the
   assembly; the checker rejects any dependency on an unproved lemma) *)
Section Rep.
#[local] Existing Instance Noise.CS.
Definition hhs3_rep : Prop :=
  (forall sh m M, init_rep sh m M |-- bytes_at sh (init_bytes M) m) /\
  (forall sh m M, field_compatible t_init [] m -> im_ok M ->
     bytes_at sh (init_bytes M) m |-- init_rep sh m M) /\
  (forall sh m M, resp_rep sh m M |-- bytes_at sh (resp_bytes M) m) /\
  (forall sh m M, field_compatible t_resp [] m -> rm_ok M ->
     bytes_at sh (resp_bytes M) m |-- resp_rep sh m M) /\
  (forall sht tab T a sh E, writable_share sh ->
     itable sht tab T * entry_out sh a E |-- itable sht tab (t_add T a sh E)) /\
  (forall sht tab T a sh E, sfind (t_D T) a = Some (sh, E) -> ~ In a (t_L T) ->
     itable sht tab T |-- itable sht tab (t_free T a) * entry_out sh a E) /\
  (forall sh p P E n h, peer_rep sh p P * entry_at sh (hs_addr p) E n h |-- @data_at_ Noise.CS sh t_peer p) /\
  (forall CSw k K E n h, keypair_rep CSw k K * entry_at Ews k E n h |--
     @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
     @data_at_ Noise.CS Ews (tarray tuchar SIZEOF_KEYPAIR) k).
End Rep.

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hhs3_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec /\
  hhs3_comm x25519 /\ hhs3_rep.

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hhs3_Gprog : funspecs :=
  hhs3_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_handshake ++ hhs3_G.
Definition hhs3_Delta : tycontext := func_tycontext HC.f_main hhs3_V hhs3_Gprog [].

Definition hhs3_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hhs3_post gv)) (@stackframe_of W_handshake HC.f_main).

End Defs.

(* ---------------------------------------------------------------------- *)
(* Cutting main's body                                                     *)
(* ---------------------------------------------------------------------- *)

Fixpoint hhs3_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hhs3_seqs l' rest) end.

Fixpoint hhs3_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hhs3_seql l') end.

Fixpoint hhs3_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: hhs3_flat_seq b | _ => [s] end.

Lemma hhs3_unfold_seql l : l <> [] ->
  unfold_Ssequence (hhs3_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hhs3_unfold_seqs l rest :
  unfold_Ssequence (hhs3_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hhs3_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hhs3_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hhs3_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hhs3_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hhs3_seql l) rest)).
  - simpl. rewrite hhs3_unfold_seql, hhs3_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 121 statements below (the last one is `return 0`) *)
Definition hhs3_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hhs3_flat_seq HC.f_main fn_body] in
        (match fn_body HC.f_main with Ssequence s _ => hhs3_flat_seq s | s => [s] end) in exact x).

Lemma hhs3_stmts_length : length hhs3_stmts = 121%nat.
Proof. reflexivity. Qed.

Definition hhs3_l (i n: nat) : list statement := firstn n (skipn i hhs3_stmts).

(* the phases:
   P1 =   0..36  setup: boot clock, wg_noise_init, raw keys, psk, devices, identities, peers, their CHECKs,
                 the two mallocs (NULL: frees + return), all_ok
   P2 =  37..65  A: fill_init, image, real clock, ts, create_initiation (+ the model, the CHECKs; !ok1:
                 return), add_mac and its CHECKs
   P3 =  66..76  B: consume_initiation, acc1, the CHECKs (accepted: wg_peer_put), completeness 1 (!acc1:
                 return)
   P4 =  77..100 B: fill_resp, create_response (+ model, completeness 2; !ok2: return), CHECKs, add_mac
   P5 = 101..110 A: consume_response, acc2, the CHECKs, completeness 3 (!acc2: return)
   P6 = 111..120 begin_session A and B, keypairs_clear, the final CHECKs, frees, return 0 *)
Definition hhs3_P1 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 0 37)) in exact x).
Definition hhs3_P2 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 37 29)) in exact x).
Definition hhs3_P3 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 66 11)) in exact x).
Definition hhs3_P4 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 77 24)) in exact x).
Definition hhs3_P5 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 101 10)) in exact x).
Definition hhs3_P6 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 111 10)) in exact x).

Lemma hhs3_body_eq :
  fn_body HC.f_main =
  Ssequence
    (hhs3_seqs (hhs3_l 0 37) (hhs3_seqs (hhs3_l 37 29) (hhs3_seqs (hhs3_l 66 11)
      (hhs3_seqs (hhs3_l 77 24) (hhs3_seqs (hhs3_l 101 10) (hhs3_seql (hhs3_l 111 10)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hhs3_phases_eq :
  hhs3_P1 = hhs3_seql (hhs3_l 0 37) /\ hhs3_P2 = hhs3_seql (hhs3_l 37 29) /\
  hhs3_P3 = hhs3_seql (hhs3_l 66 11) /\ hhs3_P4 = hhs3_seql (hhs3_l 77 24) /\
  hhs3_P5 = hhs3_seql (hhs3_l 101 10) /\ hhs3_P6 = hhs3_seql (hhs3_l 111 10).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 32 local variables *)
Record hhs3_loc := mkLoc {
  l_wa: val; l_wb: val; l_ita: val; l_itb: val; l_pta: val; l_ptb: val; l_pb: val; l_pa: val;
  l_ia: val; l_ib: val; l_rawa: val; l_rawb: val; l_psk: val; l_ssa: val; l_ssb: val; l_tmp: val;
  l_ts: val; l_img: val; l_imgb: val; l_rimg: val; l_rimgb: val; l_mi: val; l_ci: val; l_mr: val;
  l_st2: val; l_snap: val; l_d1: val; l_d2: val; l_d1b: val; l_d2b: val; l_first: val; l_second: val }.

Definition hhs3_lvars (gv: globals) (L: hhs3_loc) : list localdef :=
  [lvar HC._wa t_dev (l_wa L); lvar HC._wb t_dev (l_wb L);
   lvar HC._ita t_itab (l_ita L); lvar HC._itb t_itab (l_itb L);
   lvar HC._pta t_ptab (l_pta L); lvar HC._ptb t_ptab (l_ptb L);
   lvar HC._pb t_peer (l_pb L); lvar HC._pa t_peer (l_pa L);
   lvar HC._ia t_mident (l_ia L); lvar HC._ib t_mident (l_ib L);
   lvar HC._raw_a (tarray tuchar 32) (l_rawa L); lvar HC._raw_b (tarray tuchar 32) (l_rawb L);
   lvar HC._psk (tarray tuchar 32) (l_psk L); lvar HC._ssa (tarray tuchar 32) (l_ssa L);
   lvar HC._ssb (tarray tuchar 32) (l_ssb L); lvar HC._tmp (tarray tuchar 32) (l_tmp L);
   lvar HC._ts (tarray tuchar 12) (l_ts L);
   lvar HC._img (tarray tuchar 148) (l_img L); lvar HC._img_before (tarray tuchar 148) (l_imgb L);
   lvar HC._rimg (tarray tuchar 92) (l_rimg L); lvar HC._rimg_before (tarray tuchar 92) (l_rimgb L);
   lvar HC._mi t_minit (l_mi L); lvar HC._ci t_mcinit (l_ci L); lvar HC._mr t_mresp (l_mr L);
   lvar HC._st2 t_mstate (l_st2 L); lvar HC._snap t_hsnap (l_snap L);
   lvar HC._d1 (tarray tuchar 32) (l_d1 L); lvar HC._d2 (tarray tuchar 32) (l_d2 L);
   lvar HC._d1__1 (tarray tuchar 32) (l_d1b L); lvar HC._d2__1 (tarray tuchar 32) (l_d2b L);
   lvar HC._first (tarray tuchar 32) (l_first L); lvar HC._second (tarray tuchar 32) (l_second L);
   gvars gv].

(* the harness's constants (common.h, renamed in this unit) *)
Definition hhs3_consts (gv: globals) : mpred :=
  hc_const gv HC._x_handshake__M_BASEPOINT basepoint9 *
  hc_const gv HC._x_handshake__M_CONSTRUCTION construction_bytes *
  hc_const gv HC._x_handshake__M_IDENTIFIER identifier_bytes *
  hc_const gv HC._x_handshake__M_LABEL_MAC1 mac1_label *
  hc_const gv HC._x_handshake__M_LABEL_COOKIE cookie_label.

(* the shim's state at the start (all globals zero) *)
Definition hhs3_shim0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

(* the globals of a state: allocator, shim, noise.c's globals (keypair_counter kc), the read-only tables *)
Definition hhs3_globs (gv: globals) (S: shim) (kc: int64) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state gv S; noise_globals gv kc; wg_consts gv; hhs3_consts gv; FR].

(* the scratch locals, any contents *)
Definition hhs3_scr_tmp (L: hhs3_loc) : list mpred :=
  [hout Tsh 32 (l_tmp L); hout Tsh 148 (l_imgb L); hout Tsh 92 (l_rimgb L);
   @data_at_ HCS Tsh t_hsnap (l_snap L);
   hout Tsh 32 (l_d1 L); hout Tsh 32 (l_d2 L); hout Tsh 32 (l_d1b L); hout Tsh 32 (l_d2b L);
   hout Tsh 32 (l_first L); hout Tsh 32 (l_second L)].

(* a malloc'd message (the token at the world, the contents at Noise.CS) *)
Definition hhs3_tok (t: type) (p: val) : mpred := @malloc_token W_handshake Ews t p.

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws, and the objects they determine              *)
(* ---------------------------------------------------------------------- *)

Record hhs3_run := mkRun {
  r_rawa: list byte;    (* raw_a *)
  r_rawb: list byte;    (* raw_b *)
  r_up: bool;           (* use_psk *)
  r_psk: list byte;     (* the psk buffer (zero when not used) *)
  r_seca: list byte;    (* the cookie secret drawn by setup_device(&wa ..) *)
  r_secb: list byte;    (* .. by setup_device(&wb ..) *)
  r_boot0: int64 }.     (* the first boot clock *)

Definition hhs3_run_ok (R: hhs3_run) : Prop :=
  Zlength (r_rawa R) = 32 /\ Zlength (r_rawb R) = 32 /\ Zlength (r_psk R) = 32 /\
  (r_up R = false -> r_psk R = zeros32) /\ Zlength (r_seca R) = 32 /\ Zlength (r_secb R) = 32 /\
  0 <= Int64.unsigned (r_boot0 R) < 2 ^ 62.

Section Run.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the harness's model identities *)
Definition hhs3_IA (R: hhs3_run) : mident := mident_of x25519 (r_rawa R).
Definition hhs3_IB (R: hhs3_run) : mident := mident_of x25519 (r_rawb R).

(* the devices after setup_device *)
Definition hhs3_DA (R: hhs3_run) (L: hhs3_loc) : device :=
  setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) (r_rawa R) (r_seca R) (r_boot0 R).
Definition hhs3_DB (R: hhs3_run) (L: hhs3_loc) : device :=
  setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) (r_rawb R) (r_secb R) (r_boot0 R).

(* the peers after setup_peer: pb = A's peer for B (id 1), pa = B's peer for A (id 2) *)
Definition hhs3_PB0 (R: hhs3_run) (L: hhs3_loc) : peer :=
  setup_peer_val x25519 (hhs3_DA R L) (l_wa L) (l_pb L) nullval (mi_pub (hhs3_IB R)) (r_psk R) (Int64.repr 1).
Definition hhs3_PA0 (R: hhs3_run) (L: hhs3_loc) : peer :=
  setup_peer_val x25519 (hhs3_DB R L) (l_wb L) (l_pa L) nullval (mi_pub (hhs3_IA R)) (r_psk R) (Int64.repr 2).

(* the handshake entries (in the tables' pools) and the tables after setup *)
Definition hhs3_EB (L: hhs3_loc) : entry := mkEntry (l_pb L) IDX_HANDSHAKE Int.zero.
Definition hhs3_EA (L: hhs3_loc) : entry := mkEntry (l_pa L) IDX_HANDSHAKE Int.zero.
Definition hhs3_TA0 (L: hhs3_loc) : tstate := mkT [(hs_addr (l_pb L), Tsh, hhs3_EB L)] [].
Definition hhs3_TB0 (L: hhs3_loc) : tstate := mkT [(hs_addr (l_pa L), Tsh, hhs3_EA L)] [].

(* the precomputed static-static values of the harness (ssa, ssb) *)
Definition hhs3_ssa (R: hhs3_run) : list byte := m_precomputed_model x25519 (hhs3_IA R) (mi_pub (hhs3_IB R)).
Definition hhs3_ssb (R: hhs3_run) : list byte := m_precomputed_model x25519 (hhs3_IB R) (mi_pub (hhs3_IA R)).

(* the objects and buffers that live from the setup to the end: devices, tables, identities, raw keys, psk,
   ssa / ssb, the two messages (m1, m2: their contents are given separately) *)
Definition hhs3_setup_sep (R: hhs3_run) (L: hhs3_loc) : list mpred :=
  [device_rep Tsh (l_wa L) (hhs3_DA R L); device_rep Tsh (l_wb L) (hhs3_DB R L);
   ptable Tsh (l_pta L) (l_pb L); ptable Tsh (l_ptb L) (l_pa L);
   @data_at HCS Tsh t_mident (mident_val (hhs3_IA R)) (l_ia L);
   @data_at HCS Tsh t_mident (mident_val (hhs3_IB R)) (l_ib L);
   hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L); hbytes Tsh (r_psk R) (l_psk L);
   hbytes Tsh (hhs3_ssa R) (l_ssa L); hbytes Tsh (hhs3_ssb R) (l_ssb L)].

(* the all_ok flag after P1 *)
Definition hhs3_ok1 (R: hhs3_run) : bool := mi_ok (hhs3_IA R) && mi_ok (hhs3_IB R).

(* ---------------------------------------------------------------------- *)
(* P2: A's initiation                                                      *)
(* ---------------------------------------------------------------------- *)

(* the inputs of P2: the filled message M0 (fill_init), the real clock (sec, nsec), the ephemeral bytes r1
   and the index idx1 the table drew *)
Record hhs3_ini := mkIni { i_M0: init_msg; i_sec: int64; i_nsec: Z; i_r: list byte; i_idx: int }.

Definition hhs3_ts (I: hhs3_ini) : list byte := tai64n (i_sec I) (Int64.repr (i_nsec I)).

(* the kernel's create_initiation: its result (true at this point), message and handshake *)
Definition hhs3_ci (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini) : bool * init_msg * handshake :=
  create_initiation_model x25519 aead_enc (d_id (hhs3_DA R L)) (p_hs (hhs3_PB0 R L)) (i_M0 I) (i_r I)
    (hhs3_ts I) (i_idx I).

(* the harness's model of the initiation (m_create_initiation) *)
Definition hhs3_mi (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini)
  : option (list byte * list byte * list byte * list byte * list byte * list byte) :=
  m_create_initiation_model x25519 aead_enc (id_pub (d_id (hhs3_DA R L))) (mi_pub (hhs3_IB R)) (hhs3_ssa R)
    (i_r I) (hhs3_ts I).

(* a message with its macs replaced *)
Definition im_set_macs (M: init_msg) (m1 m2: list byte) : init_msg :=
  mkIM (im_type M) (im_sender M) (im_eph M) (im_encs M) (im_enct M) m1 m2.
Definition rm_set_macs (M: resp_msg) (m1 m2: list byte) : resp_msg :=
  mkRM (rm_type M) (rm_sender M) (rm_receiver M) (rm_eph M) (rm_encn M) m1 m2.

(* a peer's cookie after add_mac with no valid cookie: the mac1 remembered *)
Definition ck_sent_mac1 (C: cookie) (m1: list byte) : cookie :=
  mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) true m1 (ck_dkey C) (ck_mkey C).

(* the facts of P2's result (the CHECKs proved): the kernel succeeded with message M1 / handshake H1, the
   harness model with mi = MI, m1 holds M1 with mac1 = MAC(HASH("mac1----" || B's public), M1[0..116)) and
   mac2 = 0, pb's cookie remembers mac1 *)
Definition hhs3_after_init (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) : Prop :=
  mi_ok (hhs3_IA R) = true /\ hhs3_ci R L I = (true, M1, H1) /\ hhs3_mi R L I = Some MI /\
  t_fresh (hhs3_TA0 L) (hs_addr (l_pb L)) (i_idx I) /\ im_ok (i_M0 I) /\ Zlength (i_r I) = 32 /\
  0 <= i_nsec I < 1000000000.

Definition hhs3_mac1A (R: hhs3_run) (M1: init_msg) : list byte :=
  mac1_of (label_key mac1_label (mi_pub (hhs3_IB R))) (init_bytes M1).
Definition hhs3_M1m (R: hhs3_run) (M1: init_msg) : init_msg :=
  im_set_macs M1 (hhs3_mac1A R M1) (zeros 16).
Definition hhs3_PB1 (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (H1: handshake) : peer :=
  p_set_cookie (p_set_hs (hhs3_PB0 R L) H1) (ck_sent_mac1 (p_cookie (hhs3_PB0 R L)) (hhs3_mac1A R M1)).
Definition hhs3_TA1 (L: hhs3_loc) (I: hhs3_ini) : tstate := t_insert (hhs3_TA0 L) (hs_addr (l_pb L)) (i_idx I).

(* all_ok after P2 *)
Definition hhs3_ok2 (R: hhs3_run) (I: hhs3_ini) : bool := mi_ok (hhs3_IB R) && negb (is_zero (hhs3_ts I)).

(* ---------------------------------------------------------------------- *)
(* P3: B consumes the initiation                                           *)
(* ---------------------------------------------------------------------- *)

(* the kernel's consume_initiation at boot time now_b (S's boot clock = now_b) *)
Definition hhs3_cin (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (nowb: int64) : option (val * peer) :=
  consume_initiation_model x25519 aead_dec (d_id (hhs3_DB R L)) [(l_pa L, Tsh, hhs3_PA0 R L)]
    (hhs3_M1m R M1) nowb.

(* the harness's stages: ci = (ck2, h2, key, spub, ts) *)
Definition hhs3_cs1 (R: hhs3_run) (M1: init_msg) : option (list byte * list byte * list byte * list byte) :=
  m_consume_init1_model x25519 aead_dec (hhs3_IB R) (im_eph M1) (im_encs M1).

(* the facts of P3's result: B accepted (peer pa, new state PA1 with 2 references; the harness dropped
   one), its stages (CI1 = stage 1, CI2 = stage 2) *)
Definition hhs3_after_cin (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (nowb: int64) (PA1: peer)
  (CI1: list byte * list byte * list byte * list byte) (CI2: list byte * list byte * list byte) : Prop :=
  hhs3_cin R L M1 nowb = Some (l_pa L, PA1) /\ hhs3_cs1 R M1 = Some CI1 /\
  (let '(_, _, ck, h) := CI1 in
   m_consume_init2_model aead_dec (hhs3_ssb R) ck h (im_enct M1) = Some CI2) /\
  0 <= Int64.unsigned nowb < 2 ^ 62.

(* all_ok after P3: the completeness flag of the first half *)
Definition hhs3_ok3 (R: hhs3_run) (I: hhs3_ini) (nowb: int64)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) : bool :=
  let '(E, _, _, ep, _, _) := MI in
  hhs3_ok2 R I && negb (Int64.ltu nowb (Int64.repr 20000000)) &&
  dh_ok x25519 ep (mi_pub (hhs3_IB R)) && dh_ok x25519 (mi_priv (hhs3_IB R)) E &&
  bytes_eqb (x25519 ep (mi_pub (hhs3_IB R))) (x25519 (mi_priv (hhs3_IB R)) E) &&
  negb (is_zero (hhs3_ssa R)) && bytes_eqb (hhs3_ssa R) (hhs3_ssb R).

(* ---------------------------------------------------------------------- *)
(* P4: B's response                                                        *)
(* ---------------------------------------------------------------------- *)

(* the inputs of P4: the filled response M0, the ephemeral bytes and the index *)
Record hhs3_rsp := mkRsp { s_M0: resp_msg; s_r: list byte; s_idx: int }.

(* pa after P3 (one reference: the harness dropped the returned one) *)
Definition hhs3_PA2 (PA1: peer) : peer := p_set_refs PA1 Int.one.

Definition hhs3_cr (PA1: peer) (Q: hhs3_rsp) : bool * resp_msg * handshake :=
  create_response_model x25519 aead_enc (p_hs (hhs3_PA2 PA1)) (s_M0 Q) (s_r Q) (s_idx Q).

(* the harness's model: m_create_response(&mr, &ci.st, m1's ephemeral, pa's remote static, psk, r) *)
Definition hhs3_mr (R: hhs3_run) (PA1: peer) (M1: init_msg) (CI2: list byte * list byte * list byte)
  (Q: hhs3_rsp) : option (list byte * list byte * list byte * list byte * list byte) :=
  let '(_, ck, h) := CI2 in
  m_create_response_model x25519 aead_enc ck h (im_eph M1) (hs_rstatic (p_hs PA1)) (r_psk R) (s_r Q).

Definition hhs3_after_resp (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (PA1: peer)
  (CI2: list byte * list byte * list byte) (Q: hhs3_rsp) (M2: resp_msg) (H2: handshake)
  (MR: list byte * list byte * list byte * list byte * list byte) : Prop :=
  hhs3_cr PA1 Q = (true, M2, H2) /\ hhs3_mr R PA1 M1 CI2 Q = Some MR /\
  t_fresh (hhs3_TB0 L) (hs_addr (l_pa L)) (s_idx Q) /\ rm_ok (s_M0 Q) /\ Zlength (s_r Q) = 32.

Definition hhs3_mac1B (R: hhs3_run) (M2: resp_msg) : list byte :=
  mac1_of (label_key mac1_label (mi_pub (hhs3_IA R))) (resp_bytes M2).
Definition hhs3_M2m (R: hhs3_run) (M2: resp_msg) : resp_msg := rm_set_macs M2 (hhs3_mac1B R M2) (zeros 16).
Definition hhs3_PA3 (R: hhs3_run) (PA1: peer) (M2: resp_msg) (H2: handshake) : peer :=
  p_set_cookie (p_set_hs (hhs3_PA2 PA1) H2) (ck_sent_mac1 (p_cookie PA1) (hhs3_mac1B R M2)).
Definition hhs3_TB1 (L: hhs3_loc) (Q: hhs3_rsp) : tstate := t_insert (hhs3_TB0 L) (hs_addr (l_pa L)) (s_idx Q).

(* all_ok after P4 *)
Definition hhs3_ok4 (ok3: bool) (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (R: hhs3_run) (MR: list byte * list byte * list byte * list byte * list byte) : bool :=
  let '(Ei, _, _, epi, _, _) := MI in
  let '(Er, _, epr, _, _) := MR in
  ok3 && (dh_ok x25519 epr Ei && dh_ok x25519 epi Er && bytes_eqb (x25519 epr Ei) (x25519 epi Er) &&
          dh_ok x25519 epr (mi_pub (hhs3_IA R)) && dh_ok x25519 (mi_priv (hhs3_IA R)) Er &&
          bytes_eqb (x25519 epr (mi_pub (hhs3_IA R))) (x25519 (mi_priv (hhs3_IA R)) Er) &&
          negb (is_zero Er)).

(* ---------------------------------------------------------------------- *)
(* P5: A consumes the response                                             *)
(* ---------------------------------------------------------------------- *)

Definition hhs3_cre (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (M2: resp_msg) : option (val * peer) :=
  consume_response_model x25519 aead_dec (d_id (hhs3_DA R L)) (hhs3_TA1 L I)
    [(l_pb L, Tsh, hhs3_PB1 R L M1 H1)] (hhs3_M2m R M2).

(* the harness's model: m_consume_response(&st2, &mi.st, mi.eph_priv, ia.priv, psk, ephemeral, enc_nothing) *)
Definition hhs3_mcr (R: hhs3_run) (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (M2: resp_msg) : option (list byte * list byte) :=
  let '(_, _, _, ep, ck, h) := MI in
  m_consume_response_model x25519 aead_dec ck h ep (mi_priv (hhs3_IA R)) (r_psk R) (rm_eph M2) (rm_encn M2).

Definition hhs3_after_cre (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) (M2: resp_msg) (nowa: int64)
  (PB2: peer) (ST2: list byte * list byte) : Prop :=
  hhs3_cre R L I M1 H1 M2 = Some (l_pb L, PB2) /\ hhs3_mcr R MI M2 = Some ST2 /\
  0 <= Int64.unsigned nowa < 2 ^ 62.

End Run.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the shim's counters are those recorded in allocs0 / frees0 / fails0 *)
Definition hhs3_cnt (S: shim) (a f l: int64) : Prop := s_allocs S = a /\ s_frees S = f /\ s_fails S = l.

Definition hhs3_cnt_temps (a f l: int64) : list localdef :=
  [temp HC._allocs0 (Vlong a); temp HC._frees0 (Vlong f); temp HC._fails0 (Vlong l)].

(* after the prologue: the stack frame converted, the initial globals *)
Definition hhs3_S0 (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hhs3_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wa L); @data_at_ Noise.CS Tsh t_dev (l_wb L);
          @data_at_ Noise.CS Tsh t_itab (l_ita L); @data_at_ Noise.CS Tsh t_itab (l_itb L);
          @data_at_ Noise.CS Tsh t_ptab (l_pta L); @data_at_ Noise.CS Tsh t_ptab (l_ptb L);
          @data_at_ Noise.CS Tsh t_peer (l_pb L); @data_at_ Noise.CS Tsh t_peer (l_pa L);
          @data_at_ HCS Tsh t_mident (l_ia L); @data_at_ HCS Tsh t_mident (l_ib L);
          hout Tsh 32 (l_rawa L); hout Tsh 32 (l_rawb L); hout Tsh 32 (l_psk L);
          hout Tsh 32 (l_ssa L); hout Tsh 32 (l_ssb L); hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L);
          hout Tsh 92 (l_rimg L);
          @data_at_ HCS Tsh t_minit (l_mi L); @data_at_ HCS Tsh t_mcinit (l_ci L);
          @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L);
          mem_mgr gv; shim_state gv hhs3_shim0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hhs3_consts gv; FR] ++ hhs3_scr_tmp L))).

(* after P1: setup done, the CHECKs of the setup passed, m1 / m2 allocated (non-NULL, uninitialised).
   all_ok = ia.ok && ib.ok; allocs0 / frees0 / fails0 = the shim's counters (unchanged since) *)
Definition hhs3_S1 (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok1 x25519 R then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_setup_sep x25519 R L ++
         [itable Tsh (l_ita L) (hhs3_TA0 L); itable Tsh (l_itb L) (hhs3_TB0 L);
          peer_rep Tsh (l_pb L) (hhs3_PB0 x25519 R L); peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L);
          hhs3_tok t_init m1; @data_at_ Noise.CS Ews t_init m1;
          hhs3_tok t_resp m2; @data_at_ Noise.CS Ews t_resp m2;
          hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
          @data_at_ HCS Tsh t_minit (l_mi L); @data_at_ HCS Tsh t_mcinit (l_ci L);
          @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
         hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* after P2: A created its initiation (accepted by the model, all CHECKs passed) and added its macs.
   m1 = M1 with the macs; img = its image; ts = the timestamp; mi = the harness model's initiation *)
Definition hhs3_S2 (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok2 x25519 R I then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_setup_sep x25519 R L ++
         [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB0 L);
          peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1); peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L);
          hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
          hhs3_tok t_resp m2; @data_at_ Noise.CS Ews t_resp m2;
          hbytes Tsh (hhs3_ts I) (l_ts L); hbytes Tsh (init_bytes (hhs3_M1m x25519 R M1)) (l_img L);
          hout Tsh 92 (l_rimg L);
          (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
          @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_mresp (l_mr L);
          @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
         hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* after P3: B accepted (pa's new state, its reference dropped again), ci = the harness's stages *)
Definition hhs3_S3 (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok3 x25519 R I nowb MI then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_setup_sep x25519 R L ++
         [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB0 L);
          peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1); peer_rep Tsh (l_pa L) (hhs3_PA2 PA1);
          hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
          hhs3_tok t_resp m2; @data_at_ Noise.CS Ews t_resp m2;
          hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
          (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
          (let '(s, _, ck1, _) := CI1 in let '(t, ck, h) := CI2 in
           @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes (kdf2 ck1 (hhs3_ssb x25519 R))) (bytes s) (bytes t))
             (l_ci L));
          @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
         hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* after P4: B created its response (model accepted, CHECKs passed) and added its macs; rimg = its image *)
Definition hhs3_S4 (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX M2: resp_msg, EX H2: handshake, EX MR: list byte * list byte * list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_setup_sep x25519 R L ++
         [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB1 L Q);
          peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1); peer_rep Tsh (l_pa L) (hhs3_PA3 x25519 R PA1 M2 H2);
          hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
          hhs3_tok t_resp m2; resp_rep Ews m2 (hhs3_M2m x25519 R M2);
          hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hbytes Tsh (resp_bytes (hhs3_M2m x25519 R M2)) (l_rimg L);
          (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
          @data_at_ HCS Tsh t_mcinit (l_ci L);
          (let '(E, encn, ep, ck, h) := MR in @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L));
          @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
         hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* after P5: A accepted the response (pb's new state, its reference dropped again); st2 = the model's *)
Definition hhs3_S5 (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX M2: resp_msg, EX H2: handshake, EX MR: list byte * list byte * list byte * list byte * list byte,
  EX nowa: int64, EX PB2: peer, EX ST2: list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         hhs3_after_cre x25519 aead_dec R L I M1 H1 MI M2 nowa PB2 ST2; s_boot S = nowa]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_a (Vlong nowa);
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_setup_sep x25519 R L ++
         [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB1 L Q);
          peer_rep Tsh (l_pb L) (p_set_refs PB2 Int.one);
          peer_rep Tsh (l_pa L) (hhs3_PA3 x25519 R PA1 M2 H2);
          hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
          hhs3_tok t_resp m2; resp_rep Ews m2 (hhs3_M2m x25519 R M2);
          hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
          (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
          @data_at_ HCS Tsh t_mcinit (l_ci L);
          (let '(E, encn, ep, ck, h) := MR in @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L));
          (let '(ck, h) := ST2 in @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st2 L))] ++
         hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hhs3_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hhs3_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
