(* main is proved against a SMALL context (its callees' specifications exactly as they appear in
   hrp3_imports ++ hrp3_G, list hrp3_G0) and lifted to the unit's context afterwards (hrp3_lift.v).
   The body is cut into segments:
     A  = statements 0..14  of main: draws, wg_noise_init, the two devices, identities, peers, m_precomputed
     B  = statements 15..22: the three mallocs (NULL: frees + return 0), latest = 0, last = 0, now, steps
     (statement 23: for (i = 0; i < steps; i++) BODY: glue in hrp3_main.v)
       L1  = BODY 1..2: kind = nondet_u8() % 3, the message (fill_init + create_initiation + add_mac + copy to sent
             / copy of sent / copy of accepted), with `continue`s
       L2a = BODY 3..6: B's clock moves, wg_shim_boottime_ns = now, hs_take, ret = consume_initiation(m, &wb)
       L2b = BODY 7: acc = ib.ok && m_consume_initiation_1 && bytes_eq && m_consume_initiation_2 && m_ts_newer
             && m_not_flood
       L3  = BODY 8..9: CHECK(!acc) for kind 2; the CHECKs of a rejection / of an acceptance (wg_peer_put,
             latest, last, accepted updated)
     F  = statements 24..27: the three frees, return 0.
   The states between the segments are below. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Export WgNoise.proof.harness.replay.hrp3_rep.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Cutting a statement list (as law prim_aead's hm3 lemmas)                  *)
(* ---------------------------------------------------------------------- *)

Fixpoint hrp3_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hrp3_seqs l' rest) end.

Fixpoint hrp3_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hrp3_seql l') end.

Fixpoint hrp3_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hrp3_flat b | _ => [s] end.

Lemma hrp3_unfold_seql l : l <> [] ->
  unfold_Ssequence (hrp3_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hrp3_unfold_seqs l rest :
  unfold_Ssequence (hrp3_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hrp3_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hrp3_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hrp3_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hrp3_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hrp3_seql l) rest)).
  - simpl. rewrite hrp3_unfold_seql, hrp3_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 28 statements below (the last one a return) *)
Definition hrp3_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hrp3_flat RC.f_main fn_body] in
        (match fn_body RC.f_main with Ssequence s _ => hrp3_flat s | s => [s] end) in exact x).

Lemma hrp3_stmts_length : length hrp3_stmts = 28%nat.
Proof. reflexivity. Qed.

Definition hrp3_l (i n: nat) : list statement := firstn n (skipn i hrp3_stmts).

Definition hrp3_segA := ltac:(let x := eval cbv beta iota delta [hrp3_l hrp3_seql firstn skipn hrp3_stmts] in (hrp3_seql (hrp3_l 0 15)) in exact x).
Definition hrp3_segB := ltac:(let x := eval cbv beta iota delta [hrp3_l hrp3_seql firstn skipn hrp3_stmts] in (hrp3_seql (hrp3_l 15 8)) in exact x).
Definition hrp3_loop := ltac:(let x := eval cbv beta iota delta [nth hrp3_stmts] in (nth 23 hrp3_stmts Sskip) in exact x).
Definition hrp3_segF := ltac:(let x := eval cbv beta iota delta [hrp3_l hrp3_seql firstn skipn hrp3_stmts] in (hrp3_seql (hrp3_l 24 4)) in exact x).

(* the loop: i = 0; Sloop (if (i < steps) skip else break; BODY) (i++) *)
Definition hrp3_body : statement :=
  ltac:(let x := eval cbv beta iota delta [hrp3_loop] in
        (match hrp3_loop with Ssequence _ (Sloop (Ssequence _ b) _) => b | _ => Sskip end) in exact x).
Definition hrp3_bstmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hrp3_flat hrp3_body] in (hrp3_flat hrp3_body) in exact x).

Lemma hrp3_bstmts_length : length hrp3_bstmts = 9%nat.
Proof. reflexivity. Qed.

Definition hrp3_bl (i n: nat) : list statement := firstn n (skipn i hrp3_bstmts).

Definition hrp3_segL1 := ltac:(let x := eval cbv beta iota delta [hrp3_bl hrp3_seql firstn skipn hrp3_bstmts] in (hrp3_seql (hrp3_bl 0 2)) in exact x).
Definition hrp3_segL2a := ltac:(let x := eval cbv beta iota delta [hrp3_bl hrp3_seql firstn skipn hrp3_bstmts] in (hrp3_seql (hrp3_bl 2 4)) in exact x).
Definition hrp3_segL2b := ltac:(let x := eval cbv beta iota delta [hrp3_bl hrp3_seql firstn skipn hrp3_bstmts] in (hrp3_seql (hrp3_bl 6 1)) in exact x).
Definition hrp3_segL3 := ltac:(let x := eval cbv beta iota delta [hrp3_bl hrp3_seql firstn skipn hrp3_bstmts] in (hrp3_seql (hrp3_bl 7 2)) in exact x).

Lemma hrp3_body_eq :
  fn_body RC.f_main =
  Ssequence
    (hrp3_seqs (hrp3_l 0 15) (hrp3_seqs (hrp3_l 15 8) (hrp3_seqs (hrp3_l 23 1) (hrp3_seql (hrp3_l 24 4)))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hrp3_loop_eq :
  hrp3_seql (hrp3_l 23 1) = hrp3_loop.
Proof. reflexivity. Qed.

Lemma hrp3_loop_shape :
  hrp3_loop =
  Ssequence (Sset RC._i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
       (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar RC._i tulong) (Etempvar RC._steps tulong) tint) Sskip Sbreak)
          (hrp3_seqs (hrp3_bl 0 2) (hrp3_seqs (hrp3_bl 2 4) (hrp3_seqs (hrp3_bl 6 1) (hrp3_seql (hrp3_bl 7 2))))))
       (Sset RC._i (Ebinop Oadd (Etempvar RC._i tulong) (Econst_int (Int.repr 1) tint) tulong))).
Proof. reflexivity. Qed.

Lemma hrp3_segs_eq :
  hrp3_segA = hrp3_seql (hrp3_l 0 15) /\ hrp3_segB = hrp3_seql (hrp3_l 15 8) /\
  hrp3_segF = hrp3_seql (hrp3_l 24 4) /\
  hrp3_segL1 = hrp3_seql (hrp3_bl 0 2) /\ hrp3_segL2a = hrp3_seql (hrp3_bl 2 4) /\
  hrp3_segL2b = hrp3_seql (hrp3_bl 6 1) /\ hrp3_segL3 = hrp3_seql (hrp3_bl 7 2).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* main's context: its callees' specifications (as in hrp3_imports ++ hrp3_G) *)
(* ---------------------------------------------------------------------- *)

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Definition hrp3_G0 : funspecs :=
  [draw_boottime_spec; wg_noise_init_spec; @asm_env.nondet_bytes_spec W_replay; nondet_u8_spec;
   setup_device_spec x25519; m_identity_of_spec x25519 RC._x_replay__M_BASEPOINT; setup_peer_spec x25519;
   m_precomputed_spec x25519; (_quickproof_malloc, @malloc_spec' W_replay); (_quickproof_free, @free_spec' W_replay);
   bytes_set_spec; draw_steps_spec; fill_init_spec; draw_real_clock_spec;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc; wg_cookie_add_mac_to_packet_spec;
   hrp3_copy_init_spec; draw_u64_spec; hs_take_spec; wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   m_consume_initiation_1_spec x25519 aead_dec RC._x_replay__M_CONSTRUCTION RC._x_replay__M_IDENTIFIER;
   bytes_eq_spec; m_consume_initiation_2_spec aead_dec; m_ts_newer_spec; m_not_flood_spec; check_failed_spec;
   hs_same_spec; wg_peer_put_spec; m_last_consumption_spec; bytes_copy_spec].

Definition hrp3_V0 : varspecs := hrp3_V.

Definition hrp3_Delta : tycontext := func_tycontext RC.f_main hrp3_V0 hrp3_G0 [].

Definition hrp3_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hrp3_post gv)) (stackframe_of RC.f_main).

(* ---------------------------------------------------------------------- *)
(* The fixed part of the run                                               *)
(* ---------------------------------------------------------------------- *)

(* the globals and main's local variables *)
Record hrp3_fix := mkRFix {
  f_gv: globals;
  f_wa: val; f_wb: val; f_ita: val; f_itb: val; f_pta: val; f_ptb: val; f_pa: val; f_pb: val;
  f_ia: val; f_ib: val; f_rawa: val; f_rawb: val; f_psk: val; f_ssb: val; f_latest: val; f_ci: val;
  f_snap: val }.

Definition hrp3_lvars (F: hrp3_fix) : list localdef :=
  [lvar RC._wa (Tstruct RC._wg_device noattr) (f_wa F); lvar RC._wb (Tstruct RC._wg_device noattr) (f_wb F);
   lvar RC._ita (Tstruct RC._index_hashtable noattr) (f_ita F);
   lvar RC._itb (Tstruct RC._index_hashtable noattr) (f_itb F);
   lvar RC._pta (Tstruct RC._pubkey_hashtable noattr) (f_pta F);
   lvar RC._ptb (Tstruct RC._pubkey_hashtable noattr) (f_ptb F);
   lvar RC._pa (Tstruct RC._wg_peer noattr) (f_pa F); lvar RC._pb (Tstruct RC._wg_peer noattr) (f_pb F);
   lvar RC._ia (Tstruct RC._m_identity noattr) (f_ia F); lvar RC._ib (Tstruct RC._m_identity noattr) (f_ib F);
   lvar RC._raw_a (tarray tuchar 32) (f_rawa F); lvar RC._raw_b (tarray tuchar 32) (f_rawb F);
   lvar RC._psk (tarray tuchar 32) (f_psk F); lvar RC._ss_b (tarray tuchar 32) (f_ssb F);
   lvar RC._latest (tarray tuchar 12) (f_latest F);
   lvar RC._ci (Tstruct RC._m_consumed_initiation noattr) (f_ci F);
   lvar RC._snap (Tstruct RC._hs_snap noattr) (f_snap F);
   gvars (f_gv F)].

(* the values drawn by the prologue: the raw keys, the preshared key and whether it is used, the cookie
   secrets drawn by setup_device, the boot clock at setup, keypair_counter *)
Record hrp3_val := mkRVal {
  v_RAWA: list byte; v_RAWB: list byte; v_PSK: list byte; v_use: bool;
  v_secA: list byte; v_secB: list byte; v_bootA: int64; v_bootB: int64; v_kc: int64 }.

Definition hrp3_fix_ok (F: hrp3_fix) (V: hrp3_val) : Prop :=
  Zlength (v_RAWA V) = 32 /\ Zlength (v_RAWB V) = 32 /\ Zlength (v_PSK V) = 32 /\
  Zlength (v_secA V) = 32 /\ Zlength (v_secB V) = 32 /\ isptr (f_psk F).

Definition hrp3_DA (F: hrp3_fix) (V: hrp3_val) : device :=
  setup_dev x25519 (f_wa F) (f_ita F) (f_pta F) (v_RAWA V) (v_secA V) (v_bootA V).
Definition hrp3_DB (F: hrp3_fix) (V: hrp3_val) : device :=
  setup_dev x25519 (f_wb F) (f_itb F) (f_ptb F) (v_RAWB V) (v_secB V) (v_bootB V).
Definition hrp3_IA (V: hrp3_val) : mident := mident_of x25519 (v_RAWA V).
Definition hrp3_IB (V: hrp3_val) : mident := mident_of x25519 (v_RAWB V).
(* setup_peer's preshared key: use_psk ? psk : NULL *)
Definition hrp3_pskv (V: hrp3_val) : list byte := if v_use V then v_PSK V else zeros32.
Definition hrp3_PB0 (F: hrp3_fix) (V: hrp3_val) : peer :=
  setup_peer_val x25519 (hrp3_DA F V) (f_wa F) (f_pb F) nullval (mi_pub (hrp3_IB V)) (hrp3_pskv V) (Int64.repr 1).
Definition hrp3_PA0 (F: hrp3_fix) (V: hrp3_val) : peer :=
  setup_peer_val x25519 (hrp3_DB F V) (f_wb F) (f_pa F) nullval (mi_pub (hrp3_IA V)) (hrp3_pskv V) (Int64.repr 2).
Definition hrp3_SS (V: hrp3_val) : list byte := m_precomputed_model x25519 (hrp3_IB V) (mi_pub (hrp3_IA V)).

(* the shadow model's acceptance of M *)
Definition hrp3_accv (V: hrp3_val) (latest: list byte) (last now: int64) (M: init_msg)
  : option (list byte * list byte * list byte) :=
  hrp3_acc x25519 aead_dec (hrp3_IB V) (mi_pub (hrp3_IA V)) (hrp3_SS V) latest last now M.

(* ---------------------------------------------------------------------- *)
(* The loop's state                                                        *)
(* ---------------------------------------------------------------------- *)

(* the shim, A's table and peer for B, B's peer for A, the shadow model (latest, last), B's clock now, the
   last sent message (if any), the last accepted message (if any) *)
Record hrp3_dyn := mkRDyn {
  y_S: shim; y_TA: tstate; y_PB: peer; y_PA: peer; y_latest: list byte; y_last: int64; y_now: int64;
  y_hs: bool; y_Ms: init_msg; y_ha: bool; y_Ma: init_msg }.

Definition hrp3_inv (F: hrp3_fix) (V: hrp3_val) (Y: hrp3_dyn) : Prop :=
  hrp3_ta_ok (f_pb F) (y_TA Y) /\
  p_device (y_PB Y) = f_wa F /\ hs_sid (p_hs (y_PB Y)) = id_addr (f_wa F) /\
  hrp3_pa_ok (hrp3_PA0 F V) (y_PA Y) (y_latest Y) (y_last Y) /\
  Zlength (y_latest Y) = 12 /\
  Int64.unsigned (y_last Y) < 2 ^ 62 /\ Int64.unsigned (y_now Y) < 2 ^ 62 /\
  (y_ha Y = true ->
   exists t ck h, hrp3_ts x25519 aead_dec (hrp3_IB V) (mi_pub (hrp3_IA V)) (hrp3_SS V) (y_Ma Y) = Some (t, ck, h) /\
                  ts_newer t (y_latest Y) = false).

(* a malloc'd message buffer: its token, and the message (b) or anything *)
Definition hrp3_mbuf (b: bool) (M: init_msg) (p: val) : mpred :=
  (@malloc_token W_replay Ews t_init p * (if b then init_rep Ews p M else @data_at_ Noise.CS Ews t_init p))%logic.

(* the globals as the specifications use them *)
Definition hrp3_consts (gv: globals) : mpred :=
  (hc_const gv RC._x_replay__M_BASEPOINT basepoint9 * hc_const gv RC._x_replay__M_CONSTRUCTION construction_bytes *
   hc_const gv RC._x_replay__M_IDENTIFIER identifier_bytes)%logic.

(* the persistent locals, B's peer for A excepted: the devices, tables, A's peer for B, identities, keys,
   ss_b, latest *)
Definition hrp3_world (F: hrp3_fix) (V: hrp3_val) (TA: tstate) (PB: peer) (latest: list byte) : list mpred :=
  [device_rep Tsh (f_wa F) (hrp3_DA F V); device_rep Tsh (f_wb F) (hrp3_DB F V);
   itable Tsh (f_ita F) TA; itable Tsh (f_itb F) (hrp3_TB0 (f_pa F));
   ptable Tsh (f_pta F) (f_pb F); ptable Tsh (f_ptb F) (f_pa F);
   peer_rep Tsh (f_pb F) PB;
   @data_at HCS Tsh t_mident (mident_val (hrp3_IA V)) (f_ia F);
   @data_at HCS Tsh t_mident (mident_val (hrp3_IB V)) (f_ib F);
   hbytes Tsh (v_RAWA V) (f_rawa F); hbytes Tsh (v_RAWB V) (f_rawb F); hbytes Tsh (v_PSK V) (f_psk F);
   hbytes Tsh (hrp3_SS V) (f_ssb F); hbytes Tsh latest (f_latest F)].

(* the temps fixed during the loop *)
Definition hrp3_temps (Y: hrp3_dyn) (sp ap mp: val) (steps: Z) : list localdef :=
  [temp RC._steps (Vlong (Int64.repr steps)); temp RC._sent sp; temp RC._accepted ap; temp RC._m mp;
   temp RC._have_sent (Vint (if y_hs Y then Int.one else Int.zero));
   temp RC._have_accepted (Vint (if y_ha Y then Int.one else Int.zero));
   temp RC._now (Vlong (y_now Y)); temp RC._last (Vlong (y_last Y))].

Definition hrp3_globs (gv: globals) (S: shim) (kc: int64) : list mpred :=
  [shim_state gv S; noise_globals gv kc; wg_consts gv; hrp3_consts gv; mem_mgr gv].

(* the loop state at iteration i (Pi: the bound on i) *)
Definition hrp3_St (F: hrp3_fix) (V: hrp3_val) (sp ap mp: val) (steps: Z) (FR: mpred) (Pi: Prop) (i: Z)
  (Y: hrp3_dyn) : environ -> mpred :=
  PROPx [Pi; hrp3_fix_ok F V; hrp3_inv F V Y; 0 <= steps <= Int64.max_unsigned]
  (LOCALx (temp RC._i (Vlong (Int64.repr i)) :: hrp3_temps Y sp ap mp steps ++ hrp3_lvars F)
  (SEPx (hrp3_world F V (y_TA Y) (y_PB Y) (y_latest Y) ++
         [peer_rep Tsh (f_pa F) (y_PA Y);
          @data_at_ HCS Tsh t_mcinit (f_ci F); @data_at_ HCS Tsh t_hsnap (f_snap F);
          hrp3_mbuf (y_hs Y) (y_Ms Y) sp; hrp3_mbuf (y_ha Y) (y_Ma Y) ap; hrp3_mbuf false (y_Ma Y) mp] ++
         hrp3_globs (f_gv F) (y_S Y) (v_kc V) ++ [FR]))).

(* the loop invariant (before the test i < steps), and the state at the end of an iteration / at a continue
   (before i++) *)
Definition hrp3_Inv F V sp ap mp steps FR : environ -> mpred :=
  EX i: Z, EX Y: hrp3_dyn, hrp3_St F V sp ap mp steps FR (0 <= i <= steps) i Y.
Definition hrp3_Icont F V sp ap mp steps FR (i: Z) : environ -> mpred :=
  EX Y: hrp3_dyn, hrp3_St F V sp ap mp steps FR (0 <= i < steps) i Y.

(* ---------------------------------------------------------------------- *)
(* The states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

(* the initial shim (every shim global zero) *)
Definition hrp3_S0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

(* before A (after main's prologue: globals extracted, stack frame, mem_mgr created) *)
Definition hrp3_P0 (F: hrp3_fix) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hrp3_lvars F)
  (SEPx [data_at_ Tsh (Tstruct RC._wg_device noattr) (f_wa F); data_at_ Tsh (Tstruct RC._wg_device noattr) (f_wb F);
         data_at_ Tsh (Tstruct RC._index_hashtable noattr) (f_ita F);
         data_at_ Tsh (Tstruct RC._index_hashtable noattr) (f_itb F);
         data_at_ Tsh (Tstruct RC._pubkey_hashtable noattr) (f_pta F);
         data_at_ Tsh (Tstruct RC._pubkey_hashtable noattr) (f_ptb F);
         data_at_ Tsh (Tstruct RC._wg_peer noattr) (f_pa F); data_at_ Tsh (Tstruct RC._wg_peer noattr) (f_pb F);
         data_at_ Tsh (Tstruct RC._m_identity noattr) (f_ia F); data_at_ Tsh (Tstruct RC._m_identity noattr) (f_ib F);
         data_at_ Tsh (tarray tuchar 32) (f_rawa F); data_at_ Tsh (tarray tuchar 32) (f_rawb F);
         data_at_ Tsh (tarray tuchar 32) (f_psk F); data_at_ Tsh (tarray tuchar 32) (f_ssb F);
         data_at_ Tsh (tarray tuchar 12) (f_latest F);
         data_at_ Tsh (Tstruct RC._m_consumed_initiation noattr) (f_ci F);
         data_at_ Tsh (Tstruct RC._hs_snap noattr) (f_snap F);
         shim_state (f_gv F) hrp3_S0; noise_globals_raw (f_gv F) zeros32 zeros32 Int64.zero; wg_consts (f_gv F);
         hrp3_consts (f_gv F); mem_mgr (f_gv F); FR])).

(* after A: both devices set up, the identities, both peers (their handshake entries in the pools), ss_b *)
Definition hrp3_PA (F: hrp3_fix) (FR: mpred) : environ -> mpred :=
  EX V: hrp3_val, EX S: shim,
  PROPx [hrp3_fix_ok F V]
  (LOCALx (temp RC._have_sent (Vint Int.zero) :: temp RC._have_accepted (Vint Int.zero) :: hrp3_lvars F)
  (SEPx ([device_rep Tsh (f_wa F) (hrp3_DA F V); device_rep Tsh (f_wb F) (hrp3_DB F V);
          itable Tsh (f_ita F) (hrp3_TB0 (f_pb F)); itable Tsh (f_itb F) (hrp3_TB0 (f_pa F));
          ptable Tsh (f_pta F) (f_pb F); ptable Tsh (f_ptb F) (f_pa F);
          peer_rep Tsh (f_pb F) (hrp3_PB0 F V);
          @data_at HCS Tsh t_mident (mident_val (hrp3_IA V)) (f_ia F);
          @data_at HCS Tsh t_mident (mident_val (hrp3_IB V)) (f_ib F);
          hbytes Tsh (v_RAWA V) (f_rawa F); hbytes Tsh (v_RAWB V) (f_rawb F); hbytes Tsh (v_PSK V) (f_psk F);
          hbytes Tsh (hrp3_SS V) (f_ssb F); hout Tsh 12 (f_latest F);
          peer_rep Tsh (f_pa F) (hrp3_PA0 F V);
          @data_at_ HCS Tsh t_mcinit (f_ci F); @data_at_ HCS Tsh t_hsnap (f_snap F)] ++
         hrp3_globs (f_gv F) S (v_kc V) ++ [FR]))).

(* after B: the three buffers, latest = 0, last = 0, now and steps drawn: the loop's entry (before i = 0) *)
Definition hrp3_PB (F: hrp3_fix) (FR: mpred) : environ -> mpred :=
  EX V: hrp3_val, EX Y: hrp3_dyn, EX sp: val, EX ap: val, EX mp: val, EX steps: Z,
  PROPx [y_hs Y = false; y_ha Y = false; hrp3_fix_ok F V; hrp3_inv F V Y; 0 <= steps <= Int64.max_unsigned]
  (LOCALx (hrp3_temps Y sp ap mp steps ++ hrp3_lvars F)
  (SEPx (hrp3_world F V (y_TA Y) (y_PB Y) (y_latest Y) ++
         [peer_rep Tsh (f_pa F) (y_PA Y);
          @data_at_ HCS Tsh t_mcinit (f_ci F); @data_at_ HCS Tsh t_hsnap (f_snap F);
          hrp3_mbuf (y_hs Y) (y_Ms Y) sp; hrp3_mbuf (y_ha Y) (y_Ma Y) ap; hrp3_mbuf false (y_Ma Y) mp] ++
         hrp3_globs (f_gv F) (y_S Y) (v_kc V) ++ [FR]))).

(* after L1: m holds the message M of this iteration; kind 2 = a replay of the last accepted message *)
Definition hrp3_PL1 F V sp ap mp steps FR (i: Z) : environ -> mpred :=
  EX Y: hrp3_dyn, EX M: init_msg, EX kind: Z,
  PROPx [0 <= i < steps; hrp3_fix_ok F V; hrp3_inv F V Y; 0 <= steps <= Int64.max_unsigned;
         0 <= kind <= 2; kind = 2 -> y_ha Y = true /\ M = y_Ma Y]
  (LOCALx (temp RC._kind (Vint (Int.repr kind)) :: temp RC._i (Vlong (Int64.repr i)) ::
           hrp3_temps Y sp ap mp steps ++ hrp3_lvars F)
  (SEPx (hrp3_world F V (y_TA Y) (y_PB Y) (y_latest Y) ++
         [peer_rep Tsh (f_pa F) (y_PA Y);
          @data_at_ HCS Tsh t_mcinit (f_ci F); @data_at_ HCS Tsh t_hsnap (f_snap F);
          hrp3_mbuf (y_hs Y) (y_Ms Y) sp; hrp3_mbuf (y_ha Y) (y_Ma Y) ap; hrp3_mbuf true M mp] ++
         hrp3_globs (f_gv F) (y_S Y) (v_kc V) ++ [FR]))).

(* after L2a: B's clock (y_now) moved and set in the shim, the snapshot of pa's handshake taken, B consumed M:
   ret and pa's state as consume_initiation's specification says (cin_res) *)
Definition hrp3_PL2a F V sp ap mp steps FR (i: Z) : environ -> mpred :=
  EX Y: hrp3_dyn, EX M: init_msg, EX kind: Z,
  PROPx [0 <= i < steps; hrp3_fix_ok F V; hrp3_inv F V Y; 0 <= steps <= Int64.max_unsigned;
         0 <= kind <= 2; kind = 2 -> y_ha Y = true /\ M = y_Ma Y; s_boot (y_S Y) = y_now Y]
  (LOCALx (temp RC._ret (peer_result (cin_res x25519 aead_dec (hrp3_DB F V) [(f_pa F, Tsh, y_PA Y)] M (y_S Y))) ::
           temp RC._kind (Vint (Int.repr kind)) :: temp RC._i (Vlong (Int64.repr i)) ::
           hrp3_temps Y sp ap mp steps ++ hrp3_lvars F)
  (SEPx (hrp3_world F V (y_TA Y) (y_PB Y) (y_latest Y) ++
         [peers_rep (peers_after [(f_pa F, Tsh, y_PA Y)]
                       (cin_res x25519 aead_dec (hrp3_DB F V) [(f_pa F, Tsh, y_PA Y)] M (y_S Y)));
          @data_at_ HCS Tsh t_mcinit (f_ci F);
          @data_at HCS Tsh t_hsnap
            (hsnap_val (snap_of (hrp3_TB0 (f_pa F)) (hs_addr (f_pa F)) (hrp3_E0 (f_pa F)) (p_hs (y_PA Y))))
            (f_snap F);
          hrp3_mbuf (y_hs Y) (y_Ms Y) sp; hrp3_mbuf (y_ha Y) (y_Ma Y) ap; hrp3_mbuf true M mp] ++
         hrp3_globs (f_gv F) (y_S Y) (v_kc V) ++ [FR]))).

(* ci after the model chain: on acceptance its state, key, static and timestamp as the model computed them *)
Definition hrp3_ci_rep (R: option (list byte * list byte * list byte)) (ci: val) : mpred :=
  match R with
  | Some (t, ck, h) =>
      EX kv: list val, EX sv: list val,
        !! (Zlength kv = 32 /\ Zlength sv = 32 /\ Zlength t = 12) &&
        @data_at HCS Tsh t_mcinit (mcinit_val ck h kv sv (bytes t)) ci
  | None => @data_at_ HCS Tsh t_mcinit ci
  end.

(* after L2b: acc computed (hrp3_accv); ret and pa's state rewritten with it (hrp3_model_lemmas) *)
Definition hrp3_PL2b F V sp ap mp steps FR (i: Z) : environ -> mpred :=
  EX Y: hrp3_dyn, EX M: init_msg, EX kind: Z,
  PROPx [0 <= i < steps; hrp3_fix_ok F V; hrp3_inv F V Y; 0 <= steps <= Int64.max_unsigned;
         0 <= kind <= 2; kind = 2 -> y_ha Y = true /\ M = y_Ma Y; s_boot (y_S Y) = y_now Y]
  (LOCALx (temp RC._acc (Vint (match hrp3_accv V (y_latest Y) (y_last Y) (y_now Y) M with
                               | Some _ => Int.one | None => Int.zero end)) ::
           temp RC._ret (match hrp3_accv V (y_latest Y) (y_last Y) (y_now Y) M with
                         | Some _ => f_pa F | None => nullval end) ::
           temp RC._kind (Vint (Int.repr kind)) :: temp RC._i (Vlong (Int64.repr i)) ::
           hrp3_temps Y sp ap mp steps ++ hrp3_lvars F)
  (SEPx (hrp3_world F V (y_TA Y) (y_PB Y) (y_latest Y) ++
         [peer_rep Tsh (f_pa F) (match hrp3_accv V (y_latest Y) (y_last Y) (y_now Y) M with
                                 | Some (t, ck, h) => hrp3_pa_after (y_PA Y) M t ck h (y_now Y)
                                 | None => y_PA Y end);
          hrp3_ci_rep (hrp3_accv V (y_latest Y) (y_last Y) (y_now Y) M) (f_ci F);
          @data_at HCS Tsh t_hsnap
            (hsnap_val (snap_of (hrp3_TB0 (f_pa F)) (hs_addr (f_pa F)) (hrp3_E0 (f_pa F)) (p_hs (y_PA Y))))
            (f_snap F);
          hrp3_mbuf (y_hs Y) (y_Ms Y) sp; hrp3_mbuf (y_ha Y) (y_Ma Y) ap; hrp3_mbuf true M mp] ++
         hrp3_globs (f_gv F) (y_S Y) (v_kc V) ++ [FR]))).

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hrp3_post_canon {Espec: OracleKind} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hrp3_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

End Ctx.

(* ---------------------------------------------------------------------- *)
(* Facts proved elsewhere, taken as hypotheses by the segment lemmas        *)
(* (main's glue discharges them: prot_rep_lemmas3, hrp3_close, hrp3_model_lemmas) *)
(* ---------------------------------------------------------------------- *)

(* hrp3_rep_facts (hrp3_rep.v) = the statement of prot_rep_lemmas3 *)

(* the persistent locals' protocol reps back to the locals' data_at_ (main's returns); hrp3_close.v *)
Definition hrp3_close_fact : Prop :=
  forall (F: hrp3_fix) (DA DB: device) (TA: tstate) (PB PA: peer),
  hrp3_ta_ok (f_pb F) TA ->
  (device_rep Tsh (f_wa F) DA * device_rep Tsh (f_wb F) DB *
   itable Tsh (f_ita F) TA * itable Tsh (f_itb F) (hrp3_TB0 (f_pa F)) *
   ptable Tsh (f_pta F) (f_pb F) * ptable Tsh (f_ptb F) (f_pa F) *
   peer_rep Tsh (f_pb F) PB * peer_rep Tsh (f_pa F) PA)%logic
  |-- (data_at_ Tsh (Tstruct RC._wg_device noattr) (f_wa F) * data_at_ Tsh (Tstruct RC._wg_device noattr) (f_wb F) *
       data_at_ Tsh (Tstruct RC._index_hashtable noattr) (f_ita F) *
       data_at_ Tsh (Tstruct RC._index_hashtable noattr) (f_itb F) *
       data_at_ Tsh (Tstruct RC._pubkey_hashtable noattr) (f_pta F) *
       data_at_ Tsh (Tstruct RC._pubkey_hashtable noattr) (f_ptb F) *
       data_at_ Tsh (Tstruct RC._wg_peer noattr) (f_pb F) * data_at_ Tsh (Tstruct RC._wg_peer noattr) (f_pa F))%logic.

(* what every segment lemma assumes *)
Definition hrp3_facts : Prop := hrp3_model_facts /\ hrp3_rep_facts /\ hrp3_close_fact.
