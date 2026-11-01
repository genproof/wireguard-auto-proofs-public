(* law cookie_mac: main's context, locals,
   globals, the run's records, the split representations and the states between the phases of hck5_cut.v.  Port of the proof's hck3_defs.v.

   Changes from v1:
   - the shim's state is protocol4's `shim_state4 gv S w` with the refcount_t warnings EXACT; main never makes a
     reference count warn, so w = hck5_w0 (all zero, the initial value) in every state;
   - six new locals, the snapshots hs0 (struct hs_snap, at HCS as hs_take's specification), ps0 (pr_snap), da, db
     (dev_snap), sks (skb_snap), ss (shim_snap) (at CKS as the common4 specifications): `hck5_snaps0` when not
     taken (data_at_), `hck5_snaps` when taken (the values common4's take functions write);
   - three new temps: kes (the kents' list), head0 (ita's first entry), refs0 (p's reference count);
   - from P1b on, A's side is ONE SEP item `hck5_A R L A` (device wa, A's index table with p's handshake entry and
     the kents' entries in its pool, the public-key table, p without its cookie (hck5_prest, p in ANY state:
     randomized handshake, dead flag, last sent handshake, reference count, keypair slots filled by kents_add),
     the kents (kents_rep, snapped)), described by the record `A: hck5_aval` and the facts `hck5_aok R L A`;
     p's cookie stays a separate cookie_rep (as in v1); B = hck5_drest + checker_rep (as v1's).

   Conventions of the states (as in v1): main runs at the world compspecs W_cookie_mac; the protocol objects through
   prot_repr3's predicates (device_rep, itable, ptable, cookie_rep, checker_rep: Noise.CS; skb_rep: Cookie.CS), the
   harness structs as `@data_at HCS` (m_identity, hs_snap) / `@data_at CKS` (ck_snap and the v2 snapshots), byte
   buffers as hbytes / hout (HCS); malloc'd buffers `hck5_tok n p * hout/hbytes Ews .. p`.  BLAKE2s-valued values
   are variables defined by PROP facts `hck5_is x term` (entailer! does not substitute them).  FR: an opaque frame
   (TT * has_ext), carried along. *)
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
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require WgNoise.contracts.x_cookie_mac.
Local Open Scope logic.

(* an equality that the automation leaves alone (definitions of BLAKE2s-valued variables) *)
Definition hck5_is {A: Type} (x y: A) : Prop := x = y.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas, main's context                      *)
(* ---------------------------------------------------------------------- *)

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hck5_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec.

Definition hck5_Gprog : funspecs :=
  hck5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_cookie_mac ++ hck5_G.

(* main's context *)
Definition hck5_Delta : tycontext := func_tycontext HK.f_main hck5_V hck5_Gprog [].

(* a small context (a part of main proved against the callee specifications G it uses; hck5_lift) *)
Definition hck5_DeltaG (G: funspecs) : tycontext := func_tycontext HK.f_main hck5_V G [].
End Defs.

Definition hck5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hck5_post gv)) (@stackframe_of W_cookie_mac HK.f_main).

(* a part proved in a small context holds in a larger one *)
Lemma hck5_lift {Espec: OracleKind} G0 G P c R :
  incl G0 G -> NoDup (map fst hck5_V ++ map fst G) ->
  @semax W_cookie_mac Espec (hck5_DeltaG G0) P c R -> @semax W_cookie_mac Espec (hck5_DeltaG G) P c R.
Proof.
  intros HI HN H. eapply semax_Delta_subsumption; [| exact H].
  apply VST.veric.semax_prog.func_tycontext_sub; auto. apply incl_refl.
Qed.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hck5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hck5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 24 local variables (fn_vars order) *)
Record hck5_loc := mkLoc5 {
  l_wa: val; l_wb: val; l_ita: val; l_itb: val; l_pta: val; l_ptb: val; l_p: val; l_ib: val; l_cs: val;
  l_hs0: val; l_ps0: val; l_da: val; l_db: val; l_sks: val; l_ss: val;
  l_skb: val; l_rawa: val; l_rawb: val; l_pub: val; l_k: val; l_mac1: val; l_mac2: val; l_cookie: val;
  l_secret: val }.

Definition hck5_lvars (gv: globals) (L: hck5_loc) : list localdef :=
  [lvar HK._wa t_dev (l_wa L); lvar HK._wb t_dev (l_wb L);
   lvar HK._ita t_itab (l_ita L); lvar HK._itb t_itab (l_itb L);
   lvar HK._pta t_ptab (l_pta L); lvar HK._ptb t_ptab (l_ptb L);
   lvar HK._p t_peer (l_p L); lvar HK._ib t_mident (l_ib L); lvar HK._cs t_cksnap (l_cs L);
   lvar HK._hs0 t_hsnap (l_hs0 L); lvar HK._ps0 t_prsnap (l_ps0 L);
   lvar HK._da t_devsnap (l_da L); lvar HK._db t_devsnap (l_db L);
   lvar HK._sks t_skbsnap (l_sks L); lvar HK._ss t_shimsnap (l_ss L);
   lvar HK._skb t_skb (l_skb L);
   lvar HK._raw_a (tarray tuchar 32) (l_rawa L); lvar HK._raw_b (tarray tuchar 32) (l_rawb L);
   lvar HK._pub (tarray tuchar 32) (l_pub L); lvar HK._k (tarray tuchar 32) (l_k L);
   lvar HK._mac1 (tarray tuchar 16) (l_mac1 L); lvar HK._mac2 (tarray tuchar 16) (l_mac2 L);
   lvar HK._cookie__1 (tarray tuchar 16) (l_cookie L); lvar HK._secret (tarray tuchar 32) (l_secret L);
   gvars gv].

(* the harness's constants (common.h, renamed in this unit) *)
Definition hck5_consts (gv: globals) : mpred :=
  hc_const gv HK._x_cookie_mac__M_BASEPOINT basepoint9 *
  hc_const gv HK._x_cookie_mac__M_LABEL_MAC1 mac1_label *
  hc_const gv HK._x_cookie_mac__M_LABEL_COOKIE cookie_label.

(* the shim's state at the start (all globals zero), its refcount_t warnings (all zero; main never makes a
   reference count warn: they stay) *)
Definition hck5_shim0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.
Definition hck5_w0 : list int64 := [Int64.zero; Int64.zero; Int64.zero; Int64.zero; Int64.zero].

(* the globals of a state (after wg_noise_init): allocator, shim, noise.c's globals, the read-only tables,
   the harness's constants, the frame *)
Definition hck5_globs (gv: globals) (S: shim) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S hck5_w0; noise_globals gv Int64.zero; wg_consts gv; hck5_consts gv; FR].

(* a malloc'd buffer of n bytes (the token at the world) *)
Definition hck5_tok (n: Z) (p: val) : mpred := @malloc_token W_cookie_mac Ews (tarray tuchar n) p.

(* ---------------------------------------------------------------------- *)
(* The split representations (as v1)                                       *)
(* ---------------------------------------------------------------------- *)

Section Split.
#[local] Existing Instance Noise.CS.

(* a peer without its cookie *)
Definition hck5_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

(* a device without its cookie checker *)
Definition hck5_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

End Split.

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws, and the objects they determine (as v1)      *)
(* ---------------------------------------------------------------------- *)

Record hck5_run := mkRun5 {
  r_rawa: list byte;    (* raw_a *)
  r_rawb: list byte;    (* raw_b *)
  r_seca: list byte;    (* the cookie secret drawn by setup_device(&wa ..) *)
  r_secb: list byte;    (* .. by setup_device(&wb ..) (then overwritten by main) *)
  r_boot0: int64;       (* the first boot clock *)
  r_secret: list byte;  (* B's cookie secret drawn by main *)
  r_birth: int64;       (* .. and its birthdate *)
  r_honest: bool;       (* honest_peer *)
  r_pub: list byte }.   (* the peer's public key *)

Section Run.
Variable x25519: list byte -> list byte -> list byte.

Definition hck5_IDB (R: hck5_run) : identity := setup_identity x25519 (r_rawb R).

Definition hck5_run_ok (R: hck5_run) : Prop :=
  Zlength (r_rawa R) = 32 /\ Zlength (r_rawb R) = 32 /\ Zlength (r_seca R) = 32 /\
  Zlength (r_secb R) = 32 /\ Zlength (r_secret R) = 32 /\ Zlength (r_pub R) = 32 /\
  0 <= Int64.unsigned (r_boot0 R) < 2 ^ 62 /\ 0 <= Int64.unsigned (r_birth R) < 2 ^ 62 /\
  (r_honest R = true -> r_pub R = id_pub (hck5_IDB R)).

(* the devices after setup_device *)
Definition hck5_DA (R: hck5_run) (L: hck5_loc) : device :=
  setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) (r_rawa R) (r_seca R) (r_boot0 R).
Definition hck5_DB (R: hck5_run) (L: hck5_loc) : device :=
  setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) (r_rawb R) (r_secb R) (r_boot0 R).

(* B's checker after main drew its secret and birthdate *)
Definition hck5_CC1 (R: hck5_run) (L: hck5_loc) : checker :=
  let CC := d_cc (hck5_DB R L) in mkChk (r_secret R) (cc_ekey CC) (cc_mkey CC) (r_birth R) (cc_dev CC).

(* B as a whole with the checker CC (dev_take / dev_same see the device whole) *)
Definition hck5_DBc (R: hck5_run) (L: hck5_loc) (CC: checker) : device :=
  let D := hck5_DB R L in mkDev (d_dev D) (d_id D) CC (d_ptab D) (d_itab D).

(* the peer p after setup_peer (A's peer, B's or any public key, no psk, id 1), and its cookie *)
Definition hck5_P0 (R: hck5_run) (L: hck5_loc) : peer :=
  setup_peer_val x25519 (hck5_DA R L) (l_wa L) (l_p L) nullval (r_pub R) zeros32 (Int64.repr 1).
Definition hck5_C0 (R: hck5_run) : cookie := cookie_set_keys cookie_zero (r_pub R).

(* p's handshake entry after setup_peer (unhashed, outside the tables) *)
Definition hck5_E (L: hck5_loc) : entry := mkEntry (l_p L) IDX_HANDSHAKE Int.zero.

(* the A side of P1 (= v1's, unchanged after P1 in v1): device, empty tables, p without its cookie, p's entry *)
Definition hck5_aside1 (R: hck5_run) (L: hck5_loc) : list mpred :=
  [device_rep Tsh (l_wa L) (hck5_DA R L); itable Tsh (l_ita L) (mkT [] []); ptable Tsh (l_pta L) (l_p L);
   hck5_prest Tsh (l_p L) (hck5_P0 R L); entry_out Tsh (hs_addr (l_p L)) (hck5_E L)].

End Run.

(* ---------------------------------------------------------------------- *)
(* A's side from P1b on: p in ANY state, kents, the table *)
(* ---------------------------------------------------------------------- *)

(* the objects of A's side after P1b: the index table, p's state (without its cookie: p_cookie unused), the kents
   (snapped), the list head kes, the table's first entry head0 (all unchanged from P1b to the end) *)
Record hck5_aval := mkA5 { a_T: tstate; a_P: peer; a_KE: list kent4; a_kes: val; a_head0: val }.

(* A's side as ONE SEP item *)
Definition hck5_A (x25519: list byte -> list byte -> list byte) (R: hck5_run) (L: hck5_loc) (A: hck5_aval)
  : mpred :=
  device_rep Tsh (l_wa L) (hck5_DA x25519 R L) * itable Tsh (l_ita L) (a_T A) * ptable Tsh (l_pta L) (l_p L) *
  hck5_prest Tsh (l_p L) (a_P A) * kents_rep W_cookie_mac (a_kes A) (a_KE A).

(* what the frame CHECKs and the returns need of A's side:
   - p is a peer of device wa, alone in the public-key table, its handshake's identity is wa's, its keypair slots
     are NULL or kents;
   - the pool of the table: the kents' keypair entries (share Ews, as kents_add adds them), then p's handshake entry
     (share Tsh: p is main's local), every entry's peer is p;
   - the kents are snapped against the table; head0 is the table's first entry *)
Definition hck5_aok (L: hck5_loc) (A: hck5_aval) : Prop :=
  let T := a_T A in let P := a_P A in let KE := a_KE A in let p := l_p L in
  @field_compatible Noise.CS t_peer [] p /\
  p_device P = l_wa L /\ p_pknext P = nullval /\ hs_sid (p_hs P) = id_addr (l_wa L) /\
  Forall (fun v => v = nullval \/ In v (map ke_addr KE)) [p_cur P; p_prev P; p_next P] /\
  Forall (fun e => isptr (ke_addr e)) KE /\
  saddrs (t_D T) = map ke_addr KE ++ [hs_addr p] /\
  map (fun x => snd (fst x)) (t_D T) = map (fun _ => Ews) KE ++ [Tsh] /\
  Forall (fun x => e_peer (snd x) = p) (t_D T) /\
  Forall (fun e => kent_snapped T e = e) KE /\
  a_head0 A = hd nullval (t_L T).

(* ---------------------------------------------------------------------- *)
(* The B side, the setup's buffers (as v1)                                 *)
(* ---------------------------------------------------------------------- *)

Section Groups.
Variable x25519: list byte -> list byte -> list byte.

(* the B side without its checker: unchanged after P1 *)
Definition hck5_bside (R: hck5_run) (L: hck5_loc) : list mpred :=
  [hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L); itable Tsh (l_itb L) (mkT [] []); ptable Tsh (l_ptb L) nullval].

(* the setup's buffers: the identity ib, raw keys, the peer's public key *)
Definition hck5_bufs (R: hck5_run) (L: hck5_loc) : list mpred :=
  [@data_at HCS Tsh t_mident (mident_val (mident_of x25519 (r_rawb R))) (l_ib L);
   hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L); hbytes Tsh (r_pub R) (l_pub L)].

End Groups.

(* ---------------------------------------------------------------------- *)
(* The packet (P3), p's cookie state and cookie_mode (P4) (as v1)          *)
(* ---------------------------------------------------------------------- *)

Record hck5_pkt := mkPkt5 {
  q_n: Z; q_msg: list byte; q_proto: Z; q_ip4: list byte; q_ip6: list byte; q_port: list byte; q_now: int64 }.

Definition hck5_pkt_ok (Q: hck5_pkt) : Prop :=
  32 <= q_n Q <= Int.max_unsigned /\ Zlength (q_msg Q) = q_n Q /\ 0 <= q_proto Q <= 65535 /\
  Zlength (q_ip4 Q) = 4 /\ Zlength (q_ip6 Q) = 16 /\ Zlength (q_port Q) = 2 /\
  0 <= Int64.unsigned (q_now Q) < 2 ^ 62.

(* the sk_buff (data = msg) *)
Definition hck5_skb (Q: hck5_pkt) (m: val) : skb :=
  mkSkb m (Int.repr (q_n Q)) (q_proto Q) (q_ip4 Q) (q_ip6 Q) (q_port Q).

Section Cookie.
Variable x25519: list byte -> list byte -> list byte.

(* B's checker after cookie_mode's rotation (secret_birthdate = now when 120 s old; the secret is kept) *)
Definition hck5_CC2 (R: hck5_run) (L: hck5_loc) (now: int64) (cmode: bool) : checker :=
  let CC := hck5_CC1 x25519 R L in
  if andb cmode (birthdate_expired (cc_birth CC) (Int64.repr 120) now)
  then mkChk (cc_secret CC) (cc_ekey CC) (cc_mkey CC) now (cc_dev CC) else CC.

(* p's cookie C after P4: the keys of setup_peer; in cookie_mode valid, born now, B's cookie for the source
   (with B's secret: the cookie value is named ck, ck = cookie_of secret skb) *)
Definition hck5_ck_ok (R: hck5_run) (Q: hck5_pkt) (cmode: bool) (C: cookie) (ck: list byte) : Prop :=
  cookie_ok C /\ ck_dkey C = ck_dkey (hck5_C0 R) /\ ck_mkey C = ck_mkey (hck5_C0 R) /\
  (cmode = true -> ck_valid C = true /\ ck_birth C = q_now Q /\ ck_cookie C = ck).

(* the facts of P6's result: the message MSG2 validate saw (MSG1 unless corrupted), check_cookie chk, the
   rate limiter's answer rl, the bytes r a rotation drew, the result VR = (verdict, checker after) *)
Definition hck5_after_val (R: hck5_run) (L: hck5_loc) (Q: hck5_pkt) (m: val) (cmode: bool) (MSG1 MSG2: list byte)
  (corrupted chk rl: bool) (r: list byte) (VR: Z * checker) (S: shim) : Prop :=
  (corrupted = false -> MSG2 = MSG1) /\ Zlength MSG2 = q_n Q /\ Zlength r = 32 /\
  hck5_is VR (validate_model (hck5_CC2 R L (q_now Q) cmode) (hck5_skb Q m) MSG2 chk (q_now Q) rl r) /\
  s_boot S = q_now Q /\ s_rlallow S = rl /\
  (validate_rotates (hck5_CC2 R L (q_now Q) cmode) MSG2 chk (q_now Q) = true -> s_log S = r).

(* the facts before validate (after P6, P6b): MSG2, corrupted, chk, rl in the shim *)
Definition hck5_before_val (Q: hck5_pkt) (MSG1 MSG2: list byte) (corrupted rl: bool) (S: shim) : Prop :=
  (corrupted = false -> MSG2 = MSG1) /\ Zlength MSG2 = q_n Q /\ s_boot S = q_now Q /\ s_rlallow S = rl.

End Cookie.

(* ---------------------------------------------------------------------- *)
(* The scratch locals and the snapshots                                    *)
(* ---------------------------------------------------------------------- *)

(* the scratch locals of S1 .. S3: any contents *)
Definition hck5_scr (L: hck5_loc) : list mpred :=
  [hout Tsh 32 (l_k L); hout Tsh 16 (l_mac1 L); hout Tsh 16 (l_mac2 L); hout Tsh 16 (l_cookie L);
   hout Tsh 32 (l_secret L); @data_at_ CKS Tsh t_cksnap (l_cs L)].

(* the scratch locals of S4 .. S8 (the secret buffer is listed apart) *)
Definition hck5_scr2 (L: hck5_loc) : list mpred :=
  [hout Tsh 32 (l_k L); hout Tsh 16 (l_mac1 L); hout Tsh 16 (l_mac2 L); hout Tsh 16 (l_cookie L);
   @data_at_ CKS Tsh t_cksnap (l_cs L)].

(* .. of S5a (the cookie snapshot cs is listed apart) *)
Definition hck5_scr3 (L: hck5_loc) : list mpred :=
  [hout Tsh 32 (l_k L); hout Tsh 16 (l_mac1 L); hout Tsh 16 (l_mac2 L); hout Tsh 16 (l_cookie L)].

(* the six v2 snapshot locals, not taken (or no longer needed) *)
Definition hck5_snaps0 (L: hck5_loc) : list mpred :=
  [@data_at_ HCS Tsh t_hsnap (l_hs0 L); @data_at_ CKS Tsh t_prsnap (l_ps0 L);
   @data_at_ CKS Tsh t_devsnap (l_da L); @data_at_ CKS Tsh t_devsnap (l_db L);
   @data_at_ CKS Tsh t_skbsnap (l_sks L); @data_at_ CKS Tsh t_shimsnap (l_ss L)].

(* the snapshots taken (P5a: osk = None, sks not taken; P6b: osk = Some (the sk_buff)): hs0 = p's handshake and
   its entry in the table, ps0 = p whole with its cookie C, da = A's device (its public-key table's first peer p),
   db = B's device with the checker CC (an empty public-key table), ss = the shim S (no warning) *)
Definition hck5_snaps (x25519: list byte -> list byte -> list byte) (R: hck5_run) (L: hck5_loc) (A: hck5_aval)
  (C: cookie) (CC: checker) (S: shim) (osk: option skb) : list mpred :=
  [@data_at HCS Tsh t_hsnap (hsnap_val (hs_snap_cur (a_T A) (l_p L) (a_P A))) (l_hs0 L);
   @data_at CKS Tsh t_prsnap (prsnap_val (p_set_cookie (a_P A) C)) (l_ps0 L);
   @data_at CKS Tsh t_devsnap (devsnap_val (hck5_DA x25519 R L) (l_p L)) (l_da L);
   @data_at CKS Tsh t_devsnap (devsnap_val (hck5_DBc x25519 R L CC) nullval) (l_db L);
   match osk with
   | None => @data_at_ CKS Tsh t_skbsnap (l_sks L)
   | Some sk => @data_at CKS Tsh t_skbsnap (skbsnap_val sk) (l_sks L)
   end;
   @data_at CKS Tsh t_shimsnap (shimsnap_val S hck5_w0) (l_ss L)].

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* after the prologue: the stack frame converted, the initial globals *)
Definition hck5_S0 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hck5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wa L); @data_at_ Noise.CS Tsh t_dev (l_wb L);
          @data_at_ Noise.CS Tsh t_itab (l_ita L); @data_at_ Noise.CS Tsh t_itab (l_itb L);
          @data_at_ Noise.CS Tsh t_ptab (l_pta L); @data_at_ Noise.CS Tsh t_ptab (l_ptb L);
          @data_at_ Noise.CS Tsh t_peer (l_p L); @data_at_ HCS Tsh t_mident (l_ib L);
          @data_at_ CKS Tsh t_cksnap (l_cs L); @data_at_ Cookie.CS Tsh t_skb (l_skb L);
          hout Tsh 32 (l_rawa L); hout Tsh 32 (l_rawb L); hout Tsh 32 (l_pub L); hout Tsh 32 (l_k L);
          hout Tsh 16 (l_mac1 L); hout Tsh 16 (l_mac2 L); hout Tsh 16 (l_cookie L); hout Tsh 32 (l_secret L)] ++
         hck5_snaps0 L ++
         [mem_mgr gv; shim_state4 gv hck5_shim0 hck5_w0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hck5_consts gv; FR]))).

(* after P1: the setup done, its CHECKs passed (v2: B's checker secret was the shim's last draw, born at the
   boot clock); B's checker holds main's secret and birthdate; p's cookie is setup_peer's (= v1's S1) *)
Definition hck5_S1 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim,
  PROPx [hck5_run_ok x25519 R]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero))] ++ hck5_lvars gv L)
  (SEPx (hck5_aside1 x25519 R L ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC1 x25519 R L);
          cookie_rep Tsh (cookie_addr (l_p L)) (hck5_C0 R);
          @data_at_ Cookie.CS Tsh t_skb (l_skb L)] ++
         hck5_scr L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P1b: p in ANY state, p's entry in ita's pool (hashed or not), the kents added (in the pool, possibly in
   p's slots) and snapped, head0 = ita's first entry *)
Definition hck5_S1b (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A)] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC1 x25519 R L);
          cookie_rep Tsh (cookie_addr (l_p L)) (hck5_C0 R);
          @data_at_ Cookie.CS Tsh t_skb (l_skb L)] ++
         hck5_scr L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P2: len = n (32 <= n < 2^32), msg = m and copy = c allocated (exact size, uninitialised) *)
Definition hck5_S2 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX n: Z, EX m: val, EX c: val,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; 32 <= n <= Int.max_unsigned]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A);
            temp HK._len (Vlong (Int64.repr n)); temp HK._msg m; temp HK._copy c] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC1 x25519 R L);
          cookie_rep Tsh (cookie_addr (l_p L)) (hck5_C0 R);
          @data_at_ Cookie.CS Tsh t_skb (l_skb L);
          hck5_tok n m; hout Ews n m; hck5_tok n c; hout Ews n c] ++
         hck5_scr L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P3: the message (msg = q_msg), the sk_buff, the clock now (wg_shim_boottime_ns) *)
Definition hck5_S3 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q; s_boot S = q_now Q]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A);
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC1 x25519 R L);
          cookie_rep Tsh (cookie_addr (l_p L)) (hck5_C0 R);
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews (q_msg Q) m; hck5_tok (q_n Q) c; hout Ews (q_n Q) c] ++
         hck5_scr L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P4: p's cookie C (hck5_ck_ok; ck = cookie_of (B's secret) skb), cookie_mode, B's checker (hck5_CC2) *)
Definition hck5_S4 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q; s_boot S = q_now Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A);
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews (q_msg Q) m; hck5_tok (q_n Q) c; hout Ews (q_n Q) c;
          hout Tsh 32 (l_secret L)] ++
         hck5_scr2 L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P5a: the snapshots of the first round taken: cs = p's cookie C (ck_take), hs0, ps0, refs0 = p's
   reference count, da, db (B with the checker CC2), ss *)
Definition hck5_S5a (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q; s_boot S = q_now Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews (q_msg Q) m; hck5_tok (q_n Q) c; hout Ews (q_n Q) c;
          hout Tsh 32 (l_secret L); @data_at CKS Tsh t_cksnap (cksnap_val C) (l_cs L)] ++
         hck5_scr3 L ++
         hck5_snaps x25519 R L A C (hck5_CC2 x25519 R L (q_now Q) cmode) S None ++
         hck5_globs gv S FR))).

(* after P5: add_mac wrote MSG1 = the model's message into msg (copy = the same bytes: CHECKed), p's cookie is C1
   = the model's (mac1 remembered); the snapshots of P5a carried (= v1's S5 + the snapshots) *)
Definition hck5_S5 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q; s_boot S = q_now Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG1 m; hck5_tok (q_n Q) c; hbytes Ews MSG1 c;
          hout Tsh 32 (l_secret L)] ++
         hck5_scr2 L ++
         hck5_snaps x25519 R L A C (hck5_CC2 x25519 R L (q_now Q) cmode) S None ++
         hck5_globs gv S FR))).

(* after P5c: the frame CHECK passed; the snapshots are no longer needed (refs0 is: P7b compares it again) *)
Definition hck5_S5c (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q; s_boot S = q_now Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q]
  (LOCALx ([temp HK._corrupted (Vint Int.zero);
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG1 m; hck5_tok (q_n Q) c; hbytes Ews MSG1 c;
          hout Tsh 32 (l_secret L)] ++
         hck5_scr2 L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P6: msg and copy hold MSG2 (corrupted or not), check_cookie chk, the rate limiter's answer rl (in the
   shim), secret_birth / secret = B's checker's birthdate / secret (CC2) *)
Definition hck5_S6a (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_before_val Q MSG1 MSG2 corrupted rl S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (hck5_CC2 x25519 R L (q_now Q) cmode)) (l_secret L)] ++
         hck5_scr2 L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

(* after P6b: the snapshots of the second round taken (ps0 with p's cookie C1, db with CC2, sks = the sk_buff) *)
Definition hck5_S6b (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_before_val Q MSG1 MSG2 corrupted rl S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (hck5_CC2 x25519 R L (q_now Q) cmode)) (l_secret L)] ++
         hck5_scr2 L ++
         hck5_snaps x25519 R L A C1 (hck5_CC2 x25519 R L (q_now Q) cmode) S (Some (hck5_skb Q m)) ++
         hck5_globs gv S FR))).

(* after P6c: validate returned fst VR (in r); B's checker is snd VR; S = the shim after validate (its snapshot
   ss: the counters, which validate keeps) (= v1's S6 + the snapshots) *)
Definition hck5_S6 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool, EX r: list byte, EX VR: Z * checker,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode)));
            temp HK._r (Vint (Int.repr (fst VR)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (snd VR);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (hck5_CC2 x25519 R L (q_now Q) cmode)) (l_secret L)] ++
         hck5_scr2 L ++
         hck5_snaps x25519 R L A C1 (hck5_CC2 x25519 R L (q_now Q) cmode) S (Some (hck5_skb Q m)) ++
         hck5_globs gv S FR))).

(* after P7: the harness's verdict agreed with validate, B's checker after validate is the harness's (CHECKed):
   secret_birth / secret = snd VR's birthdate / secret (P7b writes them into db); the snapshots carried *)
Definition hck5_S7 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool, EX r: list byte, EX VR: Z * checker,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (snd VR)));
            temp HK._r (Vint (Int.repr (fst VR)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (snd VR);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (snd VR)) (l_secret L)] ++
         hck5_scr2 L ++
         hck5_snaps x25519 R L A C1 (hck5_CC2 x25519 R L (q_now Q) cmode) S (Some (hck5_skb Q m)) ++
         hck5_globs gv S FR))).

(* after P7b: the frame CHECK of validate passed; the snapshots and the secret no longer needed (= v1's S7) *)
Definition hck5_S7b (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool, EX r: list byte, EX VR: Z * checker,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A);
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._r (Vint (Int.repr (fst VR)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (snd VR);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hout Tsh 32 (l_secret L)] ++
         hck5_scr2 L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

End States.

(* ---------------------------------------------------------------------- *)
(* The dissolution of the setup's objects into main's stack frame          *)
(* (returns: P2's early ones, P8's), stated here and proved in hck5_free.v; *)
(* the phases P2 and P8 take it as a hypothesis                            *)
(* ---------------------------------------------------------------------- *)

Definition hck5_freeH (x25519: list byte -> list byte -> list byte) : Prop :=
  (* A's side and p's cookie: the kents' entries come out of the pool (kents_free takes them), the rest goes back
     to main's frame (p's handshake entry rejoins p) *)
  (forall R L A C, hck5_aok L A ->
     hck5_A x25519 R L A * cookie_rep Tsh (cookie_addr (l_p L)) C |--
     iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) (a_KE A) *
     kents_rep W_cookie_mac (a_kes A) (a_KE A) *
     @data_at_ W_cookie_mac Tsh t_dev (l_wa L) * @data_at_ W_cookie_mac Tsh t_itab (l_ita L) *
     @data_at_ W_cookie_mac Tsh t_ptab (l_pta L) * @data_at_ W_cookie_mac Tsh t_peer (l_p L)) /\
  (* B's side with its checker (v1's hck3_bside_free) *)
  (forall R L CC,
     fold_right sepcon emp (hck5_bside x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC |--
     @data_at_ W_cookie_mac Tsh t_dev (l_wb L) * @data_at_ W_cookie_mac Tsh t_itab (l_itb L) *
     @data_at_ W_cookie_mac Tsh t_ptab (l_ptb L)).
