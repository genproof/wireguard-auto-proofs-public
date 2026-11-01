(* law cookie_reply: main's context,
   locals, globals, the run's records and models, and the states of B's half of main (phases P1 .. P5b, before A's
   peers exist).  Port of the proof's hcy4_defs.v.

   Changes from v1:
   - the shim's state is protocol4's `shim_state4 gv S w` with the refcount_t warnings EXACT; main never makes a
     reference count warn, so w = hcy5_w0 (all zero, the initial value) in every state;
   - main has four new locals: the snapshots da, db (struct dev_snap), sks (struct skb_snap), ss (struct
     shim_snap).  Taken snapshots are `@data_at W Tsh t_xsnap (hcy5_xsv ..)` with the field values below (any
     specification of dev_take / skb_take / shim_take writes exactly these values; convert at the call if the
     specification states them at another compspecs); not yet taken / no longer needed: `@data_at_ W Tsh`;
   - `kes` is not initialized before P8 (no temp _kes before it);
   - the common.h layer is common4 (hc4_specs.v): the node list `hnodes_rep4 W` (struct hnode with `rest`, at CKS),
     the kents `kents_rep W` (whole keypair objects; their entries are pool items of A's index table), the structs (dev_snap, skb_snap, shim_snap, pr_snap) at CKS with common4's value functions
     (devsnap_val, skbsnap_val, shimsnap_val, prsnap_val).

   Conventions of the states (as in v1): main runs at the world compspecs W := W_cookie_reply.  The protocol objects
   through prot_repr3's predicates (device_rep, itable, ptable, checker_rep, cmsg_rep, skb_rep: Noise.CS /
   Cookie.CS inside), the harness struct m_identity as `@data_at HCS`, byte buffers as hbytes / hout (HCS).
   B's device is split into hcy5_drest (all but the checker) and its checker_rep.  BLAKE2s / AEAD-valued values
   (B's cookie CK, the reply CM) are variables defined by PROP facts `hcy5_is x term`.  FR: an opaque frame. *)
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
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require WgNoise.contracts.x_cookie_reply.
Local Open Scope logic.

Notation W := W_cookie_reply.

(* an equality that the automation leaves alone (definitions of BLAKE2s / AEAD-valued variables) *)
Definition hcy5_is {A: Type} (x y: A) : Prop := x = y.

Definition t_cnode5 := Tstruct HY._cnode noattr.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas, main's context                      *)
(* ---------------------------------------------------------------------- *)

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hcy5_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec.

Definition hcy5_Gprog : funspecs :=
  hcy5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W ++ hcy5_G.

(* main's context *)
Definition hcy5_Delta : tycontext := func_tycontext HY.f_main hcy5_V hcy5_Gprog [].

(* a small context (a part of main proved against the callee specifications G it uses; hcy5_lift) *)
Definition hcy5_DeltaG (G: funspecs) : tycontext := func_tycontext HY.f_main hcy5_V G [].
End Defs.

Definition hcy5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hcy5_post gv)) (@stackframe_of W HY.f_main).

(* a part proved in a small context holds in a larger one *)
Lemma hcy5_lift {Espec: OracleKind} G0 G P c R :
  incl G0 G -> NoDup (map fst hcy5_V ++ map fst G) ->
  @semax W Espec (hcy5_DeltaG G0) P c R -> @semax W Espec (hcy5_DeltaG G) P c R.
Proof.
  intros HI HN H. eapply semax_Delta_subsumption; [| exact H].
  apply VST.veric.semax_prog.func_tycontext_sub; auto. apply incl_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 23 local variables *)
Record hcy5_loc := mkLoc {
  l_wa: val; l_wb: val; l_ita: val; l_itb: val; l_pta: val; l_ptb: val; l_ib: val; l_skb: val;
  l_rawa: val; l_rawb: val; l_pub: val; l_secret: val; l_cookie: val; l_k: val; l_enc: val; l_img: val;
  l_img2: val; l_peers: val; l_da: val; l_db: val; l_sks: val; l_ss: val; l_pt: val }.

Definition hcy5_lvars (gv: globals) (L: hcy5_loc) : list localdef :=
  [lvar HY._wa t_dev (l_wa L); lvar HY._wb t_dev (l_wb L);
   lvar HY._ita t_itab (l_ita L); lvar HY._itb t_itab (l_itb L);
   lvar HY._pta t_ptab (l_pta L); lvar HY._ptb t_ptab (l_ptb L);
   lvar HY._ib t_mident (l_ib L); lvar HY._skb t_skb (l_skb L);
   lvar HY._raw_a (tarray tuchar 32) (l_rawa L); lvar HY._raw_b (tarray tuchar 32) (l_rawb L);
   lvar HY._pub (tarray tuchar 32) (l_pub L); lvar HY._secret (tarray tuchar 32) (l_secret L);
   lvar HY._cookie__1 (tarray tuchar 16) (l_cookie L); lvar HY._k (tarray tuchar 32) (l_k L);
   lvar HY._enc (tarray tuchar 32) (l_enc L); lvar HY._img (tarray tuchar 64) (l_img L);
   lvar HY._img2 (tarray tuchar 64) (l_img2 L); lvar HY._peers (tptr t_hnode4) (l_peers L);
   lvar HY._da t_devsnap (l_da L); lvar HY._db t_devsnap (l_db L);
   lvar HY._sks t_skbsnap (l_sks L); lvar HY._ss t_shimsnap (l_ss L);
   lvar HY._pt (tarray tuchar 16) (l_pt L);
   gvars gv].

(* the harness's constants (common.h, renamed in this unit) *)
Definition hcy5_consts (gv: globals) : mpred :=
  hc_const gv HY._x_cookie_reply__M_BASEPOINT basepoint9 *
  hc_const gv HY._x_cookie_reply__M_LABEL_COOKIE cookie_label.

(* the shim's state at the start (all globals zero), its refcount_t warnings (all zero; main never makes a
   reference count warn: they stay) *)
Definition hcy5_shim0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.
Definition hcy5_w0 : list int64 := [Int64.zero; Int64.zero; Int64.zero; Int64.zero; Int64.zero].

(* the globals of a state (after wg_noise_init): allocator, shim, noise.c's globals, the read-only tables,
   the harness's constants, the frame *)
Definition hcy5_globs (gv: globals) (S: shim) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S hcy5_w0; noise_globals gv Int64.zero; wg_consts gv; hcy5_consts gv; FR].

(* a malloc'd buffer of n bytes (the token at the world) *)
Definition hcy5_tok (n: Z) (p: val) : mpred := @malloc_token W Ews (tarray tuchar n) p.

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws, and the objects they determine (as v1)      *)
(* ---------------------------------------------------------------------- *)

Record hcy5_run := mkRun {
  r_rawa: list byte;    (* raw_a *)
  r_rawb: list byte;    (* raw_b *)
  r_seca: list byte;    (* the cookie secret drawn by setup_device(&wa ..) *)
  r_secb: list byte;    (* .. by setup_device(&wb ..) (then overwritten by main) *)
  r_boot0: int64;       (* the first boot clock *)
  r_secret: list byte;  (* B's cookie secret drawn by main *)
  r_birth: int64 }.     (* .. and its birthdate *)

Definition hcy5_run_ok (R: hcy5_run) : Prop :=
  Zlength (r_rawa R) = 32 /\ Zlength (r_rawb R) = 32 /\ Zlength (r_seca R) = 32 /\
  Zlength (r_secb R) = 32 /\ Zlength (r_secret R) = 32 /\
  0 <= Int64.unsigned (r_boot0 R) < 2 ^ 62 /\ 0 <= Int64.unsigned (r_birth R) < 2 ^ 62.

(* the packet: len (32 <= n < 2^32), the message bytes, the source, the clock, the receiver index *)
Record hcy5_pkt := mkPkt {
  q_n: Z; q_msg: list byte; q_proto: Z; q_ip4: list byte; q_ip6: list byte; q_port: list byte;
  q_now: int64; q_index: int }.

Definition hcy5_pkt_ok (Q: hcy5_pkt) : Prop :=
  32 <= q_n Q <= Int.max_unsigned /\ Zlength (q_msg Q) = q_n Q /\ 0 <= q_proto Q <= 65535 /\
  Zlength (q_ip4 Q) = 4 /\ Zlength (q_ip6 Q) = 16 /\ Zlength (q_port Q) = 2 /\
  0 <= Int64.unsigned (q_now Q) < 2 ^ 62.

(* the sk_buff (data = msg) *)
Definition hcy5_skb (Q: hcy5_pkt) (m: val) : skb :=
  mkSkb m (Int.repr (q_n Q)) (q_proto Q) (q_ip4 Q) (q_ip6 Q) (q_port Q).

(* the packet's mac1 (the associated data of the reply) *)
Definition hcy5_mac1 (Q: hcy5_pkt) : list byte := sublist (q_n Q - 32) (q_n Q - 16) (q_msg Q).

Section Run.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.

(* the harness's model identity of B *)
Definition hcy5_IB (R: hcy5_run) : mident := mident_of x25519 (r_rawb R).

(* the devices after setup_device *)
Definition hcy5_DA (R: hcy5_run) (L: hcy5_loc) : device :=
  setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) (r_rawa R) (r_seca R) (r_boot0 R).
Definition hcy5_DB (R: hcy5_run) (L: hcy5_loc) : device :=
  setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) (r_rawb R) (r_secb R) (r_boot0 R).

(* B's public key (wb.static_identity.static_public) *)
Definition hcy5_pubB (R: hcy5_run) (L: hcy5_loc) : list byte := id_pub (d_id (hcy5_DB R L)).

(* B's checker after main drew its secret and birthdate *)
Definition hcy5_CC1 (R: hcy5_run) (L: hcy5_loc) : checker :=
  let CC := d_cc (hcy5_DB R L) in mkChk (r_secret R) (cc_ekey CC) (cc_mkey CC) (r_birth R) (cc_dev CC).

(* .. after make_cookie's rotation (rr = the secret drawn when 120 s old) *)
Definition hcy5_CC2 (R: hcy5_run) (L: hcy5_loc) (Q: hcy5_pkt) (rr: list byte) : checker :=
  checker_rotate (hcy5_CC1 R L) (q_now Q) rr.

(* B as a whole with the checker CC (dev_take / dev_same see the device whole) *)
Definition hcy5_DBc (R: hcy5_run) (L: hcy5_loc) (CC: checker) : device :=
  let D := hcy5_DB R L in mkDev (d_dev D) (d_id D) CC (d_ptab D) (d_itab D).

(* B's cookie for the packet's source, and B's reply (the model's message_create) *)
Definition hcy5_CK (R: hcy5_run) (L: hcy5_loc) (Q: hcy5_pkt) (m: val) (rr: list byte) : list byte :=
  cookie_of (cc_secret (hcy5_CC2 R L Q rr)) (hcy5_skb Q m).
Definition hcy5_CM (R: hcy5_run) (L: hcy5_loc) (Q: hcy5_pkt) (nonce CK: list byte) : cookie_msg :=
  mkCM (Int.repr 3) (q_index Q) nonce (xaead_enc (cc_ekey (hcy5_CC1 R L)) nonce (hcy5_mac1 Q) CK).

(* the shim after message_create (the nonce drawn, then the rotation's secret) *)
Definition hcy5_S4shim (S: shim) (CC: checker) (Q: hcy5_pkt) (nonce rr: list byte) : shim :=
  if checker_rotates CC (q_now Q) then shim_draw (shim_draw S nonce) rr else shim_draw S nonce.

End Run.

(* the four snapshot locals, not taken (or no longer needed) *)
Definition hcy5_snaps0 (L: hcy5_loc) : list mpred :=
  [@data_at_ W Tsh t_devsnap (l_da L); @data_at_ W Tsh t_devsnap (l_db L);
   @data_at_ W Tsh t_skbsnap (l_sks L); @data_at_ W Tsh t_shimsnap (l_ss L)].

(* ---------------------------------------------------------------------- *)
(* The split representations                                               *)
(* ---------------------------------------------------------------------- *)

Section Split.
#[local] Existing Instance Noise.CS.

(* a device without its cookie checker *)
Definition hcy5_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

(* a pool entry with any list fields *)
Definition hcy5_pool_item (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => EX n: val, EX h: bool, entry_at sh a E n h end.

End Split.

(* ---------------------------------------------------------------------- *)
(* The groups of SEP items (B's half: A's side still empty)                *)
(* ---------------------------------------------------------------------- *)

Section Groups.
Variable x25519: list byte -> list byte -> list byte.

(* A's side before its peers: device, empty index table, empty public-key table, peers = NULL *)
Definition hcy5_aside0 (R: hcy5_run) (L: hcy5_loc) : list mpred :=
  [device_rep Tsh (l_wa L) (hcy5_DA x25519 R L); itable Tsh (l_ita L) (mkT [] []);
   ptable Tsh (l_pta L) nullval; @data_at W Tsh (tptr t_hnode4) nullval (l_peers L)].

(* B's side with the checker CC *)
Definition hcy5_bside (R: hcy5_run) (L: hcy5_loc) (CC: checker) : list mpred :=
  [hcy5_drest Tsh (l_wb L) (hcy5_DB x25519 R L); checker_rep Tsh (cc_addr (l_wb L)) CC;
   itable Tsh (l_itb L) (mkT [] []); ptable Tsh (l_ptb L) nullval].

(* the setup's buffers: B's model identity, the raw keys *)
Definition hcy5_bufs (R: hcy5_run) (L: hcy5_loc) : list mpred :=
  [@data_at HCS Tsh t_mident (mident_val (hcy5_IB x25519 R)) (l_ib L);
   hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L)].

End Groups.

(* the packet's buffers from P3 on: skb, msg, copy (both the message bytes), the reply's token *)
Definition hcy5_pbufs (L: hcy5_loc) (Q: hcy5_pkt) (m c rp: val) : list mpred :=
  [skb_rep Tsh (l_skb L) (hcy5_skb Q m); hcy5_tok (q_n Q) m; hbytes Ews (q_msg Q) m;
   hcy5_tok (q_n Q) c; hbytes Ews (q_msg Q) c; @malloc_token W Ews t_cmsg rp].

(* the scratch locals before P4: any contents *)
Definition hcy5_scrA (L: hcy5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); hout Tsh 32 (l_secret L); hout Tsh 16 (l_cookie L); hout Tsh 32 (l_k L);
   hout Tsh 32 (l_enc L); hout Tsh 64 (l_img L); hout Tsh 64 (l_img2 L); hout Tsh 16 (l_pt L)].

(* the scratch locals from P5b on (cookie and img are listed apart) *)
Definition hcy5_scrB (L: hcy5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); hout Tsh 32 (l_secret L); hout Tsh 32 (l_k L); hout Tsh 32 (l_enc L);
   hout Tsh 64 (l_img2 L); hout Tsh 16 (l_pt L)].

(* .. after P5, before P5b: the secret is listed apart *)
Definition hcy5_scrC (L: hcy5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); hout Tsh 32 (l_k L); hout Tsh 32 (l_enc L); hout Tsh 64 (l_img2 L);
   hout Tsh 16 (l_pt L)].

(* ---------------------------------------------------------------------- *)
(* The states of B's half                                                  *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.

(* after the prologue: the stack frame (at the world), the initial globals *)
Definition hcy5_S0 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hcy5_lvars gv L)
  (SEPx [@data_at_ W Tsh t_dev (l_wa L); @data_at_ W Tsh t_dev (l_wb L);
         @data_at_ W Tsh t_itab (l_ita L); @data_at_ W Tsh t_itab (l_itb L);
         @data_at_ W Tsh t_ptab (l_pta L); @data_at_ W Tsh t_ptab (l_ptb L);
         @data_at_ W Tsh t_mident (l_ib L); @data_at_ W Tsh t_skb (l_skb L);
         @data_at_ W Tsh (tarray tuchar 32) (l_rawa L); @data_at_ W Tsh (tarray tuchar 32) (l_rawb L);
         @data_at_ W Tsh (tarray tuchar 32) (l_pub L); @data_at_ W Tsh (tarray tuchar 32) (l_secret L);
         @data_at_ W Tsh (tarray tuchar 16) (l_cookie L); @data_at_ W Tsh (tarray tuchar 32) (l_k L);
         @data_at_ W Tsh (tarray tuchar 32) (l_enc L); @data_at_ W Tsh (tarray tuchar 64) (l_img L);
         @data_at_ W Tsh (tarray tuchar 64) (l_img2 L); @data_at_ W Tsh (tptr t_hnode4) (l_peers L);
         @data_at_ W Tsh t_devsnap (l_da L); @data_at_ W Tsh t_devsnap (l_db L);
         @data_at_ W Tsh t_skbsnap (l_sks L); @data_at_ W Tsh t_shimsnap (l_ss L);
         @data_at_ W Tsh (tarray tuchar 16) (l_pt L);
         mem_mgr gv; shim_state4 gv hcy5_shim0 hcy5_w0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
         wg_consts gv; hcy5_consts gv; FR])).

(* after P1: both devices set up, B's checker holds main's secret and birthdate; no peer yet *)
Definition hcy5_S1 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim,
  PROPx [hcy5_run_ok R]
  (LOCALx ([temp HY._cns nullval] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC1 x25519 R L) ++
         hcy5_bufs x25519 R L ++
         [@data_at_ Cookie.CS Tsh t_skb (l_skb L)] ++ hcy5_scrA L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P2: len = n (32 <= n < 2^32), msg = m, copy = c (n bytes each), reply = rp allocated *)
Definition hcy5_S2 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX n: Z, EX m: val, EX c: val, EX rp: val,
  PROPx [hcy5_run_ok R; 32 <= n <= Int.max_unsigned]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr n));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC1 x25519 R L) ++
         hcy5_bufs x25519 R L ++
         [@data_at_ Cookie.CS Tsh t_skb (l_skb L);
          hcy5_tok n m; hout Ews n m; hcy5_tok n c; hout Ews n c;
          @malloc_token W Ews t_cmsg rp; @data_at_ Cookie.CS Ews t_cmsg rp] ++
         hcy5_scrA L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P3: the message (msg = copy = q_msg), the sk_buff, the clock now (wg_shim_boottime_ns), index *)
Definition hcy5_S3 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  PROPx [hcy5_run_ok R; hcy5_pkt_ok Q; s_boot S = q_now Q]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp;
            temp HY._now (Vlong (q_now Q)); temp HY._index (Vint (q_index Q))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC1 x25519 R L) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [@data_at_ Cookie.CS Ews t_cmsg rp] ++
         hcy5_scrA L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P4: the reply CM = the model's message_create (nonce, rotation draw rr), B's checker after the
   rotation; secret_birth / secret = B's birthdate / secret before the call; db = B whole before the call (its
   checker CC1, an empty public-key table), sks = the sk_buff *)
Definition hcy5_S4 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CM: cookie_msg,
  PROPx [hcy5_run_ok R; hcy5_pkt_ok Q; s_boot S = q_now Q; Zlength nonce = 24; Zlength rr = 32;
         hcy5_is CM (fst (mc_res xaead_enc (hcy5_CC1 x25519 R L) (hcy5_skb Q m) (q_index Q) nonce (q_msg Q)
                               S rr))]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp;
            temp HY._now (Vlong (q_now Q)); temp HY._index (Vint (q_index Q));
            temp HY._secret_birth (Vlong (r_birth R))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM;
          hbytes Tsh (r_secret R) (l_secret L); hout Tsh 32 (l_pub L); hout Tsh 16 (l_cookie L);
          hout Tsh 32 (l_k L); hout Tsh 32 (l_enc L); hout Tsh 64 (l_img L); hout Tsh 64 (l_img2 L);
          hout Tsh 16 (l_pt L);
          @data_at_ W Tsh t_devsnap (l_da L);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DBc x25519 R L (hcy5_CC1 x25519 R L)) nullval) (l_db L);
          @data_at CKS Tsh t_skbsnap (skbsnap_val (hcy5_skb Q m)) (l_sks L);
          @data_at_ W Tsh t_shimsnap (l_ss L)] ++
         hcy5_globs gv (hcy5_S4shim S (hcy5_CC1 x25519 R L) Q nonce rr) FR))).

(* the facts of B's reply from P5 on: CK = B's cookie, CM = B's reply *)
Definition hcy5_reply_ok (R: hcy5_run) (L: hcy5_loc) (Q: hcy5_pkt) (m: val) (nonce rr CK: list byte)
  (CM: cookie_msg) : Prop :=
  hcy5_run_ok R /\ hcy5_pkt_ok Q /\ Zlength nonce = 24 /\ Zlength rr = 32 /\
  hcy5_is CK (hcy5_CK x25519 R L Q m rr) /\ hcy5_is CM (hcy5_CM x25519 xaead_enc R L Q nonce CK).

(* after P5: B's reply CHECKed; the buffer cookie holds B's cookie CK; secret / secret_birth = B's secret and
   birthdate after the rotation (the model's); the snapshots db, sks as after P4 *)
Definition hcy5_S5 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  PROPx [hcy5_reply_ok R L Q m nonce rr CK CM]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp;
            temp HY._secret_birth (Vlong (cc_birth (hcy5_CC2 x25519 R L Q rr)))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L);
          hbytes Tsh (cc_secret (hcy5_CC2 x25519 R L Q rr)) (l_secret L);
          @data_at_ W Tsh t_devsnap (l_da L);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DBc x25519 R L (hcy5_CC1 x25519 R L)) nullval) (l_db L);
          @data_at CKS Tsh t_skbsnap (skbsnap_val (hcy5_skb Q m)) (l_sks L);
          @data_at_ W Tsh t_shimsnap (l_ss L)] ++
         hcy5_scrC L ++ hcy5_globs gv S FR))).

Definition hcy5_S5b (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  PROPx [hcy5_reply_ok R L Q m nonce rr CK CM]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L)] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

End States.

(* ---------------------------------------------------------------------- *)
(* A's half: the harness's cnodes, the pool of A's index table, the peers  *)
(* ---------------------------------------------------------------------- *)

(* a cnode's snapshot (field cs, at offset 8): not yet taken, or the cookie C *)
Definition hcy5_cs_rep (o: option cookie) (p: val) : mpred :=
  match o with
  | None => @data_at_ CKS Ews t_cksnap p
  | Some C => @data_at CKS Ews t_cksnap (cksnap_val C) p
  end.

(* the cnodes (struct cnode {n; cs; next}, malloc'd): the list cns = CL (newest first) of (address, node
   address, snapshot) *)
Definition hcy5_chead (CL: list (val * val * option cookie)) : val :=
  match CL with [] => nullval | (c, _, _) :: _ => c end.

Fixpoint hcy5_cns (l: val) (CL: list (val * val * option cookie)) : mpred :=
  match CL with
  | [] => !! (l = nullval) && emp
  | (c, nd, o) :: CL' =>
      !! (l = c) &&
      (@malloc_token W Ews t_cnode5 c *
       @field_at W Ews t_cnode5 [StructField HY._n] nd c *
       hcy5_cs_rep o (offset_val 8 c) *
       @field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead CL') c *
       hcy5_cns (hcy5_chead CL') CL')
  end.

(* the cnodes are one per node, in the reverse order of the nodes (pushed while walking the node list) *)
Definition hcy5_cl_nodes (CL: list (val * val * option cookie)) (NS: list hnode4) : Prop :=
  map (fun x => snd (fst x)) CL = rev (map hn_addr NS) /\ NoDup (map (fun x => fst (fst x)) CL).
(* ... no snapshot taken yet *)
Definition hcy5_cl_none (CL: list (val * val * option cookie)) : Prop :=
  Forall (fun x => snd x = None) CL.
(* ... each holds its peer's cookie (the peers PS in node order) *)
Definition hcy5_cl_snap (CL: list (val * val * option cookie)) (PS: list (val * share * peer)) : Prop :=
  map snd CL = rev (map (fun x => Some (p_cookie (snd x))) PS).

(* the heads of the lists: nodes, peers (= the public-key table's first peer), kents *)
Definition hcy5_head (NS: list hnode4) : val := match NS with [] => nullval | N :: _ => hn_addr N end.
Definition hcy5_phead (PS: list (val * share * peer)) : val :=
  match PS with [] => nullval | (a, _, _) :: _ => a end.
Definition hcy5_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the pool of A's index table: the kents' keypair entries (at the kents' addresses, owner `own k`, a peer of
   the list), then the peers' handshake entries; ix = the entries' indices (by entry address) *)
Definition hcy5_kentry (own: val -> val) (ix: val -> int) (k: val) : val * share * entry :=
  (k, Ews, mkEntry (own k) IDX_KEYPAIR (ix k)).
Definition hcy5_hent (ix: val -> int) (a: val) : val * share * entry :=
  (hs_addr a, Ews, mkEntry a IDX_HANDSHAKE (ix (hs_addr a))).
Definition hcy5_pool (AS KS: list val) (own: val -> val) (ix: val -> int) : list (val * share * entry) :=
  map (hcy5_kentry own ix) KS ++ map (hcy5_hent ix) AS.

(* the table of A: that pool (peers PS, kents KE), any list of hashed entries, their indices pairwise distinct
   (insert draws a fresh index) *)
Definition hcy5_T_ok (PS: list (val * share * peer)) (KE: list kent4) (T: tstate) : Prop :=
  (exists own ix, t_D T = hcy5_pool (map peer_addr4 PS) (map ke_addr KE) own ix /\
                  Forall (fun k => In (own k) (map peer_addr4 PS)) (map ke_addr KE)) /\
  NoDup (t_indices T (t_L T)).

(* every peer of A: malloc'd (share Ews), device wa and A's static identity, 1 .. INT_MAX - 1 references, its
   cookie key is the label key of its public key (setup_peer; main never changes the keys), its keypair slots
   NULL or kents (KS: the kents' addresses) *)
Definition hcy5_pok (L: hcy5_loc) (KS: list val) (x: val * share * peer) : Prop :=
  match x with (a, sh, P) =>
    sh = Ews /\ p_device P = l_wa L /\ hs_sid (p_hs P) = id_addr (l_wa L) /\
    0 < Int.unsigned (p_refs P) < 2147483647 /\
    ck_dkey (p_cookie P) = label_key cookie_label (hs_rstatic (p_hs P)) /\
    Forall (fun k => k = nullval \/ In k KS) [p_cur P; p_prev P; p_next P]
  end.

(* the node list and the peers: the same peers, in the same order, distinct, chained by pubkey_next from the
   public-key table's head *)
Definition hcy5_lists_ok (L: hcy5_loc) (KS: list val) (NS: list hnode4) (PS: list (val * share * peer)) : Prop :=
  Forall (hcy5_pok L KS) PS /\ hnodes_peers4 NS PS /\ NoDup (map peer_addr4 PS) /\ NoDup (map hn_addr NS) /\
  pk_chain (hcy5_phead PS) PS.

(* np: NULL, or the node of a peer whose public key is B's *)
Definition hcy5_np_ok (pubB: list byte) (NS: list hnode4) (PS: list (val * share * peer)) (np: val) : Prop :=
  np = nullval \/
  exists N a P, In (N, (a, Ews, P)) (combine NS PS) /\ hn_addr N = np /\ hs_rstatic (p_hs P) = pubB.

(* an honest run (mode 0, np not NULL): the reply A consumes is B's reply CM with P's handshake index (P's
   entry hashed with that index), P has sent the packet's mac1 *)
Definition hcy5_honest_ok (pubB: list byte) (Q: hcy5_pkt) (CM CM': cookie_msg) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (np: val) : Prop :=
  exists N a P, In (N, (a, Ews, P)) (combine NS PS) /\ hn_addr N = np /\ hs_rstatic (p_hs P) = pubB /\
    ck_sent (p_cookie P) = true /\ ck_last_mac1 (p_cookie P) = hcy5_mac1 Q /\
    t_entry T (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE (cm_receiver CM')) /\ In (hs_addr a) (t_L T) /\
    cm_nonce CM' = cm_nonce CM /\ cm_enc CM' = cm_enc CM.

(* ---------------------------------------------------------------------- *)
(* The harness's model of the consumption (P11)                            *)
(* ---------------------------------------------------------------------- *)

(* the peer of the node at nd *)
Definition hcy5_nodepeer (NS: list hnode4) (nd: val) : val :=
  match find (fun N => if eq_dec (hn_addr N) nd then true else false) NS with
  | Some N => hn_p N
  | None => nullval
  end.

(* the first cnode whose node's peer is p *)
Fixpoint hcy5_cfind (NS: list hnode4) (CL: list (val * val * option cookie)) (p: val) : val :=
  match CL with
  | [] => nullval
  | (c, nd, _) :: CL' => if eq_dec (hcy5_nodepeer NS nd) p then c else hcy5_cfind NS CL' p
  end.

Section Model.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the kernel's consumption (message_consume_model at the clock now) *)
Definition hcy5_res (T: tstate) (PS: list (val * share * peer)) (M: cookie_msg) (now: int64)
  : option (val * peer) :=
  message_consume_model xaead_dec T PS M now.

(* the harness's target: the cnode of the accepted peer, or NULL *)
Definition hcy5_tgt (NS: list hnode4) (CL: list (val * val * option cookie)) (res: option (val * peer)) : val :=
  match res with Some (a, _) => hcy5_cfind NS CL a | None => nullval end.

End Model.

(* ---------------------------------------------------------------------- *)
(* The returns (P2, P7, P13): back to the stack frame                       *)
(* ---------------------------------------------------------------------- *)

(* pure separation logic (a child proves it: hcy5_close.v); a hypothesis of P2, P7, P13 *)
Definition hcy5_closeH : Prop :=
  (forall sh wg D, device_rep sh wg D |-- @data_at_ W sh t_dev wg) /\
  (forall sh wg D CC, hcy5_drest sh wg D * checker_rep sh (cc_addr wg) CC |-- @data_at_ W sh t_dev wg) /\
  (forall sh tab T, itable sh tab T |-- @data_at_ W sh t_itab tab * iter_sepcon hcy5_pool_item (t_D T)) /\
  (forall sh tab h, ptable sh tab h |-- @data_at_ W sh t_ptab tab) /\
  (forall sh p s, skb_rep sh p s |-- @data_at_ W sh t_skb p) /\
  (forall sh p, @data_at_ Cookie.CS sh t_skb p |-- @data_at_ W sh t_skb p) /\
  (forall sh v p, @data_at HCS sh t_mident v p |-- @data_at_ W sh t_mident p) /\
  (forall sh n p, hout sh n p |-- @data_at_ W sh (tarray tuchar n) p) /\
  (forall sh bs p, hbytes sh bs p |-- @data_at_ W sh (tarray tuchar (Zlength bs)) p).

(* ---------------------------------------------------------------------- *)
(* The states of A's half                                                  *)
(* ---------------------------------------------------------------------- *)

Section AStates.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* A's side: device, index table T, public-key table, the local `peers`, the node list NS, the peers PS *)
Definition hcy5_aside (R: hcy5_run) (L: hcy5_loc) (T: tstate) (NS: list hnode4) (PS: list (val * share * peer))
  : list mpred :=
  [device_rep Tsh (l_wa L) (hcy5_DA x25519 R L); itable Tsh (l_ita L) T; ptable Tsh (l_pta L) (hcy5_phead PS);
   @data_at W Tsh (tptr t_hnode4) (hcy5_head NS) (l_peers L); hnodes_rep4 W (hcy5_head NS) NS; peers_rep PS].

(* after P6: A's peers PS (nodes NS), their handshake entries in A's pool (unhashed), np = B's node or NULL *)
Definition hcy5_S6 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L [] NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS [] T]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside R L T NS PS ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L)] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P7: every peer's rest drawn (peer_randomize_rest: cookie state, dead flag, last sent handshake; keys
   unchanged), some handshake entries hashed, one cnode per node (no snapshot yet) *)
Definition hcy5_S7 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie),
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L [] NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS [] T;
         hcy5_cl_nodes CL NS; hcy5_cl_none CL]
  (LOCALx ([temp HY._cns (hcy5_chead CL); temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside R L T NS PS ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L);
          hcy5_cns (hcy5_chead CL) CL] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P8: the kents KE (whole keypairs of any content; their entries hashed in A's table, owners = peers of
   the list, possibly in their owners' empty slots) *)
Definition hcy5_S8 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_none CL]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside R L T NS PS ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) KE] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P9: the reply A consumes CM' (honest: B's reply to P, P remembers the packet's mac1), its image in
   img *)
Definition hcy5_S9 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_none CL; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside R L T NS PS ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) KE] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after P10: the nodes hold the snapshots of the peers (table T), the cnodes their peers' cookies, the kents
   their own snapshots (PS: the peers before the call); da = A as a whole, head0 = the table's first entry,
   ss = the shim's counters and warnings (S: the shim before and after the call); the clock now2; the peers
   after wg_cookie_message_consume *)
Definition hcy5_S10 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  EX now2: int64,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_snap CL PS; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np;
         0 <= Int64.unsigned now2 < 2 ^ 62]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero));
            temp HY._head0 (hd nullval (t_L T)); temp HY._now (Vlong now2)] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside R L T (hnodes_snapped4 T NS PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L);
          @data_at_ W Tsh t_devsnap (l_db L); @data_at_ W Tsh t_skbsnap (l_sks L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S hcy5_w0) (l_ss L)] ++
         hcy5_scrB L ++ hcy5_globs gv S FR))).

(* after P11 (and after P12): target = the cnode of the accepted peer or NULL (the harness's model agrees
   with the kernel's), the CHECK of the accepted peer's cookie passed *)
Definition hcy5_S11 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  EX now2: int64,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_snap CL PS; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np;
         0 <= Int64.unsigned now2 < 2 ^ 62]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero));
            temp HY._head0 (hd nullval (t_L T));
            temp HY._target (hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside R L T (hnodes_snapped4 T NS PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L);
          @data_at_ W Tsh t_devsnap (l_db L); @data_at_ W Tsh t_skbsnap (l_sks L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S hcy5_w0) (l_ss L)] ++
         hcy5_scrB L ++ hcy5_globs gv S FR))).

End AStates.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hcy5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hcy5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
