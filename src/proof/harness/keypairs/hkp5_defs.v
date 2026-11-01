(* law keypairs: main's loop states and the statements of the
   loop-body segments.
   The loop body (hkp5_cut.v) = L0 ; IFC ; LC with IFC dispatching on op to Op0 Op1 Op2 Op3 Op7 Op45 Op6.
   Every segment is a semax in its OWN small context (hkp5_Delta G: main's function with the callee specs G it
   calls; the glue lifts it to main's whole context by semax_Delta_subsumption / func_tycontext_sub).
   The state: the kernel's objects of P (device, table, peer, keypairs), main's locals, the harness's model
   (hk5_items), the snapshots hsm / prm and the constants warn0 / prefs, the shim with its EXACT warnings
   (shim_state4), noise's globals, and a frame FR (the other peers, their keypairs, dsm, the other / kes globals:
   constant during the loop; only Op1's foreign branch and LC read them, stated with the common.h v2 layer). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Export WgNoise.proof.harness.keypairs.hkp5_reps.
Require Export WgNoise.proof.harness.keypairs.hkp5_cut.
Require Export WgNoise.proof.harness.keypairs.hkp5_zfspec.

Module P4 := WgNoise.proof.protocol4.prot_specs4.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* replay_counter_fresh (common.h): a fresh replay window                   *)
(* ---------------------------------------------------------------------- *)

Definition hk5_t_rc := Tstruct KC._noise_replay_counter noattr.

(* struct noise_replay_counter {counter; lock; backtrack[128]} as keypair_rep holds it (Noise.CS) *)
Definition hk5_rcf_spec :=
  DECLARE KC._replay_counter_fresh
  WITH sh: share, c: val, rc: int64, lk: val, bt: list int64
  PRE [ tptr hk5_t_rc ]
    PROP (readable_share sh; Zlength bt = 128) PARAMS (c)
    SEP (@data_at Noise.CS sh hk5_t_rc (Vlong rc, (lk, map Vlong bt)) c)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if andb (Int64.eq rc Int64.zero) (forallb (fun x => Int64.eq x Int64.zero) bt) then Int.one
                  else Int.zero))
    SEP (@data_at Noise.CS sh hk5_t_rc (Vlong rc, (lk, map Vlong bt)) c).

(* ---------------------------------------------------------------------- *)
(* The fixed part of the run                                               *)
(* ---------------------------------------------------------------------- *)

#[local] Existing Instance W_keypairs.

(* the globals and main's local variables *)
Record hkp5_fix := mkKF5 {
  f_gv: globals; f_w: val; f_t: val; f_pt: val; f_p: val; f_raw: val; f_pub: val; f_snap: val; f_opub: val;
  f_first: val; f_second: val }.

Definition hkp5_lvars (F: hkp5_fix) : list localdef :=
  [lvar KC._w (Tstruct KC._wg_device noattr) (f_w F); lvar KC._t (Tstruct KC._index_hashtable noattr) (f_t F);
   lvar KC._pt (Tstruct KC._pubkey_hashtable noattr) (f_pt F); lvar KC._p (Tstruct KC._wg_peer noattr) (f_p F);
   lvar KC._raw (tarray tuchar 32) (f_raw F); lvar KC._pub (tarray tuchar 32) (f_pub F);
   lvar KC._snap (Tstruct KC._hs_snap noattr) (f_snap F); lvar KC._opub (tarray tuchar 32) (f_opub F);
   lvar KC._first (tarray tuchar 32) (f_first F); lvar KC._second (tarray tuchar 32) (f_second F);
   gvars (f_gv F)].

(* the values fixed by the prologue: the device's raw key, P's public key, the cookie secret setup_device drew,
   the boot clock at setup; the allocation / free counters and the warnings at the loop's start (allocs0, frees0,
   warn0); the other pool entries (the other peers' handshake entries, the kents' keypair entries) and the hashed
   ones; the public-key table's head; P's reference count (prefs) *)
Record hkp5_val := mkKV5 {
  v_RAW: list byte; v_PUB: list byte; v_sec: list byte; v_boot: int64; v_allocs0: int64; v_frees0: int64;
  v_w0: list int64; v_OD: list (val * share * entry); v_OH: list val; v_head: val; v_prefs: int }.

Definition hkp5_fix_ok (F: hkp5_fix) (V: hkp5_val) : Prop :=
  Zlength (v_RAW V) = 32 /\ Zlength (v_PUB V) = 32 /\ Zlength (v_sec V) = 32 /\ Zlength (v_w0 V) = 5.

(* the loop's state: the shim and its warnings, keypair_counter, the peer, the live keypairs, the table, the
   harness's model, the clock now, next_id, id_known, the snapshot in hsm *)
Record hkp5_dyn := mkKY5 {
  y_S: shim; y_w: list int64; y_kc: int64; y_P: peer; y_KS: list (val * keypair); y_T: tstate; y_H: hk5_state;
  y_now: int64; y_next_id: int64; y_id_known: bool; y_hsn: hsnap }.

(* struct ck_snap / pr_snap values (W_keypairs): prm = the rest of P (its slots as pr_take found them: NULL) *)
Definition hk5_ck_val (C: cookie) : reptype (Tstruct KC._ck_snap noattr) :=
  (Vlong (ck_birth C), (Val.of_bool (ck_valid C), (bytes (ck_cookie C), (Val.of_bool (ck_sent C),
   (bytes (ck_last_mac1 C), (bytes (ck_dkey C), bytes (ck_mkey C))))))).
Definition hk5_prsnap_val (P: peer) : reptype (Tstruct KC._pr_snap noattr) :=
  (p_device P, (Val.of_bool (p_dead P), (nullval, (nullval, (nullval, (Vlong (p_lsh P),
   (hk5_ck_val (p_cookie P), (Vlong (p_id P), p_pknext P)))))))).

(* hsm holds a snapshot of P's handshake: equal to the current one but (possibly) its entry's next field *)
Definition hk5_hsm_ok (p: val) (T: tstate) (P: peer) (sn: hsnap) : Prop :=
  t_entry T (hs_addr p) = Some (sn_entry sn) /\ sn_hashed sn = vin (hs_addr p) (t_L T) /\ sn_hs sn = p_hs P.

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.

(* the device as setup_device made it *)
Definition hkp5_D (F: hkp5_fix) (V: hkp5_val) : device :=
  setup_dev x25519 (f_w F) (f_t F) (f_pt F) (v_RAW V) (v_sec V) (v_boot V).

(* the invariant: the model against the kernel (hk5_rel, the warnings); P's device, static identity and count;
   frees (m_frees) and allocations (live nodes) counted (unsigned long); next_id is keypair_counter + 1 once
   known; the clock below 2^62; hsm a snapshot of P's handshake; P's public-key link NULL (P is the first peer of
   the device's public-key table: rest_same compares the link with itself) *)
Definition hkp5_inv (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) : Prop :=
  hk5_rel (f_p F) (v_OD V) (v_OH V) (y_H Y) (y_P Y) (y_KS Y) (y_T Y) /\
  hk5_warn_ok (v_w0 V) (h5_warn (y_H Y)) (y_w Y) /\
  p_device (y_P Y) = f_w F /\ hs_sid (p_hs (y_P Y)) = id_addr (f_w F) /\ p_refs (y_P Y) = v_prefs V /\
  Int64.sub (s_frees (y_S Y)) (v_frees0 V) = h5_frees (y_H Y) /\
  Int64.sub (s_allocs (y_S Y)) (v_allocs0 V) =
    Int64.add (h5_frees (y_H Y)) (Int64.repr (Zlength (h5_ML (y_H Y)))) /\
  (y_id_known Y = true -> y_next_id Y = Int64.add (y_kc Y) Int64.one) /\
  Int64.unsigned (y_now Y) < 2 ^ 62 /\
  hk5_hsm_ok (f_p F) (y_T Y) (y_P Y) (y_hsn Y) /\
  p_pknext (y_P Y) = nullval.

(* the temps fixed during the loop (i excepted) *)
Definition hkp5_temps (V: hkp5_val) (Y: hkp5_dyn) (steps: Z) : list localdef :=
  [temp KC._steps (Vlong (Int64.repr steps)); temp KC._now (Vlong (y_now Y));
   temp KC._next_id (Vlong (y_next_id Y));
   temp KC._id_known (Vint (if y_id_known Y then Int.one else Int.zero));
   temp KC._allocs0 (Vlong (v_allocs0 V)); temp KC._frees0 (Vlong (v_frees0 V))].

(* main's locals and the kernel objects *)
Definition hkp5_world (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) : list mpred :=
  [device_rep Tsh (f_w F) (hkp5_D F V); itable Tsh (f_t F) (y_T Y); ptable Tsh (f_pt F) (v_head V);
   peer_rep Tsh (f_p F) (y_P Y); keypairs_rep W_keypairs (y_KS Y);
   hbytes Tsh (v_RAW V) (f_raw F); hbytes Tsh (v_PUB V) (f_pub F);
   @data_at_ HCS Tsh t_hsnap (f_snap F); hout Tsh 32 (f_opub F); hout Tsh 32 (f_first F); hout Tsh 32 (f_second F)].

(* the harness's snapshots and constants: hsm, prm, warn0, prefs *)
Definition hkp5_hglobs (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) : list mpred :=
  [@data_at HCS Ews t_hsnap (hsnap_val (y_hsn Y)) (f_gv F KC._hsm);
   data_at Ews (Tstruct KC._pr_snap noattr) (hk5_prsnap_val (y_P Y)) (f_gv F KC._prm);
   hk5_warr Ews (v_w0 V) (f_gv F KC._warn0); data_at Ews tuint (Vint (v_prefs V)) (f_gv F KC._prefs)].

Definition hkp5_globs (gv: globals) (S: shim) (w: list int64) (kc: int64) : list mpred :=
  [shim_state4 gv S w; noise_globals gv kc; wg_consts gv; mem_mgr gv].

Definition hkp5_SEP (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) (FR: mpred) : list mpred :=
  hkp5_world F V Y ++ hk5_items (f_gv F) (y_H Y) ++ hkp5_hglobs F V Y ++
  hkp5_globs (f_gv F) (y_S Y) (y_w Y) (y_kc Y) ++ [FR].

(* the loop state at iteration i (Pi: the bound on i) *)
Definition hkp5_St (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (Pi: Prop) (i: Z) (Y: hkp5_dyn)
  : environ -> mpred :=
  PROPx [Pi; hkp5_fix_ok F V; hkp5_inv F V Y; 0 <= steps <= Int64.max_unsigned]
  (LOCALx (temp KC._i (Vlong (Int64.repr i)) :: hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP F V Y FR))).

(* the loop invariant (before the test i < steps), and the state at the end of an iteration / at a continue
   (before i++) *)
Definition hkp5_Inv F V steps FR : environ -> mpred :=
  EX i: Z, EX Y: hkp5_dyn, hkp5_St F V steps FR (0 <= i <= steps) i Y.
Definition hkp5_Icont F V steps FR (i: Z) : environ -> mpred :=
  EX Y: hkp5_dyn, hkp5_St F V steps FR (0 <= i < steps) i Y.

(* after L0: op drawn (0..7), the clock moved and set in the shim *)
Definition hkp5_PL0 F V steps FR (i op: Z) : environ -> mpred :=
  EX Y: hkp5_dyn,
  PROPx [0 <= i < steps; hkp5_fix_ok F V; hkp5_inv F V Y; 0 <= steps <= Int64.max_unsigned;
         0 <= op < 8; s_boot (y_S Y) = y_now Y]
  (LOCALx (temp KC._op (Vint (Int.repr op)) :: temp KC._i (Vlong (Int64.repr i)) ::
           hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP F V Y FR))).

End Ctx.

(* ---------------------------------------------------------------------- *)
(* The segments' contexts                                                  *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_Delta (G: funspecs) : tycontext := func_tycontext KC.f_main hkp5_V G [].

Definition hkp5_malloc : ident * funspec := (_quickproof_malloc, @malloc_spec' W_keypairs).
Definition hkp5_free : ident * funspec := (_quickproof_free, @free_spec' W_keypairs).

Definition hkp5_G_L0 : funspecs := [nondet_u8_spec; draw_u64_spec].

Definition hkp5_G_Op0 : funspecs :=
  [hkp5_malloc; hkp5_free; nondet_u8_spec; hs_randomize_spec; P4.wg_index_hashtable_insert_spec;
   hs_take_spec; P4.wg_noise_handshake_begin_session_spec W_keypairs; hs_same_spec; check_failed_spec;
   m_transport_spec KC._x_keypairs__M_BASEPOINT; hk5_zf_spec; hk5_rcf_spec; bytes_copy_spec; hk5_m_put_spec].

Definition hkp5_G_Op2 : funspecs :=
  [hs_take_spec; P4.wg_noise_expire_current_peer_keypairs_spec W_keypairs; hk5_zf_spec; check_failed_spec].

Definition hkp5_G_Op3 : funspecs := [P4.wg_noise_keypairs_clear_spec W_keypairs; hk5_m_put_spec].

Definition hkp5_G_Op7 : funspecs := [hk5_pick_live_spec; draw_u64_spec].

Definition hkp5_G_Op45 : funspecs :=
  [nondet_u8_spec; hk5_pick_live_spec; P4.wg_noise_keypair_get_spec W_keypairs; check_failed_spec; hk5_m_get_spec].

Definition hkp5_G_Op6 : funspecs :=
  [nondet_u8_spec; hk5_pick_held_spec; P4.wg_noise_keypair_put_spec W_keypairs; hk5_m_put_spec].

(* prm's snapshot determines P's public-key link *)
Lemma hk5_prsnap_val_pknext (P1 P2: peer) :
  hk5_prsnap_val P1 = hk5_prsnap_val P2 -> p_pknext P1 = p_pknext P2.
Proof.
  unfold hk5_prsnap_val. intros E.
  change (reptype (Tstruct KC._pr_snap noattr)) with
    (val * (val * (val * (val * (val * (val * (reptype (Tstruct KC._ck_snap noattr) * (val * val))))))))%type in E.
  inversion E. reflexivity.
Qed.
