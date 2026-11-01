(* nb port of the hc4b_ke_add_defs.v.: shared definitions of the proof of
   hc4_body_kents_add: the body's Delta, the Clight segments (verbatim from src/harness/cookie_mac/code.v
   f_kents_add), the LOCALs of the loop body after `kp = &k->kp; owner = ...`, the raw pieces of a fresh struct
   kent, the slot invariant. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Module HC := WgNoise.harness.x_cookie_mac.code.

(* the world's compspecs, hidden from typeclass resolution *)
Definition hc4nb2_ke_add_csw := compspecs.
#[export] Typeclasses Opaque hc4nb2_ke_add_csw.

Definition hc4nb2_ke_add_Delta (CSw: hc4nb2_ke_add_csw) : tycontext :=
  func_tycontext HC.f_kents_add [] (hc4nb_G_kents_add CSw) nil.

(* the temps of the loop body once kp and owner are set *)
Definition hc4nb2_ke_add_locs (l k n i owner tab peers p: val) (fl: int) (gv: globals) : list localdef :=
  [temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i; temp HC._owner owner; temp HC._kp k;
   gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl)].

(* segment C: from nondet_bytes(kp->sending.key, 32) to kp->internal_id = draw_u64(), then `rest` *)
Definition hc4nb2_ke_add_sC (rest: statement) : statement :=
  (Ssequence (Scall None (Evar HC._nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid cc_default)) ((Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._sending (Tstruct HC._noise_symmetric_key noattr)) HC._key (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)) (Ssequence (Ssequence (Scall (Some HC._t'7) (Evar HC._draw_boottime (Tfunction nil tulong cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._sending (Tstruct HC._noise_symmetric_key noattr)) HC._birthdate tulong) (Etempvar HC._t'7 tulong))) (Ssequence (Ssequence (Scall (Some HC._t'8) (Evar HC._nondet_u8 (Tfunction nil tuchar cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._sending (Tstruct HC._noise_symmetric_key noattr)) HC._is_valid tbool) (Ebinop Oand (Etempvar HC._t'8 tuchar) (Econst_int (Int.repr 1) tint) tint))) (Ssequence (Scall None (Evar HC._nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid cc_default)) ((Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._receiving (Tstruct HC._noise_symmetric_key noattr)) HC._key (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)) (Ssequence (Ssequence (Scall (Some HC._t'9) (Evar HC._draw_boottime (Tfunction nil tulong cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._receiving (Tstruct HC._noise_symmetric_key noattr)) HC._birthdate tulong) (Etempvar HC._t'9 tulong))) (Ssequence (Ssequence (Scall (Some HC._t'10) (Evar HC._nondet_u8 (Tfunction nil tuchar cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._receiving (Tstruct HC._noise_symmetric_key noattr)) HC._is_valid tbool) (Ebinop Oand (Etempvar HC._t'10 tuchar) (Econst_int (Int.repr 1) tint) tint))) (Ssequence (Ssequence (Scall (Some HC._t'11) (Evar HC._draw_u64 (Tfunction nil tulong cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._sending_counter (Tstruct HC.___gp_atomic64_t noattr)) HC._counter tlong) (Ecast (Etempvar HC._t'11 tulong) tlong))) (Ssequence (Ssequence (Scall (Some HC._t'12) (Evar HC._draw_u64 (Tfunction nil tulong cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._receiving_counter (Tstruct HC._noise_replay_counter noattr)) HC._counter tulong) (Etempvar HC._t'12 tulong))) (Ssequence (Ssequence (Sset HC._j (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar HC._j tulong) (Ebinop Odiv (Econst_int (Int.repr 8192) tint) (Econst_int (Int.repr 64) tint) tint) tint) Sskip Sbreak) (Ssequence (Scall (Some HC._t'13) (Evar HC._draw_u64 (Tfunction nil tulong cc_default)) nil) (Sassign (Ederef (Ebinop Oadd (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._receiving_counter (Tstruct HC._noise_replay_counter noattr)) HC._backtrack (tarray tulong 128)) (Etempvar HC._j tulong) (tptr tulong)) tulong) (Ecast (Etempvar HC._t'13 tulong) tulong)))) (Sset HC._j (Ebinop Oadd (Etempvar HC._j tulong) (Econst_int (Int.repr 1) tint) tulong)))) (Ssequence (Ssequence (Scall (Some HC._t'14) (Evar HC._nondet_u32 (Tfunction nil tuint cc_default)) nil) (Sassign (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._remote_index tuint) (Etempvar HC._t'14 tuint))) (Ssequence (Ssequence (Scall (Some HC._t'15) (Evar HC._nondet_u8 (Tfunction nil tuchar cc_default)) nil) (Sassign (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._i_am_the_initiator tbool) (Ebinop Oand (Etempvar HC._t'15 tuchar) (Econst_int (Int.repr 1) tint) tint))) (Ssequence (Ssequence (Scall (Some HC._t'16) (Evar HC._draw_peer_refs (Tfunction nil tuint cc_default)) nil) (Sassign (Efield (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._refcount (Tstruct HC._kref noattr)) HC._refcount tuint) (Etempvar HC._t'16 tuint))) (Ssequence (Ssequence (Scall (Some HC._t'17) (Evar HC._draw_u64 (Tfunction nil tulong cc_default)) nil) (Sassign (Efield (Ederef (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr))) (Tstruct HC._noise_keypair noattr)) HC._internal_id tulong) (Etempvar HC._t'17 tulong))) rest))))))))))))).

(* the fill: if (fill) switch (nondet_u8() % 4) { ... } *)
Definition hc4nb2_ke_add_sD : statement :=
  (Sifthenelse (Etempvar HC._fill tint) (Ssequence (Scall (Some HC._t'18) (Evar HC._nondet_u8 (Tfunction nil tuchar cc_default)) nil) (Sswitch (Ebinop Omod (Etempvar HC._t'18 tuchar) (Econst_int (Int.repr 4) tint) tint) (LScons (Some 0) (Ssequence (Ssequence (Sset HC._t'21 (Efield (Efield (Ederef (Etempvar HC._owner (tptr (Tstruct HC._wg_peer noattr))) (Tstruct HC._wg_peer noattr)) HC._keypairs (Tstruct HC._noise_keypairs noattr)) HC._current_keypair (tptr (Tstruct HC._noise_keypair noattr)))) (Sifthenelse (Ebinop Oeq (Etempvar HC._t'21 (tptr (Tstruct HC._noise_keypair noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Sassign (Efield (Efield (Ederef (Etempvar HC._owner (tptr (Tstruct HC._wg_peer noattr))) (Tstruct HC._wg_peer noattr)) HC._keypairs (Tstruct HC._noise_keypairs noattr)) HC._current_keypair (tptr (Tstruct HC._noise_keypair noattr))) (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr)))) Sskip)) Sbreak) (LScons (Some 1) (Ssequence (Ssequence (Sset HC._t'20 (Efield (Efield (Ederef (Etempvar HC._owner (tptr (Tstruct HC._wg_peer noattr))) (Tstruct HC._wg_peer noattr)) HC._keypairs (Tstruct HC._noise_keypairs noattr)) HC._previous_keypair (tptr (Tstruct HC._noise_keypair noattr)))) (Sifthenelse (Ebinop Oeq (Etempvar HC._t'20 (tptr (Tstruct HC._noise_keypair noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Sassign (Efield (Efield (Ederef (Etempvar HC._owner (tptr (Tstruct HC._wg_peer noattr))) (Tstruct HC._wg_peer noattr)) HC._keypairs (Tstruct HC._noise_keypairs noattr)) HC._previous_keypair (tptr (Tstruct HC._noise_keypair noattr))) (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr)))) Sskip)) Sbreak) (LScons (Some 2) (Ssequence (Ssequence (Sset HC._t'19 (Efield (Efield (Ederef (Etempvar HC._owner (tptr (Tstruct HC._wg_peer noattr))) (Tstruct HC._wg_peer noattr)) HC._keypairs (Tstruct HC._noise_keypairs noattr)) HC._next_keypair (tptr (Tstruct HC._noise_keypair noattr)))) (Sifthenelse (Ebinop Oeq (Etempvar HC._t'19 (tptr (Tstruct HC._noise_keypair noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Sassign (Efield (Efield (Ederef (Etempvar HC._owner (tptr (Tstruct HC._wg_peer noattr))) (Tstruct HC._wg_peer noattr)) HC._keypairs (Tstruct HC._noise_keypairs noattr)) HC._next_keypair (tptr (Tstruct HC._noise_keypair noattr))) (Etempvar HC._kp (tptr (Tstruct HC._noise_keypair noattr)))) Sskip)) Sbreak) (LScons None Sbreak LSnil)))))) Sskip).

(* k->next = l; l = k; *)
Definition hc4nb2_ke_add_sL : statement :=
  (Ssequence (Sassign (Efield (Ederef (Etempvar HC._k (tptr (Tstruct HC._kent noattr))) (Tstruct HC._kent noattr)) HC._next (tptr (Tstruct HC._kent noattr))) (Etempvar HC._l (tptr (Tstruct HC._kent noattr)))) (Sset HC._l (Etempvar HC._k (tptr (Tstruct HC._kent noattr))))).

(* the keypair of a fresh kent at k, but its entry: kp_body_rep's fields, uninitialized *)
Definition hc4nb2_ke_add_body0 (k: val) : mpred :=
  @field_at_ Noise.CS Ews t_kp [StructField I._sending] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._sending_counter] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._receiving] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._receiving_counter] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._remote_index] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._i_am_the_initiator] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._refcount] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._rcu] k *
  @field_at_ Noise.CS Ews t_kp [StructField I._internal_id] k *
  spacer Ews 1181 1184 k.

(* the slots of the peers: NULL or addresses `own` (the pool of the index table: valid pointers) *)
Definition hc4nb2_ke_add_slots_ok (own: list val) (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (_, _, P) => Forall (vp_ok own) [p_cur P; p_prev P; p_next P] end) PS.
