(* law keypairs: the harness's shadow model as Coq
   data and its relation to the kernel's keypair world (prot_model3: peer slots, live keypairs KS, index table T,
   the refcount_t warnings w of prot_repr4).  Pure Coq.

   Differences to the model:
   - struct mk carries the harness's held references (u64 `held`, no href list), the sending / receiving counters
     and the kernel's count `refs` with refcount_t's saturation (M_INT_MAX, M_SATURATED);
   - m_put / m_get model saturation and the warnings m_warn[5] (REFCOUNT_ADD_NOT_ZERO_OVF, REFCOUNT_SUB_UAF);
   - a node's count is SATURATED (any slots, any held) or = (slots holding it) + held, in 1 .. INT_MAX;
   - a hashed node sits in a slot (so that at the end, after the clear, no live node is hashed);
   - the table's pool also holds the OTHER entries OD (the other peers' handshake entries, the keypairs of the
     other peers: kents), constant, hashed exactly when in OH;
   - the kernel's warnings are the initial ones plus the model's (hk5_warn_ok). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Export WgNoise.proof.protocol4.prot_model4.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The harness's objects                                                    *)
(* ---------------------------------------------------------------------- *)

(* struct mk (keypairs.c), without its next field (the next node's address follows from the list) *)
Record hk5_mk := mkMK5 {
  m5_kp: val; m5_refs: int; m5_held: int64; m5_hashed: bool; m5_index: int;
  m5_send: list byte; m5_recv: list byte; m5_sv: bool; m5_rv: bool; m5_init: bool;
  m5_rindex: int; m5_birth: int64; m5_id: int64; m5_scnt: int64; m5_rcnt: int64 }.

(* the harness's dynamic globals: live (the node list in list order: (node address, contents)),
   s_prev / s_cur / s_next (node addresses or NULL), m_frees, m_warn[5] *)
Record hk5_state := mkH5 {
  h5_ML: list (val * hk5_mk); h5_sp: val; h5_sc: val; h5_sn: val; h5_frees: int64; h5_warn: list int64 }.

(* M_INT_MAX, M_SATURATED (keypairs.c) *)
Definition hk5_INT_MAX : int := Int.repr 2147483647.
Lemma hk5_sat_eq : REFCOUNT_SATURATED = Int.repr 3221225472.
Proof. reflexivity. Qed.

Definition m5_set_refs (M: hk5_mk) (r: int) : hk5_mk :=
  mkMK5 (m5_kp M) r (m5_held M) (m5_hashed M) (m5_index M) (m5_send M) (m5_recv M) (m5_sv M) (m5_rv M)
        (m5_init M) (m5_rindex M) (m5_birth M) (m5_id M) (m5_scnt M) (m5_rcnt M).
Definition m5_set_held (M: hk5_mk) (h: int64) : hk5_mk :=
  mkMK5 (m5_kp M) (m5_refs M) h (m5_hashed M) (m5_index M) (m5_send M) (m5_recv M) (m5_sv M) (m5_rv M)
        (m5_init M) (m5_rindex M) (m5_birth M) (m5_id M) (m5_scnt M) (m5_rcnt M).
Definition m5_unhash (M: hk5_mk) : hk5_mk :=
  mkMK5 (m5_kp M) (m5_refs M) (m5_held M) false (m5_index M) (m5_send M) (m5_recv M) (m5_sv M) (m5_rv M)
        (m5_init M) (m5_rindex M) (m5_birth M) (m5_id M) (m5_scnt M) (m5_rcnt M).
Definition m5_invalidate_send (M: hk5_mk) : hk5_mk :=
  mkMK5 (m5_kp M) (m5_refs M) (m5_held M) (m5_hashed M) (m5_index M) (m5_send M) (m5_recv M) false (m5_rv M)
        (m5_init M) (m5_rindex M) (m5_birth M) (m5_id M) (m5_scnt M) (m5_rcnt M).
Definition m5_set_cnts (M: hk5_mk) (sc rc: int64) : hk5_mk :=
  mkMK5 (m5_kp M) (m5_refs M) (m5_held M) (m5_hashed M) (m5_index M) (m5_send M) (m5_recv M) (m5_sv M) (m5_rv M)
        (m5_init M) (m5_rindex M) (m5_birth M) (m5_id M) sc rc.

Definition h5_set_ML (H: hk5_state) (ML: list (val * hk5_mk)) : hk5_state :=
  mkH5 ML (h5_sp H) (h5_sc H) (h5_sn H) (h5_frees H) (h5_warn H).
Definition h5_set_slots (H: hk5_state) (sp sc sn: val) : hk5_state :=
  mkH5 (h5_ML H) sp sc sn (h5_frees H) (h5_warn H).

(* m_get(k) on the count (keypairs.c): INT_MAX or SATURATED -> SATURATED (warning ADD_NOT_ZERO_OVF), else +1 *)
Definition hk5_get_sat (r: int) : bool := Int.eq r hk5_INT_MAX || Int.eq r REFCOUNT_SATURATED.
Definition hk5_get_refs (r: int) : int := if hk5_get_sat r then REFCOUNT_SATURATED else Int.add r Int.one.
Definition hk5_get_warn (r: int) (mw: list int64) : list int64 :=
  if hk5_get_sat r then warn_bump mw REFCOUNT_ADD_NOT_ZERO_OVF else mw.

(* op 4/5 on node k (contents M): m_get(k) then k->held++ *)
Definition hk5_mget (M: hk5_mk) : hk5_mk :=
  m5_set_held (m5_set_refs M (hk5_get_refs (m5_refs M))) (Int64.add (m5_held M) Int64.one).

(* m_put(k, unref) on the live list, m_frees and m_warn (keypairs.c):
     if (unref) k->hashed = false;
     if (k->refs == M_SATURATED) { m_warn[REFCOUNT_SUB_UAF]++; return; }
     k->refs--; if (k->refs == 0) { mk_unlink(k); free(k); m_frees++; } *)
Definition hk5_put (k: val) (unref: bool) (ML: list (val * hk5_mk)) (fr: int64) (mw: list int64)
  : list (val * hk5_mk) * int64 * list int64 :=
  if eq_dec k nullval then (ML, fr, mw) else
  match afind ML k with
  | None => (ML, fr, mw)
  | Some M =>
    let M1 := if unref then m5_unhash M else M in
    if Int.eq (m5_refs M) REFCOUNT_SATURATED
    then ((if unref then aupd ML k M1 else ML), fr, warn_bump mw REFCOUNT_SUB_UAF)
    else
      let r := Int.sub (m5_refs M) Int.one in
      if Int.eq r Int.zero then (adel ML k, Int64.add fr Int64.one, mw)
      else (aupd ML k (m5_set_refs M1 r), fr, mw)
  end.

(* m_put on the whole harness state *)
Definition hk5_hput (k: val) (unref: bool) (H: hk5_state) : hk5_state :=
  match hk5_put k unref (h5_ML H) (h5_frees H) (h5_warn H) with
  | (ML, fr, mw) => mkH5 ML (h5_sp H) (h5_sc H) (h5_sn H) fr mw
  end.

(* the kernel's refcount_t warnings of the keypair operations: prot_model4.v (kp_get_warn, kp_put_warn and the
   chains add_new_keypair_warn, received_with_keypair_warn, keypairs_clear_warn, begin_session_warn) *)

(* ---------------------------------------------------------------------- *)
(* The relation to the kernel's keypair world of the peer at p             *)
(* ---------------------------------------------------------------------- *)

Definition hk5_eqb (a b: val) : bool := if eq_dec a b then true else false.

(* the keypair a slot's node stands for (NULL for NULL) *)
Definition hk5_slot_kp (ML: list (val * hk5_mk)) (m: val) : val :=
  if eq_dec m nullval then nullval else match afind ML m with Some M => m5_kp M | None => nullval end.

Definition hk5_slots (H: hk5_state) : list val := [h5_sp H; h5_sc H; h5_sn H].

Definition hk5_nonnull (l: list val) : list val := filter (fun x => negb (hk5_eqb x nullval)) l.

(* the slot references to node m in the reference list R *)
Definition hk5_cnt (R: list val) (m: val) : Z := Zlength (filter (hk5_eqb m) R).

Fixpoint hk5_remove1 (m: val) (R: list val) : list val :=
  match R with [] => [] | x :: R' => if eq_dec x m then R' else x :: hk5_remove1 m R' end.

(* a node's count: saturated (then anything else goes: never freed), or the slot references R to it plus its held
   references, between 1 and INT_MAX *)
Definition hk5_count_ok (R: list val) (m: val) (M: hk5_mk) : Prop :=
  m5_refs M = REFCOUNT_SATURATED \/
  (Int.unsigned (m5_refs M) = hk5_cnt R m + Int64.unsigned (m5_held M) /\
   1 <= Int.unsigned (m5_refs M) <= Int.max_signed).

(* a node and its keypair: every field check_all compares, the entry in the table's pool (share Ews, peer p,
   type KEYPAIR, the node's index) and its table membership *)
Definition hk5_match (p: val) (T: tstate) (M: hk5_mk) (K: keypair) : Prop :=
  kp_refs K = m5_refs M /\
  sfind (t_D T) (m5_kp M) = Some (Ews, mkEntry p IDX_KEYPAIR (m5_index M)) /\
  vin (m5_kp M) (t_L T) = m5_hashed M /\
  kp_send K = mkSym (m5_send M) (m5_birth M) (m5_sv M) /\
  kp_recv K = mkSym (m5_recv M) (m5_birth M) (m5_rv M) /\
  kp_init K = m5_init M /\ kp_rindex K = m5_rindex M /\ kp_id K = m5_id M /\
  kp_scounter K = m5_scnt M /\ kp_rcounter K = m5_rcnt M.

(* the pool of T: P's handshake entry (share Tsh: the harness's local peer; peer p, type HANDSHAKE), P's live
   keypairs' entries, and the other entries OD (constant; hashed exactly when in OH); every index in the table
   once; the table well formed *)
Definition hk5_pool (p: val) (OD: list (val * share * entry)) (OH: list val) (KS: list (val * keypair))
  (T: tstate) : Prop :=
  (forall a, In a (saddrs (t_D T)) <-> a = hs_addr p \/ In a (map fst KS) \/ In a (saddrs OD)) /\
  ~ In (hs_addr p) (map fst KS) /\ ~ In (hs_addr p) (saddrs OD) /\
  (forall a, In a (map fst KS) -> ~ In a (saddrs OD)) /\
  (exists idx, sfind (t_D T) (hs_addr p) = Some (Tsh, mkEntry p IDX_HANDSHAKE idx)) /\
  Forall (fun x => match x with (a, sh, E) => sfind (t_D T) a = Some (sh, E) /\ vin a (t_L T) = vin a OH end) OD /\
  NoDup (t_indices T (t_L T)) /\ itable_wf T.

(* the relation under a reference list R (the slots, possibly a temporary in the middle of a rotation) *)
Definition hk5_core (p: val) (OD: list (val * share * entry)) (OH: list val) (R: list val)
  (ML: list (val * hk5_mk)) (KS: list (val * keypair)) (T: tstate) : Prop :=
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS /\
  NoDup (map fst ML) /\ ~ In nullval (map fst ML) /\
  NoDup (map fst KS) /\ ~ In nullval (map fst KS) /\
  Forall (fun m => m = nullval \/ In m (map fst ML)) R /\
  Forall (fun x => hk5_count_ok R (fst x) (snd x)) ML /\
  Forall (fun x => m5_hashed (snd x) = true -> In (fst x) R) ML /\
  hk5_pool p OD OH KS T.

(* H (the harness) against the kernel's peer P (slots), live keypairs KS and table T of the peer at p: the core
   under the three slots, the non-NULL slots pairwise distinct, P's slots the slots' keypairs *)
Definition hk5_rel (p: val) (OD: list (val * share * entry)) (OH: list val) (H: hk5_state) (P: peer)
  (KS: list (val * keypair)) (T: tstate) : Prop :=
  hk5_core p OD OH (hk5_slots H) (h5_ML H) KS T /\
  NoDup (hk5_nonnull (hk5_slots H)) /\
  p_prev P = hk5_slot_kp (h5_ML H) (h5_sp H) /\ p_cur P = hk5_slot_kp (h5_ML H) (h5_sc H) /\
  p_next P = hk5_slot_kp (h5_ML H) (h5_sn H).

(* the kernel's warnings w = the initial ones w0 + the model's mw (unsigned long, wrapping); the model never
   counts ADD_OVF, ADD_UAF, DEC_LEAK *)
Definition hk5_warn_ok (w0 mw w: list int64) : Prop :=
  Zlength w0 = 5 /\ Zlength mw = 5 /\ Zlength w = 5 /\
  (forall i, 0 <= i < 5 -> Znth i w = Int64.add (Znth i w0) (Znth i mw)) /\
  Znth REFCOUNT_ADD_OVF mw = Int64.zero /\ Znth REFCOUNT_ADD_UAF mw = Int64.zero /\
  Znth REFCOUNT_DEC_LEAK mw = Int64.zero.

(* ---------------------------------------------------------------------- *)

(* hkp5_lem_*.v); the segment lemmas take hkp5_model_facts as a hypothesis *)
(* ---------------------------------------------------------------------- *)

(* the shared specifications' preconditions and the node <-> keypair correspondence *)
Definition hk5_fact_pre : Prop :=
  forall p OD OH R ML KS T,
  hk5_core p OD OH R ML KS T ->
  kps_in_pool T p KS /\ hs_in_pool T p /\
  (forall m M, afind ML m = Some M -> exists K, afind KS (m5_kp M) = Some K /\ hk5_match p T M K) /\
  (forall m, In m (map fst ML) -> hk5_slot_kp ML m <> nullval /\ In (hk5_slot_kp ML m) (map fst KS)) /\
  (forall m1 m2, In m1 (map fst ML) -> m2 = nullval \/ In m2 (map fst ML) ->
     hk5_slot_kp ML m1 = hk5_slot_kp ML m2 -> m1 = m2).

Definition hk5_fact_slots : Prop :=
  forall p OD OH H P KS T, hk5_rel p OD OH H P KS T -> slots_ok P KS.

(* the core does not depend on the order of R, only on its non-NULL counts *)
Definition hk5_fact_perm : Prop :=
  forall p OD OH R R' ML KS T,
  (forall m, m <> nullval -> hk5_cnt R m = hk5_cnt R' m) ->
  Forall (fun m => m = nullval \/ In m (map fst ML)) R' ->
  hk5_core p OD OH R ML KS T -> hk5_core p OD OH R' ML KS T.

(* a slot reference to node m goes (m_put(m, 1) on the harness's side, wg_noise_keypair_put(m's keypair, true)
   on the kernel's: a slot is always dropped with unreference_now): the core under R minus that reference; the
   warnings move together; a free on both sides or on neither *)
Definition hk5_fact_put : Prop :=
  forall p OD OH R ML KS T S fr mw w0 w m,
  hk5_core p OD OH R ML KS T -> hk5_warn_ok w0 mw w -> In m R -> m <> nullval ->
  let '(ML', fr', mw') := hk5_put m true ML fr mw in
  let k := hk5_slot_kp ML m in
  let W' := kp_put k true (mkKW KS T S) in
  hk5_core p OD OH (hk5_remove1 m R) ML' (kw_KS W') (kw_T W') /\
  hk5_warn_ok w0 mw' (kp_put_warn k KS w) /\
  ((kw_S W' = S /\ fr' = fr /\ Zlength ML' = Zlength ML) \/
   (kw_S W' = shim_free S /\ fr' = Int64.add fr Int64.one /\ Zlength ML' = Zlength ML - 1 /\
    ~ In m (map fst ML') /\ ~ In m (hk5_remove1 m R))).

(* a held reference to node m goes (op 6, the end: k->held--, then wg_noise_keypair_put and m_put) *)
Definition hk5_fact_put_held : Prop :=
  forall p OD OH R ML KS T S fr mw w0 w m M unref,
  hk5_core p OD OH R ML KS T -> hk5_warn_ok w0 mw w -> afind ML m = Some M ->
  Int64.unsigned (m5_held M) > 0 ->
  let ML1 := aupd ML m (m5_set_held M (Int64.sub (m5_held M) Int64.one)) in
  let '(ML', fr', mw') := hk5_put m unref ML1 fr mw in
  let k := m5_kp M in
  let W' := kp_put k unref (mkKW KS T S) in
  hk5_core p OD OH R ML' (kw_KS W') (kw_T W') /\
  hk5_warn_ok w0 mw' (kp_put_warn k KS w) /\
  ((kw_S W' = S /\ fr' = fr /\ Zlength ML' = Zlength ML) \/
   (kw_S W' = shim_free S /\ fr' = Int64.add fr Int64.one /\ Zlength ML' = Zlength ML - 1 /\
    ~ In m (map fst ML') /\ ~ In m R)).

(* a new reference to the live node m (op 4/5: wg_noise_keypair_get, m_get, k->held++) *)
Definition hk5_fact_get : Prop :=
  forall p OD OH R ML KS T mw w0 w m M,
  hk5_core p OD OH R ML KS T -> hk5_warn_ok w0 mw w -> afind ML m = Some M ->
  fst (kp_get (m5_kp M) KS) = m5_kp M /\
  hk5_core p OD OH R (aupd ML m (hk5_mget M)) (snd (kp_get (m5_kp M) KS)) T /\
  hk5_warn_ok w0 (hk5_get_warn (m5_refs M) mw) (kp_get_warn (m5_kp M) KS w).

Definition hkp5_model_facts : Prop :=
  hk5_fact_pre /\ hk5_fact_slots /\ hk5_fact_perm /\ hk5_fact_put /\ hk5_fact_put_held /\ hk5_fact_get.
