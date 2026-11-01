(* law keypairs: the harness's own objects and the
   specifications of its list functions.
   - struct mk nodes (hk5_node) in the live list (hk5_mklist), the globals live, s_prev, s_cur, s_next, m_frees,
     m_warn (hk5_items), all at the world compspecs W_keypairs (wg3_worlds.v), the model hkp5_model.v;
   - specifications of mk_unlink, m_get, m_put, pick_live, pick_held, warn_same. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Export WgNoise.proof.harness.keypairs.hkp5_model.
Require WgNoise.contracts.x_keypairs.
Require WgNoise.harness.x_keypairs.code.

Module KC := WgNoise.harness.x_keypairs.code.
Local Open Scope logic.

(* the WHOLE program's variables (main_pre describes every global; VST's main_pre_InitGpred needs each of them
   in main's Delta) *)
Definition hkp5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_keypairs.whole_prog) in exact x).

(* ---------------------------------------------------------------------- *)
(* The harness's objects (W_keypairs)                                      *)
(* ---------------------------------------------------------------------- *)

Section Reps.
#[local] Existing Instance W_keypairs.

Definition t_mk5 := Tstruct KC._mk noattr.

(* struct mk {kp, refs, held, hashed, index, send[32], recv[32], send_valid, recv_valid, initiator,
   remote_index, birth, id, scnt, rcnt, next} *)
Definition hk5_mk_val (M: hk5_mk) (nx: val) : reptype t_mk5 :=
  (m5_kp M, (Vint (m5_refs M), (Vlong (m5_held M), (Val.of_bool (m5_hashed M), (Vint (m5_index M),
   (bytes (m5_send M), (bytes (m5_recv M), (Val.of_bool (m5_sv M), (Val.of_bool (m5_rv M),
   (Val.of_bool (m5_init M), (Vint (m5_rindex M), (Vlong (m5_birth M), (Vlong (m5_id M),
   (Vlong (m5_scnt M), (Vlong (m5_rcnt M), nx))))))))))))))).

(* a node at m (malloc'd by the harness) with contents M and next field nx *)
Definition hk5_node (m: val) (M: hk5_mk) (nx: val) : mpred :=
  !! (Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32) &&
  (data_at Ews t_mk5 (hk5_mk_val M nx) m * malloc_token Ews t_mk5 m).

Definition hk5_head {A: Type} (l: list (val * A)) : val :=
  match l with [] => nullval | (a, _) :: _ => a end.

(* the live list: each node's next field is the next node's address (NULL for the last) *)
Fixpoint hk5_mklist (ML: list (val * hk5_mk)) : mpred :=
  match ML with
  | [] => emp
  | (m, M) :: ML' => hk5_node m M (hk5_head ML') * hk5_mklist ML'
  end.

(* m_warn[5] / warn0[5] (unsigned long) *)
Definition hk5_warr (sh: share) (w: list int64) (a: val) : mpred :=
  !! (Zlength w = 5) && data_at sh (tarray tulong 5) (map Vlong w) a.

(* the dynamic globals of the model: live (+ the list), s_prev, s_cur, s_next, m_frees, m_warn *)
Definition hk5_items (gv: globals) (H: hk5_state) : list mpred :=
  [data_at Ews (tptr t_mk5) (hk5_head (h5_ML H)) (gv KC._live); hk5_mklist (h5_ML H);
   data_at Ews (tptr t_mk5) (h5_sp H) (gv KC._s_prev); data_at Ews (tptr t_mk5) (h5_sc H) (gv KC._s_cur);
   data_at Ews (tptr t_mk5) (h5_sn H) (gv KC._s_next);
   data_at Ews tulong (Vlong (h5_frees H)) (gv KC._m_frees); hk5_warr Ews (h5_warn H) (gv KC._m_warn)].

End Reps.

(* ---------------------------------------------------------------------- *)
(* The specifications of the harness's list functions                      *)
(* ---------------------------------------------------------------------- *)

Section Specs.
#[local] Existing Instance W_keypairs.

(* mk_unlink(k): k leaves the live list (its first occurrence); its memory is handed back *)
Definition hk5_mk_unlink_spec :=
  DECLARE KC._mk_unlink
  WITH gv: globals, ML: list (val * hk5_mk), k: val
  PRE [ tptr t_mk5 ]
    PROP (In k (map fst ML); NoDup (map fst ML))
    PARAMS (k) GLOBALS (gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at Ews (tptr t_mk5) (hk5_head (adel ML k)) (gv KC._live); hk5_mklist (adel ML k);
         data_at_ Ews t_mk5 k; malloc_token Ews t_mk5 k).

(* m_get(k) of a live node: its count per hk5_get_refs, m_warn per hk5_get_warn *)
Definition hk5_m_get_spec :=
  DECLARE KC._m_get
  WITH gv: globals, ML: list (val * hk5_mk), k: val, M: hk5_mk, mw: list int64
  PRE [ tptr t_mk5 ]
    PROP (afind ML k = Some M; NoDup (map fst ML))
    PARAMS (k) GLOBALS (gv)
    SEP (hk5_mklist ML; hk5_warr Ews mw (gv KC._m_warn))
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hk5_mklist (aupd ML k (m5_set_refs M (hk5_get_refs (m5_refs M))));
         hk5_warr Ews (hk5_get_warn (m5_refs M) mw) (gv KC._m_warn)).

(* m_put(k, unref): the model hk5_put (NULL: nothing; else unhash if unref; a saturated count stays and warns;
   else one reference less, at 0 the node is unlinked, freed and counted in m_frees) *)
Definition hk5_m_put_spec :=
  DECLARE KC._m_put
  WITH gv: globals, ML: list (val * hk5_mk), fr: int64, mw: list int64, k: val, unref: bool
  PRE [ tptr t_mk5, tint ]
    PROP (k = nullval \/ In k (map fst ML); NoDup (map fst ML))
    PARAMS (k; Vint (if unref then Int.one else Int.zero)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML;
         data_at Ews tulong (Vlong fr) (gv KC._m_frees); hk5_warr Ews mw (gv KC._m_warn))
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv;
         data_at Ews (tptr t_mk5) (hk5_head (fst (fst (hk5_put k unref ML fr mw)))) (gv KC._live);
         hk5_mklist (fst (fst (hk5_put k unref ML fr mw)));
         data_at Ews tulong (Vlong (snd (fst (hk5_put k unref ML fr mw)))) (gv KC._m_frees);
         hk5_warr Ews (snd (hk5_put k unref ML fr mw)) (gv KC._m_warn)).

(* pick_live(): NULL iff the live list is empty, else any live node *)
Definition hk5_pick_live_spec :=
  DECLARE KC._pick_live
  WITH gv: globals, ML: list (val * hk5_mk)
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML)
  POST [ tptr t_mk5 ] EX k: val,
    PROP ((ML = [] /\ k = nullval) \/ (ML <> [] /\ In k (map fst ML)))
    RETURN (k)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML).

(* pick_held(): NULL iff no live node has a held reference, else any live node with one *)
Definition hk5_pick_held_spec :=
  DECLARE KC._pick_held
  WITH gv: globals, ML: list (val * hk5_mk)
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML)
  POST [ tptr t_mk5 ] EX k: val,
    PROP ((k = nullval /\ Forall (fun x => m5_held (snd x) = Int64.zero) ML) \/
          (exists M, In (k, M) ML /\ m5_held M <> Int64.zero))
    RETURN (k)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML).

(* warn_same(): the shim's warnings w are the initial ones w0 plus the model's mw: returns 1 *)
Definition hk5_warn_same_spec :=
  DECLARE KC._warn_same
  WITH gv: globals, w0: list int64, mw: list int64, w: list int64
  PRE [ ]
    PROP (hk5_warn_ok w0 mw w) PARAMS () GLOBALS (gv)
    SEP (refwarn4 gv w; hk5_warr Ews w0 (gv KC._warn0); hk5_warr Ews mw (gv KC._m_warn))
  POST [ tint ]
    PROP () RETURN (Vint Int.one)
    SEP (refwarn4 gv w; hk5_warr Ews w0 (gv KC._warn0); hk5_warr Ews mw (gv KC._m_warn)).

End Specs.

(* the callees of the list functions (VST: semax_body's function context) *)
Definition hk5_Gm_put : funspecs := [hk5_mk_unlink_spec; (_quickproof_free, @free_spec' W_keypairs)].
Definition hk5_Gpick : funspecs := [nondet_size_spec].
