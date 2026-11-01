(* the shadow model of harness/transport.h and the
   harness's own small functions: representation, specifications, the contexts of their body proofs.

   Functions: draw_steps, draw_nonce (transport_order.c), wm_init, wm_accepts, wm_commit, wm_free, rc_init,
   rc_take, rc_same (transport.h).

   Everything is at the world compspecs W_transport_order: the specifications mention
   the harness structs (wmodel, wacc, rc_snap, noise_replay_counter), whose reptype must compute.  The window
   model is the counter law's (counter_spec.v: cnt_ok, cnt_top', cnt_L', cnt_inv; hcnt_defs3.v: hcnt_prune):
   the harness's list S of accepted nonces is exactly the counter piece's L, pruned as hcnt_prune does.
   Bodies are proved with the EMPTY varspecs ht4o_V0 (no function here reads a global) and the small Gprogs
   below, then lifted into the unit (asm_lib.asm_body_lift).

   Law transport_keepalive has the same transport.h Clight and the same composite list: a copy for it is
   `sed -e s/transport_order/transport_keepalive/g -e s/ht4o_/ht4k_/g` of the ht4o_wm* files (draw_nonce is
   transport_order's only). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.proof.harness.counter.hcnt_defs3.
Require WgNoise.proof.harness.prim_aead.haead_spec3.
Require WgNoise.harness.x_transport_order.code.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

Module TO := WgNoise.harness.x_transport_order.code.

Definition ht4o_twacc := Tstruct TO._wacc noattr.
Definition ht4o_twm := Tstruct TO._wmodel noattr.
Definition ht4o_tsnap := Tstruct TO._rc_snap noattr.
Definition ht4o_trc := Tstruct TO._noise_replay_counter noattr.

(* the window model's pruning (counter law): keep x when x + 1 + W >= top *)
Definition ht4o_prune (top: Z) (S: list Z) : list Z := hcnt_defs3.hcnt_prune top S.

(* ---------------------------------------------------------------------- *)
(* Representation                                                          *)
(* ---------------------------------------------------------------------- *)

(* the accepted set: a NULL-terminated list of malloc'd struct wacc { u64 n; struct wacc *next; } *)
Fixpoint ht4o_wlist (S: list Z) (p: val) : mpred :=
  match S with
  | nil => !! (p = nullval) && emp
  | x :: S' => EX q: val,
      malloc_token Ews ht4o_twacc p * data_at Ews ht4o_twacc (Vlong (Int64.repr x), q) p * ht4o_wlist S' q
  end.

(* struct wmodel { struct wacc *set; u64 top; } at m (share sh) holding the set S and top *)
Definition ht4o_wm (sh: share) (top: Z) (S: list Z) (m: val) : mpred :=
  EX p: val, data_at sh ht4o_twm (p, Vlong (Int64.repr top)) m * ht4o_wlist S p.

(* struct noise_replay_counter { u64 counter; spinlock lock (never written: Vundef); unsigned long backtrack[128]; } *)
Definition ht4o_rc (top: Z) (bm: list Z) : reptype ht4o_trc :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

(* struct rc_snap { u64 counter; unsigned long backtrack[128]; } *)
Definition ht4o_snap (top: Z) (bm: list Z) : reptype ht4o_tsnap :=
  (Vlong (Int64.repr top), map (fun w => Vlong (Int64.repr w)) bm).

Definition ht4o_words (bm: list Z) : Prop :=
  Zlength bm = 128 /\ Forall (fun w => 0 <= w <= Int64.max_unsigned) bm.

(* ---------------------------------------------------------------------- *)
(* Specifications                                                          *)
(* ---------------------------------------------------------------------- *)

(* draw_steps(): any count (STEPS_MAX = SIZE_MAX) *)
Definition ht4o_draw_steps_spec :=
  DECLARE TO._draw_steps
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* draw_nonce(top): any 64-bit value (the distribution is irrelevant to the law) *)
Definition ht4o_draw_nonce_spec :=
  DECLARE TO._draw_nonce
  WITH top: Z
  PRE [ tulong ]
    PROP (0 <= top <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr top)) SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* wm_init(m): the empty model *)
Definition ht4o_wm_init_spec :=
  DECLARE TO._wm_init
  WITH sh: share, m: val
  PRE [ tptr ht4o_twm ]
    PROP (writable_share sh) PARAMS (m) SEP (data_at_ sh ht4o_twm m)
  POST [ tvoid ]
    PROP () RETURN () SEP (ht4o_wm sh 0 [] m).

(* wm_accepts(m, n): the counter law's verdict cnt_ok top S n *)
Definition ht4o_wm_accepts_spec :=
  DECLARE TO._wm_accepts
  WITH sh: share, m: val, top: Z, S: list Z, n: Z
  PRE [ tptr ht4o_twm, tulong ]
    PROP (readable_share sh; 0 <= top <= Int64.max_unsigned; 0 <= n <= Int64.max_unsigned;
          Forall (fun x => 0 <= x <= Int64.max_unsigned) S)
    PARAMS (m; Vlong (Int64.repr n))
    SEP (ht4o_wm sh top S m)
  POST [ tint ]
    PROP () RETURN (Vint (if cnt_ok top S n then Int.one else Int.zero))
    SEP (ht4o_wm sh top S m).

(* wm_commit(m, n) for an accepted n: 0 and nothing changed if malloc fails, else 1, n joins S, top becomes
   max top (n + 1) and the nonces the window has left behind are dropped (freed) *)
Definition ht4o_wm_commit_spec :=
  DECLARE TO._wm_commit
  WITH sh: share, m: val, top: Z, S: list Z, n: Z, gv: globals
  PRE [ tptr ht4o_twm, tulong ]
    PROP (writable_share sh; 0 <= top <= CNT_R; 0 <= n < CNT_R; Forall (fun x => 0 <= x < CNT_R) S)
    PARAMS (m; Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (ht4o_wm sh top S m; mem_mgr gv)
  POST [ tint ] EX b: bool,
    PROP () RETURN (Vint (if b then Int.one else Int.zero))
    SEP (if b then ht4o_wm sh (Z.max top (n + 1)) (ht4o_prune (Z.max top (n + 1)) (n :: S)) m
         else ht4o_wm sh top S m;
         mem_mgr gv).

(* wm_free(m): every node freed, set = NULL *)
Definition ht4o_wm_free_spec :=
  DECLARE TO._wm_free
  WITH sh: share, m: val, top: Z, S: list Z, gv: globals
  PRE [ tptr ht4o_twm ]
    PROP (writable_share sh) PARAMS (m) GLOBALS (gv)
    SEP (ht4o_wm sh top S m; mem_mgr gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh ht4o_twm (nullval, Vlong (Int64.repr top)) m; mem_mgr gv).

(* rc_init(c): counter 0, every bitmap word 0 (the lock is not written) *)
Definition ht4o_rc_init_spec :=
  DECLARE TO._rc_init
  WITH sh: share, c: val
  PRE [ tptr ht4o_trc ]
    PROP (writable_share sh) PARAMS (c) SEP (data_at_ sh ht4o_trc c)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh ht4o_trc (ht4o_rc 0 (Zrepeat 0 128)) c).

(* rc_take(s, c): s := a copy of c's counter and bitmap *)
Definition ht4o_rc_take_spec :=
  DECLARE TO._rc_take
  WITH ssh: share, s: val, csh: share, c: val, top: Z, bm: list Z
  PRE [ tptr ht4o_tsnap, tptr ht4o_trc ]
    PROP (writable_share ssh; readable_share csh; Zlength bm = 128)
    PARAMS (s; c)
    SEP (data_at_ ssh ht4o_tsnap s; data_at csh ht4o_trc (ht4o_rc top bm) c)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh ht4o_tsnap (ht4o_snap top bm) s; data_at csh ht4o_trc (ht4o_rc top bm) c).

(* rc_same(s, c): 1 iff the snapshot equals c's counter and bitmap *)
Definition ht4o_rc_same_spec :=
  DECLARE TO._rc_same
  WITH ssh: share, s: val, top1: Z, bm1: list Z, csh: share, c: val, top2: Z, bm2: list Z
  PRE [ tptr ht4o_tsnap, tptr ht4o_trc ]
    PROP (readable_share ssh; readable_share csh; 0 <= top1 <= Int64.max_unsigned;
          0 <= top2 <= Int64.max_unsigned; ht4o_words bm1; ht4o_words bm2)
    PARAMS (s; c)
    SEP (data_at ssh ht4o_tsnap (ht4o_snap top1 bm1) s; data_at csh ht4o_trc (ht4o_rc top2 bm2) c)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if Z.eq_dec top1 top2 then if list_eq_dec Z.eq_dec bm1 bm2 then Int.one else Int.zero
                  else Int.zero))
    SEP (data_at ssh ht4o_tsnap (ht4o_snap top1 bm1) s; data_at csh ht4o_trc (ht4o_rc top2 bm2) c).

(* ---------------------------------------------------------------------- *)
(* The contexts of the body proofs                                         *)
(* ---------------------------------------------------------------------- *)

Definition ht4o_V0 : varspecs := [].

(* draw_steps: nondet_size; draw_nonce: nondet_u8, nondet_u32, draw_u64 (haead_spec3's, as ht4c) *)
Definition ht4o_G_draw : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; haead_spec3.draw_u64_spec].

(* wm_commit / wm_free: malloc and free of the world *)
Definition ht4o_G_mem : funspecs :=
  [(_quickproof_malloc, @malloc_spec' W_transport_order); (_quickproof_free, @free_spec' W_transport_order)].

(* the specifications of this file *)
Definition ht4o_wm_G : funspecs :=
  [ht4o_draw_steps_spec; ht4o_draw_nonce_spec; ht4o_wm_init_spec; ht4o_wm_accepts_spec; ht4o_wm_commit_spec;
   ht4o_wm_free_spec; ht4o_rc_init_spec; ht4o_rc_take_spec; ht4o_rc_same_spec].
