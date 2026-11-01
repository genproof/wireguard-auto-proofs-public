(* The counter piece's model and specifications.

   Model (harness/counter.c): the list L of accepted nonces and top = 1 + the largest accepted one (0 if none).
   Nonce n is accepted exactly when cnt_ok top L n; then n joins L and top becomes max top (n + 1).

   The bitmap backtrack[128] (u64 words, as Z) represents L inside the window: bit t (t = n + 1) is bit t mod 64
   of word (t / 64) mod 128.  Invariant cnt_inv top L bm:
   - the EXACT window [top - W, top] of t values agrees with L (bit t set iff t - 1 in L);
   - the bits above top in top's own word are clear;
   - L's elements are in [0, top), top <= R.
   L is only constrained inside the window: a client may drop (or keep) nonces older than the window
   (cnt_inv_prune).  The specifications are stated in Counter.CS; a caller in another compspecs converts
   its data_at of struct noise_replay_counter. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require WgNoise.counter.code.

#[local] Existing Instance WgNoise.units.Counter.CS.

Definition _quickproof_ilog2 : ident := WgNoise.counter.code._quickproof_ilog2.
Definition _test_and_set_bit : ident := WgNoise.counter.code._test_and_set_bit.
Definition _counter_validate : ident := WgNoise.counter.code._counter_validate.
Definition _wg_counter_validate : ident := WgNoise.counter.code._wg_counter_validate.
Definition _noise_replay_counter : ident := WgNoise.counter.code._noise_replay_counter.

(* W = COUNTER_WINDOW_SIZE, R = REJECT_AFTER_MESSAGES, as in the harness *)
Definition CNT_W : Z := 8128.
Definition CNT_R : Z := Int64.max_unsigned - CNT_W - 1.

Definition cnt_ok (top: Z) (L: list Z) (n: Z) : bool :=
  (top <? CNT_R + 1) && (n <? CNT_R) && (top <=? n + 1 + CNT_W) && negb (existsb (Z.eqb n) L).

Definition cnt_top' (top: Z) (L: list Z) (n: Z) : Z := if cnt_ok top L n then Z.max top (n + 1) else top.
Definition cnt_L' (top: Z) (L: list Z) (n: Z) : list Z := if cnt_ok top L n then n :: L else L.

(* bit t of the bitmap *)
Definition cnt_bit (bm: list Z) (t: Z) : bool := Z.testbit (Znth ((t / 64) mod 128) bm) (t mod 64).

Record cnt_inv (top: Z) (L: list Z) (bm: list Z) : Prop := {
  cnt_len: Zlength bm = 128;
  cnt_words: Forall (fun w => 0 <= w <= Int64.max_unsigned) bm;
  cnt_top_range: 0 <= top <= CNT_R;
  cnt_L_range: forall n, In n L -> 0 <= n < top;
  cnt_window: forall t, top - CNT_W <= t <= top -> cnt_bit bm t = existsb (Z.eqb (t - 1)) L;
  cnt_above: forall t, top < t < 64 * (top / 64 + 1) -> cnt_bit bm t = false
}.

(* the value of a struct noise_replay_counter: counter, lock (untouched), backtrack *)
Definition cnt_val (top: Z) (lk: val) (bm: list Z) : reptype (Tstruct _noise_replay_counter noattr) :=
  (Vlong (Int64.repr top), (lk, map (fun w => Vlong (Int64.repr w)) bm)).

Definition quickproof_ilog2_spec :=
  DECLARE _quickproof_ilog2
  WITH n: Z
  PRE [ tulong ]
    PROP (0 <= n <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr n)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.log2 n))) SEP ().

(* one word: the caller passes the address of the word and the bit number below 64 *)
Definition test_and_set_bit_spec :=
  DECLARE _test_and_set_bit
  WITH sh: share, p: val, nr: Z, w: Z
  PRE [ tulong, tptr tulong ]
    PROP (writable_share sh; 0 <= nr < 64; 0 <= w <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr nr); p)
    SEP (data_at sh tulong (Vlong (Int64.repr w)) p)
  POST [ tint ]
    PROP () RETURN (Val.of_bool (Z.testbit w nr))
    SEP (data_at sh tulong (Vlong (Int64.repr (Z.lor w (Z.shiftl 1 nr)))) p).

Definition cnt_validate_funspec : funspec :=
  WITH sh: share, c: val, top: Z, L: list Z, bm: list Z, lk: val, n: Z
  PRE [ tptr (Tstruct _noise_replay_counter noattr), tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned; cnt_inv top L bm)
    PARAMS (c; Vlong (Int64.repr n))
    SEP (data_at sh (Tstruct _noise_replay_counter noattr) (cnt_val top lk bm) c)
  POST [ tbool ]
    EX bm': list Z,
    PROP (cnt_inv (cnt_top' top L n) (cnt_L' top L n) bm')
    RETURN (Val.of_bool (cnt_ok top L n))
    SEP (data_at sh (Tstruct _noise_replay_counter noattr) (cnt_val (cnt_top' top L n) lk bm') c).

Definition counter_validate_spec := (_counter_validate, cnt_validate_funspec).
Definition wg_counter_validate_spec := (_wg_counter_validate, cnt_validate_funspec).

(* the counter piece *)
Definition cnt_imports (cs: compspecs) : funspecs := [].
Definition cnt_G : funspecs :=
  [quickproof_ilog2_spec; test_and_set_bit_spec; counter_validate_spec; wg_counter_validate_spec].
