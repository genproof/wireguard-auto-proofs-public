(* wg_counter_validate's
   specification at the world W_transport_keepalive, over representation ht4k_rc of struct
   noise_replay_counter (lock Vundef: rc_init never writes it), and its funspec_sub from the counter piece's
   (counter_spec.v, at Counter.CS).  Law transport_order: `sed -e s/transport_keepalive/transport_order/g
   -e s/ht4k_/ht4o_/g`. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.transport_keepalive.ht4k_wm_spec.

Local Open Scope Z_scope.

#[local] Instance ht4k_cnt_CCE : change_composite_env Counter.CS W_transport_keepalive.
Proof. make_cs_preserve Counter.CS W_transport_keepalive. Defined.

Lemma ht4k_rc_change sh top bm v :
  @data_at W_transport_keepalive sh ht4k_trc (ht4k_rc top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold ht4k_trc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_transport_keepalive ht4k_cnt_CCE sh
    (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) (ht4k_rc top bm) (JMeq_refl _) eq_refl)).
Qed.

Definition ht4k_cnt_validate_spec :=
  DECLARE _wg_counter_validate
  WITH sh: share, c: val, top: Z, L: list Z, bm: list Z, n: Z
  PRE [ tptr ht4k_trc, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned; cnt_inv top L bm)
    PARAMS (c; Vlong (Int64.repr n))
    SEP (@data_at W_transport_keepalive sh ht4k_trc (ht4k_rc top bm) c)
  POST [ tbool ]
    EX bm': list Z,
    PROP (cnt_inv (cnt_top' top L n) (cnt_L' top L n) bm')
    RETURN (Val.of_bool (cnt_ok top L n))
    SEP (@data_at W_transport_keepalive sh ht4k_trc (ht4k_rc (cnt_top' top L n) bm') c).

Lemma ht4k_cnt_validate_sub : funspec_sub (snd wg_counter_validate_spec) (snd ht4k_cnt_validate_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros [[[[[sh c] top] L] bm] n] gargs. simpl.
  Exists (sh, c, top, L, bm, Vundef, n) (@emp mpred _ _). simpl.
  rewrite emp_sepcon, ht4k_rc_change.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho. rewrite emp_sepcon. apply andp_left2.
  Intros bm'. Exists bm'. rewrite ht4k_rc_change. entailer!.
Qed.
