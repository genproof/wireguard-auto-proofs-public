(*
   - the local skb: Cookie.CS data_at_ -> field-wise at the world W (main's stores and the three nondet_bytes into
     the address / port arrays), and back into hrx5_skb_part;
   - the shim's wg_shim_ratelimit_allow at W, the rest of shim_state4 apart;
   - the queue length global wg_shim_handshake_queue_len: HRX <-> W. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

#[local] Instance hrx5_B2_cce_C : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.
#[local] Instance hrx5_B2_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_B2_cce_H : change_composite_env HRX W.
Proof. make_cs_preserve HRX W. Defined.

Definition hrx5_B2_fa4 (p: val) : val := @field_address W t_skb (DOT HM._ip4 DOT HM._saddr DOT HM._s_addr) p.
Definition hrx5_B2_fa16 (p: val) : val := @field_address W t_skb (DOT HM._ip6 DOT HM._saddr DOT HM._s6_addr) p.
Definition hrx5_B2_fa2 (p: val) : val := @field_address W t_skb (DOT HM._udp DOT HM._source) p.

(* nondet_bytes' result as bytes *)
Lemma hrx5_B2_vbytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros HF. unfold bytes. rewrite map_map. apply map_ext_Forall.
  eapply Forall_impl; [| exact HF]. intros b Hb. simpl.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Section W.
#[local] Existing Instance W.

(* the uninitialised skb, field-wise *)
Lemma hrx5_B2_skb_open sh p :
  @data_at_ Cookie.CS sh t_skb p =
  field_at_ sh t_skb (DOT HM._data) p * field_at_ sh t_skb (DOT HM._len) p *
  field_at_ sh t_skb (DOT HM._protocol) p *
  data_at_ sh (tarray tuchar 4) (hrx5_B2_fa4 p) * data_at_ sh (tarray tuchar 16) (hrx5_B2_fa16 p) *
  data_at_ sh (tarray tuchar 2) (hrx5_B2_fa2 p) * spacer sh 36 40 p.
Proof.
  rewrite (@data_at__change_composite Cookie.CS W _ sh t_skb); [| prove_cs_preserve_type].
  rewrite data_at__eq at 1. unfold hrx5_B2_fa4, hrx5_B2_fa16, hrx5_B2_fa2.
  unfold_data_at (data_at sh t_skb (default_val t_skb) p).
  unfold_field_at 4%nat. unfold_field_at 4%nat. unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at sh t_skb [StructField HM._s_addr; StructField HM._saddr; StructField HM._ip4]).
  rewrite (field_at_data_at sh t_skb [StructField HM._s6_addr; StructField HM._saddr; StructField HM._ip6]).
  rewrite (field_at_data_at sh t_skb [StructField HM._source; StructField HM._udp]).
  rewrite !data_at__eq. unfold field_at_. apply pred_ext; cancel.
Qed.

(* the filled skb (data and len still any), back to hrx5_skb_part *)
Lemma hrx5_B2_skb_close L (pr: Z) (a4 a6 a2: list byte) :
  0 <= pr <= 65535 -> Zlength a4 = 4 -> Zlength a6 = 16 -> Zlength a2 = 2 ->
  field_at_ Tsh t_skb (DOT HM._data) (l_skb L) * field_at_ Tsh t_skb (DOT HM._len) (l_skb L) *
  field_at Tsh t_skb (DOT HM._protocol) (Vint (Int.repr pr)) (l_skb L) *
  data_at Tsh (tarray tuchar 4) (bytes a4) (hrx5_B2_fa4 (l_skb L)) *
  data_at Tsh (tarray tuchar 16) (bytes a6) (hrx5_B2_fa16 (l_skb L)) *
  data_at Tsh (tarray tuchar 2) (bytes a2) (hrx5_B2_fa2 (l_skb L)) * spacer Tsh 36 40 (l_skb L)
  |-- hrx5_skb_part L pr a4 a6 a2.
Proof.
  intros Hpr H4 H6 H2. unfold hrx5_skb_part.
  apply andp_right; [apply prop_right; split3; auto |].
  Exists Vundef Vundef.
  set (p := l_skb L).
  pose (v := (Vundef, (Vundef, (Vint (Int.repr pr), (bytes a4, (bytes a6, bytes a2))))) : @reptype W t_skb).
  rewrite (@data_at_change_composite Cookie.CS W _ Tsh t_skb _ v); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold hrx5_B2_fa4, hrx5_B2_fa16, hrx5_B2_fa2, v. unfold field_at_.
  unfold_data_at (data_at Tsh t_skb _ p).
  unfold_field_at 7%nat. unfold_field_at 7%nat. unfold_field_at 8%nat. unfold_field_at 8%nat.
  unfold_field_at 9%nat.
  rewrite (field_at_data_at Tsh t_skb [StructField HM._s_addr; StructField HM._saddr; StructField HM._ip4]).
  rewrite (field_at_data_at Tsh t_skb [StructField HM._s6_addr; StructField HM._saddr; StructField HM._ip6]).
  rewrite (field_at_data_at Tsh t_skb [StructField HM._source; StructField HM._udp]).
  cancel.
Qed.

(* the addresses of the skb's arrays *)
Lemma hrx5_B2_fa_eqs p :
  @field_compatible W t_skb (DOT HM._protocol) p ->
  hrx5_B2_fa4 p = offset_val 14 p /\ hrx5_B2_fa16 p = offset_val 18 p /\ hrx5_B2_fa2 p = offset_val 34 p.
Proof.
  intros FP.
  assert (FS: @field_compatible W t_skb [] p).
  { apply field_compatible_cons in FP. simpl in FP. tauto. }
  unfold hrx5_B2_fa4, hrx5_B2_fa16, hrx5_B2_fa2.
  rewrite !field_address_offset by auto with field_compatible. simpl. auto.
Qed.

End W.

(* the queue length global *)
Lemma hrx5_B2_qlen_ eq_sh p :
  @data_at_ HRX eq_sh tint p = @data_at_ W eq_sh tint p.
Proof. rewrite (@data_at__change_composite HRX W _ eq_sh tint); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hrx5_B2_qlen gv q :
  @data_at W Ews tint (Vint q) (gv HM._wg_shim_handshake_queue_len) = qlen_rep gv q.
Proof.
  unfold qlen_rep.
  rewrite (@data_at_change_composite HRX W _ Ews tint (Vint q) (Vint q)); [reflexivity | apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the shim with the rate limiter's answer set to b *)
Definition hrx5_B2_srl (S: shim) (b: bool) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) b.

Section NS.
#[local] Existing Instance Noise.CS.
(* the shim's globals but the rate limiter *)
Definition hrx5_B2_shim_rest (gv: globals) (S: shim) : mpred :=
   data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released).
End NS.

Lemma hrx5_B2_N2W_tbool sh v p : @data_at Noise.CS sh tbool v p = @data_at W sh tbool v p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W _ sh tbool v v (JMeq_refl _) eq_refl)).
Qed.

Lemma hrx5_B2_shim_eq gv S w :
  shim_state4 gv S w =
  !! shim_ok S && (hrx5_B2_shim_rest gv S *
     @data_at W Ews tbool (Val.of_bool (s_rlallow S)) (gv HM._wg_shim_ratelimit_allow)) * refwarn4 gv w.
Proof.
  unfold shim_state4, shim_core, hrx5_B2_shim_rest. rewrite (hrx5_B2_N2W_tbool _ _ (gv _wg_shim_ratelimit_allow)). reflexivity.
Qed.

Lemma hrx5_B2_shim_close gv S w b :
  shim_ok S ->
  hrx5_B2_shim_rest gv S * @data_at W Ews tbool (Val.of_bool b) (gv HM._wg_shim_ratelimit_allow) * refwarn4 gv w
  |-- shim_state4 gv (hrx5_B2_srl S b) w.
Proof.
  intros HS. rewrite hrx5_B2_shim_eq. change (hrx5_B2_shim_rest gv (hrx5_B2_srl S b)) with (hrx5_B2_shim_rest gv S).
  simpl s_rlallow. entailer!.
Qed.
