(*
   - the local sk_buff skb: Cookie.CS data_at_ -> field-wise at the world W_cookie_reply (stores by main, the
     three nondet_bytes into the address / port arrays), and back into skb_rep;
   - B's checker: the field wb.cookie_checker.secret_birthdate at W (load by main) with a wand;
   - the shim's boot clock at W (store by main). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.proof.libc.libc_bytes.
Local Open Scope logic.

#[local] Instance hcy5_p3_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p3_cce_C : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p3_cce_WC : change_composite_env W_cookie_reply Cookie.CS.
Proof. make_cs_preserve W_cookie_reply Cookie.CS. Defined.

Definition hcy5_p3_fa4 (p: val) : val := @field_address W_cookie_reply t_skb (DOT HY._ip4 DOT HY._saddr DOT HY._s_addr) p.
Definition hcy5_p3_fa16 (p: val) : val := @field_address W_cookie_reply t_skb (DOT HY._ip6 DOT HY._saddr DOT HY._s6_addr) p.
Definition hcy5_p3_fa2 (p: val) : val := @field_address W_cookie_reply t_skb (DOT HY._udp DOT HY._source) p.

(* nondet_bytes' result as bytes *)
Lemma hcy5_p3_vbytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros HF. unfold bytes. rewrite map_map. apply map_ext_Forall.
  eapply Forall_impl; [| exact HF]. intros b Hb. simpl.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hcy5_p3_Zlength_bytes (bs: list Z) : Zlength (map Byte.repr bs) = Zlength bs.
Proof. apply Zlength_map. Qed.

Section W.
#[local] Existing Instance W_cookie_reply.

(* the uninitialised skb, field-wise *)
Lemma hcy5_p3_skb_open sh p :
  @data_at_ Cookie.CS sh t_skb p =
  field_at_ sh t_skb (DOT HY._data) p * field_at_ sh t_skb (DOT HY._len) p *
  field_at_ sh t_skb (DOT HY._protocol) p *
  data_at_ sh (tarray tuchar 4) (hcy5_p3_fa4 p) * data_at_ sh (tarray tuchar 16) (hcy5_p3_fa16 p) *
  data_at_ sh (tarray tuchar 2) (hcy5_p3_fa2 p) * spacer sh 36 40 p.
Proof.
  rewrite (@data_at__change_composite Cookie.CS W_cookie_reply _ sh t_skb); [| prove_cs_preserve_type].
  rewrite data_at__eq at 1. unfold hcy5_p3_fa4, hcy5_p3_fa16, hcy5_p3_fa2.
  unfold_data_at (data_at sh t_skb (default_val t_skb) p).
  unfold_field_at 4%nat. unfold_field_at 4%nat. unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at sh t_skb [StructField HY._s_addr; StructField HY._saddr; StructField HY._ip4]).
  rewrite (field_at_data_at sh t_skb [StructField HY._s6_addr; StructField HY._saddr; StructField HY._ip6]).
  rewrite (field_at_data_at sh t_skb [StructField HY._source; StructField HY._udp]).
  rewrite !data_at__eq. unfold field_at_. apply pred_ext; cancel.
Qed.

(* the filled skb, back to skb_rep *)
Lemma hcy5_p3_skb_close sh p (d: val) (l: int) (pr: Z) (a4 a6 a2: list byte) :
  0 <= pr <= 65535 -> Zlength a4 = 4 -> Zlength a6 = 16 -> Zlength a2 = 2 ->
  field_at sh t_skb (DOT HY._data) d p * field_at sh t_skb (DOT HY._len) (Vint l) p *
  field_at sh t_skb (DOT HY._protocol) (Vint (Int.repr pr)) p *
  data_at sh (tarray tuchar 4) (bytes a4) (hcy5_p3_fa4 p) *
  data_at sh (tarray tuchar 16) (bytes a6) (hcy5_p3_fa16 p) *
  data_at sh (tarray tuchar 2) (bytes a2) (hcy5_p3_fa2 p) * spacer sh 36 40 p
  |-- skb_rep sh p (mkSkb d l pr a4 a6 a2).
Proof.
  intros Hpr H4 H6 H2. unfold skb_rep.
  apply andp_right; [apply prop_right; split3; auto |].
  pose (v := (d, (Vint l, (Vint (Int.repr pr), (bytes a4, (bytes a6, bytes a2))))) : @reptype W_cookie_reply t_skb).
  rewrite (@data_at_change_composite Cookie.CS W_cookie_reply _ sh t_skb _ v); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold hcy5_p3_fa4, hcy5_p3_fa16, hcy5_p3_fa2, v.
  unfold_data_at (data_at sh t_skb _ p).
  unfold_field_at 7%nat. unfold_field_at 7%nat. unfold_field_at 8%nat. unfold_field_at 8%nat.
  unfold_field_at 9%nat.
  rewrite (field_at_data_at sh t_skb [StructField HY._s_addr; StructField HY._saddr; StructField HY._ip4]).
  rewrite (field_at_data_at sh t_skb [StructField HY._s6_addr; StructField HY._saddr; StructField HY._ip6]).
  rewrite (field_at_data_at sh t_skb [StructField HY._source; StructField HY._udp]).
  cancel.
Qed.

End W.

(* P |-- A * (A -* P) from a split of P *)
Lemma hcy5_p3_wand_intro (P A R Q: mpred) : P |-- A * R -> A * R |-- Q -> P |-- A * (A -* Q).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hcy5_p3_N2W_tulong sh v p : @data_at Noise.CS sh tulong v p = @data_at W_cookie_reply sh tulong v p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_cookie_reply _ sh tulong v v (JMeq_refl _) eq_refl)).
Qed.

(* the shim with the boot clock set to v *)
Definition hcy5_p3_sboot (S: shim) (v: int64) : shim :=
  mkShim v (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).

Section NS.
#[local] Existing Instance Noise.CS.
(* the shim's globals but the boot clock *)
Definition hcy5_p3_shim_rest (gv: globals) (S: shim) : mpred :=
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow).
End NS.

(* the shim's rest with the warnings (one SEP item) *)
Definition hcy5_p3_shim_rest4 (gv: globals) (S: shim) (w: list int64) : mpred :=
  hcy5_p3_shim_rest gv S * refwarn4 gv w.

Lemma hcy5_p3_shim_eq gv S w :
  shim_state4 gv S w =
  !! shim_ok S && (@data_at W_cookie_reply Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) * hcy5_p3_shim_rest4 gv S w).
Proof.
  unfold shim_state4, shim_core, hcy5_p3_shim_rest4, hcy5_p3_shim_rest. rewrite hcy5_p3_N2W_tulong.
  rewrite sepcon_andp_prop'. f_equal. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hcy5_p3_shim_rest_boot gv S v : hcy5_p3_shim_rest gv (hcy5_p3_sboot S v) = hcy5_p3_shim_rest gv S.
Proof. reflexivity. Qed.

Lemma hcy5_p3_shim_ok_boot S v : shim_ok S -> shim_ok (hcy5_p3_sboot S v).
Proof. auto. Qed.

(* B's checker: wb.cookie_checker.secret_birthdate at the world, for main's load *)
Lemma hcy5_p3_birth_eq sh wb v :
  @field_compatible Noise.CS t_dev [] wb ->
  @field_at Noise.CS sh t_cc (DOT I._secret_birthdate) v (cc_addr wb) =
  @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) v wb.
Proof.
  intros FC.
  assert (FW: @field_compatible W_cookie_reply t_dev [] wb) by (apply (@field_compatible_change_composite Noise.CS W_cookie_reply _ t_dev); [reflexivity | exact FC]).
  assert (A: @field_address Noise.CS t_cc (DOT I._secret_birthdate) (cc_addr wb) = @field_address W_cookie_reply t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) wb).
  { rewrite (@field_address_offset W_cookie_reply t_dev) by auto with field_compatible.
    assert (FC2: @field_compatible Noise.CS t_cc [] (cc_addr wb)).
    { pose proof (field_compatible_nested_field (cs:=Noise.CS) t_dev (DOT I._cookie_checker) wb) as FN.
      exact (FN ltac:(auto with field_compatible)). }
    rewrite (@field_address_offset Noise.CS t_cc) by auto with field_compatible.
    unfold cc_addr. rewrite offset_offset_val. reflexivity. }
  rewrite !field_at_data_at, A. simpl nested_field_type.
  exact (f_equal (fun f => f _) (@data_at_change_composite Noise.CS W_cookie_reply _ sh tulong v v (JMeq_refl _) eq_refl)).
Qed.

Section NS2.
#[local] Existing Instance Noise.CS.
Lemma hcy5_p3_cc_open sh wb CC :
  @field_compatible Noise.CS t_dev [] wb ->
  checker_rep sh (cc_addr wb) CC |--
  @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) (Vlong (cc_birth CC)) wb *
  (@field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) (Vlong (cc_birth CC)) wb -*
   checker_rep sh (cc_addr wb) CC).
Proof.
  intros FC. unfold checker_rep at 1. Intros lk.
  unfold_data_at (@data_at Noise.CS sh t_cc _ (cc_addr wb)).
  rewrite (hcy5_p3_birth_eq sh wb) by auto.
  match goal with |- ?a * (?b * (?c * (?d * ?e))) |-- _ =>
    apply (hcy5_p3_wand_intro _ d (a*b*c*e)); [cancel |] end.
  unfold checker_rep. Exists lk. entailer!.
  unfold_data_at (@data_at Noise.CS sh t_cc _ (cc_addr wb)).
  rewrite (hcy5_p3_birth_eq sh wb) by auto. cancel.
Qed.
End NS2.

(* the addresses of the skb's arrays *)
Lemma hcy5_p3_fa_eqs p :
  @field_compatible W_cookie_reply t_skb (DOT HY._protocol) p ->
  hcy5_p3_fa4 p = offset_val 14 p /\ hcy5_p3_fa16 p = offset_val 18 p /\ hcy5_p3_fa2 p = offset_val 34 p.
Proof.
  intros FP.
  assert (FS: @field_compatible W_cookie_reply t_skb [] p).
  { apply field_compatible_cons in FP. simpl in FP. tauto. }
  unfold hcy5_p3_fa4, hcy5_p3_fa16, hcy5_p3_fa2.
  rewrite !field_address_offset by auto with field_compatible. simpl. auto.
Qed.

(* the message buffer back as hbytes *)
Lemma hcy5_p3_hbytes_eq sh n bs p :
  Zlength bs = n -> @data_at W_cookie_reply sh (tarray tuchar n) (bytes bs) p = hbytes sh bs p.
Proof.
  intros <-. unfold hbytes. apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

(* the shim with the new boot clock *)
Lemma hcy5_p3_shim_close gv S w v :
  shim_ok S ->
  @data_at W_cookie_reply Ews tulong (Vlong v) (gv _wg_shim_boottime_ns) * hcy5_p3_shim_rest4 gv S w
  |-- shim_state4 gv (hcy5_p3_sboot S v) w.
Proof.
  intros HS. rewrite hcy5_p3_shim_eq. unfold hcy5_p3_shim_rest4. rewrite hcy5_p3_shim_rest_boot.
  apply andp_right; [apply prop_right; auto |]. apply derives_refl.
Qed.

#[local] Instance hcy5_p3_cce_H : change_composite_env HCS W_cookie_reply.
Proof. make_cs_preserve HCS W_cookie_reply. Defined.

(* an output buffer at the world *)
Lemma hcy5_p3_conv_bytes sh n p : hout sh n p = @data_at_ W_cookie_reply sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_cookie_reply _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.
