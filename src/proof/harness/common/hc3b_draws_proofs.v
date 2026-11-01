(* hc_pieces3, group draws: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

#[local] Existing Instance CSk.

Lemma hc3b_draws_body_check_failed :
  @semax_body [] (hc3_G_none) CSk FH.f_check_failed (check_failed_spec).
Proof.
start_function. contradiction.
Qed.

Lemma hc3b_draws_body_m_not_flood :
  @semax_body [] (hc3_G_none) CSk FH.f_m_not_flood (m_not_flood_spec).
Proof.
start_function. forward.
apply prop_right; unfold not_flood, s64_le; destruct (Int64.lt _ _); reflexivity.
Qed.

Lemma hc3b_draws_body_m_last_consumption :
  @semax_body [] (hc3_G_none) CSk FH.f_m_last_consumption (m_last_consumption_spec).
Proof.
start_function.
forward_if (PROP () LOCAL (temp FH._t'1 (Vlong (last_consumption last now))) SEP ()).
- forward. entailer!.
  unfold last_consumption, Int64.lt, Int64.zero; destruct (zlt _ _); [reflexivity | lia].
- forward. entailer!.
  unfold last_consumption, Int64.lt, Int64.zero; destruct (zlt _ _); [lia | reflexivity].
- forward.
Qed.

Lemma hc3b_draws_body_draw_size :
  @semax_body [] (hc3_G_draw_size) CSk FK.f_draw_size (draw_size_spec).
Proof.
start_function.
forward_call tt. Intros n.
forward_if (PROP () LOCAL (temp FK._t'2 (Vlong (Int64.repr n))) SEP ()).
- forward. entailer!.
- exfalso. unfold Int64.ltu in H0. rewrite (Int64.unsigned_repr n) in H0 by lia.
  destruct (zlt _ _) as [L|]; [|discriminate]. change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned in L. lia.
- forward. Exists n. entailer!.
Qed.

Lemma hc3b_draws_body_draw_steps :
  @semax_body [] (hc3_G_draw_size) CSk FR.f_draw_steps (draw_steps_spec).
Proof.
start_function.
forward_call tt. Intros n.
forward_if (PROP () LOCAL (temp FR._t'2 (Vlong (Int64.repr n))) SEP ()).
- forward. entailer!.
- exfalso. unfold Int64.ltu in H0. rewrite (Int64.unsigned_repr n) in H0 by lia.
  destruct (zlt _ _) as [L|]; [|discriminate]. change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned in L. lia.
- forward. Exists n. entailer!.
Qed.

Lemma hc3b_draws_body_draw_u64 :
  @semax_body [] (hc3_G_draw_u64) CSk FH.f_draw_u64 (draw_u64_spec).
Proof.
start_function.
apply -> seq_assoc. forward_call tt. Intros hi. forward.
forward_call tt. Intros lo. forward.
Exists (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo)). entailer!.
Qed.

Lemma hc3b_draws_body_draw_boottime :
  @semax_body [] (hc3_G_draw_boottime) CSk FH.f_draw_boottime (draw_boottime_spec).
Proof.
start_function.
forward_call tt. Intros v.
forward.
Exists (Int64.and v (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 62)) (Int64.repr 1))). entailer!.
rewrite Int64.and_commut.
pose proof (Int64.and_le (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 62)) (Int64.repr 1)) v).
pose proof (Int64.unsigned_range (Int64.and (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 62)) (Int64.repr 1)) v)).
change (Int64.unsigned (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 62)) (Int64.repr 1))) with (2^62-1) in H.
lia.
Qed.

Lemma hc3b_draws_body_draw_hs_state :
  @semax_body [] (hc3_G_draw_hs_state) CSk FR.f_draw_hs_state (draw_hs_state_spec).
Proof.
start_function.
forward_call tt. Intros b.
(* VST's forward_if on this switch fails (the value of t'1 % 5 is not syntactically Int.repr _) *)
apply semax_seq with (PROP () LOCAL () SEP ()).
2: { unfold MORE_COMMANDS, abbreviate. forward. Exists HS_CONSUMED_RESPONSE. entailer!. simpl; tauto. }
apply (semax_switch_PQR (b mod 5)); [reflexivity | entailer! | entailer! | ].
{ destruct H1 as [_ E]; discriminate. }
{ f_equal. unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 5); rep_lia).
assert (b mod 5 = 0 \/ b mod 5 = 1 \/ b mod 5 = 2 \/ b mod 5 = 3 \/ b mod 5 = 4) as [E|[E|[E|[E|E]]]]
  by (pose proof (Z.mod_pos_bound b 5); lia);
  rewrite E; match goal with |- semax _ _ ?c _ => let c' := eval simpl in c in change c with c' end; forward;
  [Exists HS_ZEROED | Exists HS_CREATED_INITIATION | Exists HS_CONSUMED_INITIATION | Exists HS_CREATED_RESPONSE | idtac ];
  try (entailer!; simpl; tauto).
Qed.

(* a scalar data_at does not depend on the compspecs (shim_state is stated at Noise.CS) *)
Lemma hc3b_draws_data_at_tlong_cs {cs1 cs2: compspecs} sh (v: val) p :
  @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  split; intros (?&?&?&?&?); repeat split; auto;
    (eapply align_compatible_rec_by_value; [reflexivity|]);
    (eapply align_compatible_rec_by_value_inv in H2; [exact H2 | reflexivity]).
Qed.

(* draw_real_clock stores to the shim globals wg_shim_real_sec / _nsec: with V0 = [] their Evar does not typecheck
   (tc_lvalue = FF), so the body is proved with these two in V0 (hc3_Vsub holds in every law's unit, where they are
   variables of the shim) *)
Definition hc3b_draws_V_real_clock : varspecs := [(FH._wg_shim_real_sec, tlong); (FH._wg_shim_real_nsec, tlong)].

Lemma hc3b_draws_body_draw_real_clock :
  @semax_body hc3b_draws_V_real_clock (hc3_G_draw_real_clock) CSk FH.f_draw_real_clock (draw_real_clock_spec).
Proof.
start_function.
forward_call tt. Intros v.
unfold shim_state. Intros.
change _wg_shim_real_sec with FH._wg_shim_real_sec. change _wg_shim_real_nsec with FH._wg_shim_real_nsec.
rewrite !(@hc3b_draws_data_at_tlong_cs Noise.CS CSk).
(* the other shim globals are not in Delta: hide them from entailer!'s check *)
freeze FR := - (data_at _ _ _ (gv FH._wg_shim_real_sec)) (data_at _ _ _ (gv FH._wg_shim_real_nsec)).
forward.
forward_call tt. Intros ns.
forward.
thaw FR.
assert (Hm: Int.unsigned (Int.modu (Int.repr ns) (Int.repr 1000000000)) = ns mod 1000000000).
{ unfold Int.modu. rewrite (Int.unsigned_repr ns), (Int.unsigned_repr 1000000000) by rep_lia.
  apply Int.unsigned_repr. pose proof (Z.mod_pos_bound ns 1000000000). rep_lia. }
Exists v (Int.unsigned (Int.modu (Int.repr ns) (Int.repr 1000000000))).
unfold shim_state, shim_set_real; simpl s_boot; simpl s_rsec; simpl s_rnsec; simpl s_log; simpl s_logprev;
  simpl s_u32; simpl s_allocs; simpl s_fails; simpl s_frees; simpl s_failnext; simpl s_released; simpl s_rlallow.
rewrite !(@hc3b_draws_data_at_tlong_cs Noise.CS CSk).
change _wg_shim_real_sec with FH._wg_shim_real_sec. change _wg_shim_real_nsec with FH._wg_shim_real_nsec.
go_lowerx. rewrite Hm. unfold stackframe_of; simpl. rewrite !sepcon_emp.
pose proof (Z.mod_pos_bound ns 1000000000).
repeat (apply andp_right; [apply prop_right; unfold shim_ok in *; simpl; repeat split; tauto || lia | ]).
cancel.
Qed.

End Bodies.
