(* law create_any: Segment F0a (hca5_fdefs.v) = the op == 0 branch body's statements 0..5 (fill_init(m); init_img(before, m); bytes_copy(exp, before, 148); draw_real_clock(); m_tai64n(ts, wg_shim_real_sec, wg_shim_real_nsec); r = wg_noise_handshake_create_initiation(m, &p.handshake)), from hca5_F0S0 m to hca5_F0S1 m.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: the same C). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

#[local] Instance hca5_F0a_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

(* the shim's globals but the real clock *)
Definition hca5_F0a_rest (gv: globals) (S: shim) : mpred :=
  @data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
  @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
  @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow).

Lemma hca5_F0a_long sh (v: val) p : @data_at Noise.CS sh tlong v p = @data_at W_create_any sh tlong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_create_any _ sh tlong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hca5_F0a_shim gv S w : shim_state4 gv S w =
  !! shim_ok S &&
  (@data_at W_create_any Ews tlong (Vlong (s_rsec S)) (gv HC._wg_shim_real_sec) *
   @data_at W_create_any Ews tlong (Vlong (s_rnsec S)) (gv HC._wg_shim_real_nsec) * hca5_F0a_rest gv S) *
  refwarn4 gv w.
Proof.
  unfold shim_state4, shim_core, hca5_F0a_rest. f_equal. f_equal.
  rewrite <- !hca5_F0a_long.
  apply pred_ext; cancel.
Qed.

Lemma hca5_F0a_fold gv S w : shim_ok S ->
  @data_at W_create_any Ews tlong (Vlong (s_rsec S)) (gv HC._wg_shim_real_sec) *
  @data_at W_create_any Ews tlong (Vlong (s_rnsec S)) (gv HC._wg_shim_real_nsec) * hca5_F0a_rest gv S *
  refwarn4 gv w |-- shim_state4 gv S w.
Proof.
  intros HS. rewrite hca5_F0a_shim. rewrite sepcon_andp_prop'.
  apply andp_right; [apply prop_right; exact HS | apply derives_refl].
Qed.

Lemma hca5_F0a_init sh m : @data_at_ W_create_any sh t_init_W m = @data_at_ Noise.CS sh t_init m.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_init eq_refl) m). Qed.

Lemma hca5_F0a_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). unfold init_bytes.
  rewrite !Zlength_app, !prot_rep3_le32_len, H1, H2, H3, H4, H5. reflexivity.
Qed.

Lemma hca5_F0a_sfind (p: val) (KS: list kdraw) (E: entry) :
  ~ In (hs_addr p) (map kd_addr KS) ->
  sfind (map (hca5_kpool p) KS ++ [(hs_addr p, Tsh, E)]) (hs_addr p) = Some (Tsh, E).
Proof.
  induction KS as [|K KS IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_F0a_inpool (p: val) (KS: list kdraw) (T: tstate) :
  hca5_pool p KS T -> hs_in_pool T p.
Proof.
  intros [[E [HD [Hp _]]] [Hnd _]]. exists E. split; [|exact Hp]. unfold t_entry. rewrite HD.
  inversion Hnd; subst. rewrite hca5_F0a_sfind by assumption. reflexivity.
Qed.

Lemma hca5_F0a_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0S0 x25519 gv L FR w m)
    hca5_F0a
    (overridePost (hca5_F0S1 x25519 aead_enc gv L FR w m) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_F0S0, hca5_Delta, hca5_R, hca5_F0a. simplify_func_tycontext. abbreviate_semax.
  Intros R S P T KS E.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  rewrite hca5_F0a_init.
  forward_call (Ews, m).
  Intros M. pose proof (hca5_F0a_len M H4) as HML.
  forward_call (Tsh, l_before L, Ews, m, M).
  forward_call (Tsh, l_exp L, Tsh, l_before L, init_bytes M).
  { rewrite HML. entailer!. }
  { rewrite HML. cancel. }
  forward_call (gv, S, w). Intros vret. destruct vret as [sec ns]; cbn [fst snd] in *.
  rewrite hca5_F0a_shim. Intros. forward. forward.
  forward_call (Tsh, l_ts L, s_rsec (shim_set_real S sec (Int64.repr ns)), s_rnsec (shim_set_real S sec (Int64.repr ns))).
  sep_apply (hca5_F0a_fold gv (shim_set_real S sec (Int64.repr ns)) w H6).
  set (S1 := shim_set_real S sec (Int64.repr ns)).
  pose proof (hca5_F0a_inpool _ _ _ H1) as Hin.
  rename H0 into HPOK. pose proof HPOK as (Hpd & Hsid & Hok).
  forward_call (gv, S1, w, Int64.zero, Ews, m, M, Tsh, l_p L, P, Tsh, l_wa L, hca5_D x25519 R L, Tsh, T).
  Intros vret. destruct vret as [rr idx]; cbn [fst snd] in *.
  change (d_itab (hca5_D x25519 R L)) with (l_ita L).
  change (ci_res x25519 aead_enc (hca5_D x25519 R L) P M S1 rr idx)
    with (hca5_CI x25519 aead_enc R L P M S1 rr idx) in *.
  change (if id_has (d_id (hca5_D x25519 R L))
          then (if fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))
                then shim_u32 (shim_draw S1 rr) idx else shim_draw S1 rr) else S1)
    with (hca5_CIshim x25519 aead_enc R L P M S1 rr idx).
  forward.
  unfold hca5_F0S1. Exists R P T KS E M S1 rr idx S.
  forget (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) as S2.
  forget (hca5_CI x25519 aead_enc R L P M S1 rr idx) as CI.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app].
  destruct (fst (fst CI)) eqn:Hb; entailer!.
Qed.
