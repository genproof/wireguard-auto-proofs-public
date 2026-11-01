(* law cookie_reply, phase P10, segment D:
   statement 62..65: now = draw_boottime(); wg_shim_boottime_ns = now; shim_take(&ss); wg_cookie_message_consume(reply, &wa).
*)
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
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p10_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

#[local] Instance hcy5_p10_d_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

#[local] Instance hcy5_p10_d_cce_KW : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

(* the snapshot local: the world's data_at_ is CKS's *)
Lemma hcy5_p10_d_shimsnap_ sh p : @data_at_ W_cookie_reply sh t_shimsnap p = @data_at_ CKS sh t_shimsnap p.
Proof. symmetry. exact (f_equal (fun f => f p) (@data_at__change_composite CKS W_cookie_reply _ sh t_shimsnap eq_refl)). Qed.

(* the shim's boot clock (Noise.CS) as main stores it (world) *)
Lemma hcy5_p10_d_ulong sh (v: val) p :
  @data_at Noise.CS sh tulong v p = @data_at W_cookie_reply sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

(* the shim after main's store of the boot clock *)
Lemma hcy5_p10_d_shim gv S now : shim_ok S ->
  @data_at Noise.CS Ews tulong (Vlong now) (gv _wg_shim_boottime_ns) *
  @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
  @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
  @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
  @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)
  |-- shim_core gv (shim_set_boot S now).
Proof. intros HS. unfold shim_core; cbn. entailer!. Qed.

(* a peer address of PS: found, with a reference *)
Lemma hcy5_p10_d_sfind L KS PS a :
  Forall (hcy5_pok L KS) PS -> In a (map peer_addr4 PS) ->
  exists sh P, sfind PS a = Some (sh, P) /\ p_refs P <> Int.zero.
Proof.
  induction PS as [| [[x sh] P] PS IH]; cbn [map In]; intros Hok Hin; [contradiction |].
  inv Hok. cbn [sfind]. destruct (eq_dec x a) as [-> | Hne].
  - exists sh, P. split; [reflexivity |]. destruct H1 as (_ & _ & _ & Hr & _).
    intro E. rewrite E, Int.unsigned_zero in Hr. lia.
  - apply IH; auto. destruct Hin as [Hin | Hin]; [cbn in Hin; contradiction | exact Hin].
Qed.

(* the consumption's precondition on A's pool and peers *)
Lemma hcy5_p10_d_ppok L KS NS PS KE T :
  hcy5_lists_ok L KS NS PS -> hcy5_T_ok PS KE T -> pool_peers_ok T PS.
Proof.
  intros (Hpok & _ & _ & _ & _) ((own & ix & HD & Hown) & _). unfold pool_peers_ok. rewrite HD. unfold hcy5_pool.
  apply Forall_app. split; apply Forall_forall; intros x Hin; apply in_map_iff in Hin; destruct Hin as (y & <- & Hin).
  - unfold hcy5_kentry. cbn [e_peer e_type]. split; [| right; reflexivity].
    apply (hcy5_p10_d_sfind L KS); auto. rewrite Forall_forall in Hown. apply Hown; auto.
  - unfold hcy5_hent. cbn [e_peer e_type]. split; [| left; split; reflexivity].
    apply (hcy5_p10_d_sfind L KS); auto.
Qed.

Lemma hcy5_p10_d_wf L KS PS : Forall (hcy5_pok L KS) PS -> peers_wf PS.
Proof.
  intros Hpok. unfold peers_wf. eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hp. destruct Hp as (-> & _).
  auto.
Qed.

Lemma hcy5_p10_d_refs L KS PS : Forall (hcy5_pok L KS) PS -> peers_refs_ok PS.
Proof.
  intros Hpok. unfold peers_refs_ok. eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hp.
  destruct Hp as (_ & _ & _ & Hr & _). exact Hr.
Qed.

(* the head of the peers after the consumption (supd keeps the addresses) *)
Lemma hcy5_p10_d_phead PS r : hcy5_phead (peers_after PS r) = hcy5_phead PS.
Proof.
  destruct r as [[a P'] |]; [| reflexivity]. destruct PS as [| [[x sh] w] PS]; cbn; [reflexivity |].
  destruct (EqDec_val x a); reflexivity.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p10_D_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p10_TC x25519 xaead_enc gv L FR) hcy5_p10_sD
    (overridePost (hcy5_S10 x25519 xaead_enc xaead_dec gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p10_TC, hcy5_Delta, hcy5_R, hcy5_p10_sD. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q nonce rr CK CM.
  Intros NS PS T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  forward_call tt. Intros now.
  unfold shim_state4, shim_core. Intros.
  rewrite hcy5_p10_d_ulong.
  forward.
  rewrite <- hcy5_p10_d_ulong.
  sep_apply (hcy5_p10_d_shim gv S now H8).
  rewrite hcy5_p10_d_shimsnap_.
  forward_call (gv, Tsh, l_ss L, shim_set_boot S now, hcy5_w0).
  { unfold shim_state4. cancel. }
  pose proof H0 as Hlists. destruct Hlists as (Hpok & Hnp & Hnd1 & Hnd2 & Hpk).
  change (itable Tsh (l_ita L) T) with (itable Tsh (d_itab (hcy5_DA x25519 R L)) T).
  forward_call (gv, shim_set_boot S now, hcy5_w0, Ews, rp, CM', Tsh, l_wa L, hcy5_DA x25519 R L, Tsh, T, PS).
  { split; [apply (hcy5_p10_d_ppok L (map ke_addr KE) NS PS KE T); auto |].
    split; [apply (hcy5_p10_d_wf L (map ke_addr KE)); auto | apply (hcy5_p10_d_refs L (map ke_addr KE)); auto]. }
  unfold hcy5_S10. Exists R (shim_set_boot S now) m c rp Q nonce rr CK CM.
  Exists NS PS T np CL KE CM' honest now.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  rewrite hcy5_p10_d_phead.
  change (mcons_res xaead_dec T PS CM' (shim_set_boot S now)) with (hcy5_res xaead_dec T PS CM' now).
  change (d_itab (hcy5_DA x25519 R L)) with (l_ita L).
  entailer!.
Qed.

End Seg.
