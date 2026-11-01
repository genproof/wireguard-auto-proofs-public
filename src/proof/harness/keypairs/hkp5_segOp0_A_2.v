(* law keypairs, segment Op0 part A, piece A2: statements 6..10 of the op 0
   branch (hs_randomize(&p.handshake); st = p.handshake.state; if (nondet_u8() & 1)
   wg_index_hashtable_insert(&t, &p.handshake.entry); p.is_dead = dead; prm.is_dead = dead).

   States: hkp5_segOp0_A_defs.v; "Op0 part A". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The peer's fields A2 reads / stores, at main's compspecs (v1's A2)      *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hkp5_o0A2_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkp5_o0A2_hscs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0A2_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0A2_pcs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0A2_CCE) t_peer = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0A2_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_keypairs (Tstruct KC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_keypairs hkp5_o0A2_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hkp5_o0A2_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_keypairs (Tstruct KC._wg_peer noattr) [StructField KC._handshake] p = hs_addr p.
Proof. intros H. apply hkp5_o0A2_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hkp5_o0A2_state sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint v) (hs_addr p) =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._state; StructField KC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField KC._state; StructField KC._handshake] with ([StructField KC._state] ++ [StructField KC._handshake]).
  rewrite (@field_at_app W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._state] [StructField KC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hkp5_o0A2_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0A2_CCE sh t_hs
           [StructField prot_repr3.I._state] (Vint v) (Vint v) (JMeq_refl _) hkp5_o0A2_hscs)).
Qed.

Lemma hkp5_o0A2_dead sh p v :
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] v p =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._is_dead] v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0A2_CCE sh t_peer
           [StructField prot_repr3.I._is_dead] v v (JMeq_refl _) hkp5_o0A2_pcs)).
Qed.

(* the peer without its handshake's state and its is_dead *)
Definition hkp5_o0A2_rest (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._ephemeral_private] (bytes (hs_eph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes (hs_hash H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes (hs_ck H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes (hs_ts H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hkp5_o0A2_open sh p P :
  peer_rep sh p P |--
  (!! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
   (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._state; StructField KC._handshake]
      (Vint (hs_state (p_hs P))) p *
    @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._is_dead] (Val.of_bool (p_dead P)) p *
    hkp5_o0A2_rest sh p P))%logic.
Proof.
  unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
  apply andp_right; [apply prop_right; split; auto |].
  unfold hkp5_o0A2_rest. cbv zeta.
  rewrite <- (hkp5_o0A2_state sh p _ Hfc), <- hkp5_o0A2_dead.
  cancel.
Qed.

Lemma hkp5_o0A2_fold sh p P dead :
  @field_compatible Noise.CS t_peer [] p -> hs_ok (p_hs P) ->
  (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._state; StructField KC._handshake]
      (Vint (hs_state (p_hs P))) p *
    @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._is_dead] (Val.of_bool dead) p *
    hkp5_o0A2_rest sh p P)%logic |-- peer_rep sh p (hkp5_o0A_set_dead P dead).
Proof.
  intros Hfc Hok.
  unfold hkp5_o0A2_rest. cbv zeta.
  rewrite <- (hkp5_o0A2_state sh p _ Hfc), <- hkp5_o0A2_dead.
  unfold peer_rep, hs_rep. unfold hkp5_o0A_set_dead.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  Intros lk. Exists lk.
  apply andp_right; [apply prop_right; split; assumption |].
  cancel.
Qed.

Lemma hkp5_o0A_2_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i Y dead k R :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0A_ins_fact ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0A_K x25519 F V steps FR i Y dead k) hkp5_o0A_s2
    (overridePost (EX Y': hkp5_dyn, EX E: entry, hkp5_o0A_N x25519 F V steps FR i Y' E k) R).
Proof.
  intros HF HX HI.
  unfold hkp5_o0A_K, hkp5_Delta, hkp5_o0A_s2.
  destruct Y as [S w kc P KS T HH now next_id id_known hsn].
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  Intros.
  abbreviate_semax.
  forward_call (Tsh, f_p F, P).
Intros vret. destruct vret as [[[[[[[st lic] eph] reph] hash] ck] ts] ri].
  cbn [fst snd] in *.
  set (P1 := p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri)).
  sep_apply (hkp5_o0A2_open Tsh (f_p F) P1). Intros.
  match goal with Hx: hs_ok _ |- _ => rename Hx into Hok end.
  match goal with Hx: field_compatible t_peer [] _ |- _ => rename Hx into Hfc end.
  assert (Est: hs_state (p_hs P1) = st) by reflexivity. rewrite Est.
  forward.
  forward_call tt.
  Intros u.
pose proof H1 as Hinv.
  destruct H1 as (Hrel & Hwarn & Hdev & Hsid & Hrefs & Hfr & Hal & Hid & Hnow & Hhsm).
  cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn] in Hrel, Hwarn, Hdev, Hsid, Hrefs, Hfr, Hal,
    Hid, Hnow, Hhsm.
  match goal with |- semax _ (PROPx ?Pp (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    let Rf := eval pattern T, S in Rs in
    match Rf with ?f _ _ =>
      forward_if (EX T1: tstate, EX S1: shim,
        PROPx (hk5_rel (f_p F) (v_OD V) (v_OH V) HH P KS T1 :: (s_boot S1 = s_boot S) ::
               (s_allocs S1 = s_allocs S) :: (s_fails S1 = s_fails S) :: (s_frees S1 = s_frees S) :: Pp)
        (LOCALx Q (SEPx (f T1 S1))))
    end
  end.
  { pose proof Hrel as ((_ & _ & _ & _ & _ & _ & _ & _ & Hpool) & _).
    pose proof Hpool as (Hsad & _).
    assert (Hin: In (hs_addr (f_p F)) (saddrs (t_D T))) by (apply Hsad; left; reflexivity).
    forward_call (f_gv F, S, w, Tsh, f_t F, T, hs_addr (f_p F), @None (share * entry)).
    { unfold P4.raw_rep. rewrite emp_sepcon. cancel. }
    Intros idx. cbn [P4.raw_add] in *.
    assert_PROP (itable_wf (t_insert T (hs_addr (f_p F)) idx)) as Hwf by (unfold itable; entailer!).
    assert (Hrel1: hk5_rel (f_p F) (v_OD V) (v_OH V) HH P KS (t_insert T (hs_addr (f_p F)) idx))
      by (apply HI; assumption).
    Exists (t_insert T (hs_addr (f_p F)) idx) (shim_u32 S idx).
    entailer!. }
  { forward. Exists T S. entailer!. }
  Intros T1 S1.
forward.
  forward.
  replace (force_val (sem_cast_i2bool (Val.of_bool dead))) with (Val.of_bool dead) by (destruct dead; reflexivity).
  change (Vint st) with (Vint (hs_state (p_hs P1))).
  sep_apply (hkp5_o0A2_fold Tsh (f_p F) P1 dead Hfc Hok).
  set (P2 := hkp5_o0A_set_dead P1 dead).
  change (fst (hk5_prsnap_val P), (Val.of_bool dead, snd (snd (hk5_prsnap_val P)))) with (hk5_prsnap_val P2).
  pose proof H1 as ((_ & _ & _ & _ & _ & _ & _ & _ & Hpool1) & _).
  pose proof Hpool1 as (_ & _ & _ & _ & (idx1 & Hhs1) & _).
  assert (Hent: t_entry T1 (hs_addr (f_p F)) = Some (mkEntry (f_p F) IDX_HANDSHAKE idx1))
    by (unfold t_entry; rewrite Hhs1; reflexivity).
  set (Y' := {| y_S := S1; y_w := w; y_kc := kc; y_P := P2; y_KS := KS; y_T := T1; y_H := HH; y_now := now;
    y_next_id := next_id; y_id_known := id_known; y_hsn := hsn |}).
  assert (Hinv0: hkp5_inv0 F V Y').
  { unfold hkp5_inv0, Y'. cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
    rewrite H14, H16.
    exact (conj H1 (conj Hwarn (conj Hdev (conj Hsid (conj Hrefs (conj Hfr (conj Hal (conj Hid (conj Hnow (proj2 Hhsm)))))))))). }
  assert (Ed: p_dead P2 = dead) by reflexivity.
  assert (Es: hs_state (p_hs P2) = st) by reflexivity.
  assert (Hok2: hs_ok (p_hs P2)) by exact Hok.
  destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
  Exists Y' (mkEntry (f_p F) IDX_HANDSHAKE idx1).
  unfold hkp5_o0A_N, hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  unfold Y'. cbn [app y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  fold Y'.
  rewrite Ed, Es, H13, H14, H15, H16.
  entailer!.
Qed.