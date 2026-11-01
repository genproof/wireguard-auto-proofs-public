(* law handshake: main's phase P1, segment E = statements 23..27: m_precomputed x2, the precomputed and psk CHECKs.
   (section P1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* the m_identity struct with its public key apart (as in hhs3_p1_D) *)
Definition hhs3E_midrest (sh: share) (p: val) (I: mident) : mpred :=
  (@field_at HCS sh t_mident (DOT HC._priv) (bytes (mi_priv I)) p *
   @field_at HCS sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.

Lemma hhs3E_mid_split sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (hbytes sh (mi_pub I) (offset_val 32 p) * hhs3E_midrest sh p I)%logic.
Proof.
  intros FC Lpub.
  unfold mident_val. unfold_data_at (@data_at HCS sh t_mident _ p).
  assert (Hpub: @field_at HCS sh t_mident (DOT HC._pub) (bytes (mi_pub I)) p = hbytes sh (mi_pub I) (offset_val 32 p)).
  { rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes. rewrite Lpub.
    reflexivity. }
  simpl in Hpub. rewrite Hpub. unfold hhs3E_midrest. apply pred_ext; cancel.
Qed.

Lemma hhs3E_mid_join sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_pub I) = 32 ->
  (hbytes sh (mi_pub I) (offset_val 32 p) * hhs3E_midrest sh p I |-- @data_at HCS sh t_mident (mident_val I) p)%logic.
Proof. intros. rewrite hhs3E_mid_split by auto. cancel. Qed.

Lemma hhs3E_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hhs3E_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Section Fields.
#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* the peer without its handshake *)
Definition hhs3E_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hhs3E_peer_split sh p P :
  peer_rep sh p P = hhs3E_prest sh p P * hs_rep sh (hs_addr p) (p_hs P).
Proof.
  unfold peer_rep, hhs3E_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

(* the handshake without its precomputed static-static DH and its preshared key *)
Definition hhs3E_hrest (sh: share) (h: val) (H: handshake) : mpred :=
  !! (field_compatible t_hs [] h /\ hs_ok H) &&
  (field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
   field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
   field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
   field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
   field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h).

Lemma hhs3E_hs_split sh h H :
  hs_rep sh h H =
  hbytes sh (hs_ss H) (offset_val 152 h) * hbytes sh (hs_psk H) (offset_val 184 h) * hhs3E_hrest sh h H.
Proof.
  unfold hs_rep, hhs3E_hrest. apply pred_ext.
  - Intros lk. Exists lk. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & _).
    assert_PROP (field_compatible t_hs (DOT I._state) h) as FC0 by entailer!.
    assert (FC: field_compatible t_hs [] h) by (destruct FC0 as (?&?&?&?&?); repeat split; auto).
    unfold hbytes. rewrite L4, L5. rewrite !(@hhs3E_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros lk. Exists lk. rename H0 into FC, H1 into Hok. pose proof Hok as (L1 & L2 & L3 & L4 & L5 & _).
    unfold hbytes. rewrite L4, L5. rewrite !(@hhs3E_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

Lemma hhs3E_peer_open sh p P :
  peer_rep sh p P =
  hbytes sh (hs_ss (p_hs P)) (offset_val 152 (hs_addr p)) * hbytes sh (hs_psk (p_hs P)) (offset_val 184 (hs_addr p)) *
  (hhs3E_hrest sh (hs_addr p) (p_hs P) * hhs3E_prest sh p P).
Proof.
  rewrite hhs3E_peer_split, hhs3E_hs_split. apply pred_ext; cancel.
Qed.

Lemma hhs3E_peer_close sh p P :
  hbytes sh (hs_ss (p_hs P)) (offset_val 152 (hs_addr p)) * hbytes sh (hs_psk (p_hs P)) (offset_val 184 (hs_addr p)) *
  (hhs3E_hrest sh (hs_addr p) (p_hs P) * hhs3E_prest sh p P) |-- peer_rep sh p P.
Proof. rewrite hhs3E_peer_open. apply derives_refl. Qed.
End Fields.

Lemma hhs3_p1_E_clamp s : Zlength (clamp s) = Zlength s.
Proof. unfold clamp. list_solve. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p1_E_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p1_SD x25519 gv L FR) hhs3_p1_E
    (overridePost (hhs3_p1_SE x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p1_SD, hhs3_Delta, hhs3_R, hhs3_p1_E. simplify_func_tycontext. abbreviate_semax.
  Intros R S a0 f0 l0.
  unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
  destruct HH as (Hx & _ & _ & _ & Hrep). pose proof H as (La & Lb & Lpsk & Hup & _).
  assert (LQa: Zlength (mi_pub (hhs3_IA x25519 R)) = 32) by apply Hx.
  assert (LQb: Zlength (mi_pub (hhs3_IB x25519 R)) = 32) by apply Hx.
  assert (LPa: Zlength (mi_priv (hhs3_IA x25519 R)) = 32).
  { unfold hhs3_IA, mident_of; simpl. rewrite hhs3_p1_E_clamp. auto. }
  assert (LPb: Zlength (mi_priv (hhs3_IB x25519 R)) = 32).
  { unfold hhs3_IB, mident_of; simpl. rewrite hhs3_p1_E_clamp. auto. }
  assert_PROP (@field_compatible HCS t_mident [] (l_ia L) /\ @field_compatible HCS t_mident [] (l_ib L)) as FCi
    by entailer!.
  destruct FCi as (FCia & FCib).
  rewrite (hhs3E_mid_split Tsh (l_ib L)) by auto. Intros.
  forward_call (Tsh, l_ssa L, Tsh, l_ia L, hhs3_IA x25519 R, Tsh, offset_val 32 (l_ib L), mi_pub (hhs3_IB x25519 R)).
  sep_apply (hhs3E_mid_join Tsh (l_ib L) (hhs3_IB x25519 R) FCib LQb).
  rewrite (hhs3E_mid_split Tsh (l_ia L)) by auto. Intros.
  forward_call (Tsh, l_ssb L, Tsh, l_ib L, hhs3_IB x25519 R, Tsh, offset_val 32 (l_ia L), mi_pub (hhs3_IA x25519 R)).
  sep_apply (hhs3E_mid_join Tsh (l_ia L) (hhs3_IA x25519 R) FCia LQa).
  set (PB := hhs3_PB0 x25519 R L). set (PA := hhs3_PA0 x25519 R L).
  set (SSA := m_precomputed_model x25519 (hhs3_IA x25519 R) (mi_pub (hhs3_IB x25519 R))).
  set (SSB := m_precomputed_model x25519 (hhs3_IB x25519 R) (mi_pub (hhs3_IA x25519 R))).
  assert (EssB: hs_ss (p_hs PB) = SSA) by reflexivity.
  assert (EssA: hs_ss (p_hs PA) = SSB) by reflexivity.
  assert (EpB: hs_psk (p_hs PB) = r_psk R) by reflexivity.
  assert (EpA: hs_psk (p_hs PA) = r_psk R) by reflexivity.
  assert (LSA: Zlength SSA = 32).
  { unfold SSA, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  assert (LSB: Zlength SSB = 32).
  { unfold SSB, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  assert (Q1: bytes_eqb (hs_ss (p_hs PB)) SSA = true) by (rewrite EssB; apply hhs3E_eqb_refl).
  assert (Q2: bytes_eqb (hs_ss (p_hs PA)) SSB = true) by (rewrite EssA; apply hhs3E_eqb_refl).
  assert (Q3: bytes_eqb (hs_psk (p_hs PB)) (r_psk R) = true) by (rewrite EpB; apply hhs3E_eqb_refl).
  assert (Q4: bytes_eqb (hs_psk (p_hs PA)) (r_psk R) = true) by (rewrite EpA; apply hhs3E_eqb_refl).
  rewrite (hhs3E_peer_open Tsh (l_pb L)), (hhs3E_peer_open Tsh (l_pa L)). Intros.
  (* CHECK(bytes_eq(pb.handshake.precomputed_static_static, ssa, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 152 (hs_addr (l_pb L)), hs_ss (p_hs PB), Tsh, l_ssa L, SSA).
    { rewrite EssB, LSA. entailer!. }
    { rewrite EssB, LSA; rep_lia. }
    rewrite Q1.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(pa.handshake.precomputed_static_static, ssb, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 152 (hs_addr (l_pa L)), hs_ss (p_hs PA), Tsh, l_ssb L, SSB).
    { rewrite EssA, LSB. entailer!. }
    { rewrite EssA, LSB; rep_lia. }
    rewrite Q2.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(pb.handshake.preshared_key, psk, 32) && bytes_eq(pa.handshake.preshared_key, psk, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 184 (hs_addr (l_pb L)), hs_psk (p_hs PB), Tsh, l_psk L, r_psk R).
    { rewrite EpB, Lpsk. entailer!. }
    { rewrite EpB, Lpsk; rep_lia. }
    rewrite Q3.
    forward_if (temp HC._t'13 (Vint Int.one)).
    { forward_call (Tsh, offset_val 184 (hs_addr (l_pa L)), hs_psk (p_hs PA), Tsh, l_psk L, r_psk R).
      { rewrite EpA, Lpsk. entailer!. }
    { rewrite EpA, Lpsk; rep_lia. }
      rewrite Q4. forward. entailer!. }
    { exfalso. exact (Int.one_not_zero H1). }
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hhs3E_peer_close Tsh (l_pb L) PB).
  sep_apply (hhs3E_peer_close Tsh (l_pa L) PA).
  unfold hhs3_p1_SE. Exists R S a0 f0 l0.
  unfold hhs3_p1_SEsep, hhs3_setup_sep, hhs3_p1_rest, hhs3_globs, hhs3_scr_tmp, hhs3_lvars, hhs3_cnt_temps.
  cbn [app]. unfold hhs3_ssa, hhs3_ssb. fold SSA SSB.
  entailer!. unfold PA, PB. cancel.
Qed.

End Seg.
