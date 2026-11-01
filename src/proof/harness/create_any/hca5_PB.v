(* law create_any: Segment B = statements 8..10 (setup_peer, m_precomputed, CHECK(bytes_eq(p.handshake.precomputed_static_static, dh, 32))), from hca5_SA to hca5_SB.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: same C where the C did not change). *)
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
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

Lemma hca5_PB_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hca5_PB_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Section Fields.
#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* the peer without its handshake *)
Definition hca5_PB_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hca5_PB_peer_split sh p P :
  peer_rep sh p P = hca5_PB_prest sh p P * hs_rep sh (hs_addr p) (p_hs P).
Proof.
  unfold peer_rep, hca5_PB_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

(* the handshake without its precomputed static-static DH and its preshared key *)
Definition hca5_PB_hrest (sh: share) (h: val) (H: handshake) : mpred :=
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

Lemma hca5_PB_hs_split sh h H :
  hs_rep sh h H =
  hbytes sh (hs_ss H) (offset_val 152 h) * hbytes sh (hs_psk H) (offset_val 184 h) * hca5_PB_hrest sh h H.
Proof.
  unfold hs_rep, hca5_PB_hrest. apply pred_ext.
  - Intros lk. Exists lk. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & _).
    assert_PROP (field_compatible t_hs (DOT I._state) h) as FC0 by entailer!.
    assert (FC: field_compatible t_hs [] h) by (destruct FC0 as (?&?&?&?&?); repeat split; auto).
    unfold hbytes. rewrite L4, L5. rewrite !(@hca5_PB_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros lk. Exists lk. rename H0 into FC, H1 into Hok. pose proof Hok as (L1 & L2 & L3 & L4 & L5 & _).
    unfold hbytes. rewrite L4, L5. rewrite !(@hca5_PB_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

Lemma hca5_PB_peer_open sh p P :
  peer_rep sh p P =
  hbytes sh (hs_ss (p_hs P)) (offset_val 152 (hs_addr p)) * hbytes sh (hs_psk (p_hs P)) (offset_val 184 (hs_addr p)) *
  (hca5_PB_hrest sh (hs_addr p) (p_hs P) * hca5_PB_prest sh p P).
Proof.
  rewrite hca5_PB_peer_split, hca5_PB_hs_split. apply pred_ext; cancel.
Qed.

Lemma hca5_PB_peer_close sh p P :
  hbytes sh (hs_ss (p_hs P)) (offset_val 152 (hs_addr p)) * hbytes sh (hs_psk (p_hs P)) (offset_val 184 (hs_addr p)) *
  (hca5_PB_hrest sh (hs_addr p) (p_hs P) * hca5_PB_prest sh p P) |-- peer_rep sh p P.
Proof. rewrite hca5_PB_peer_open. apply derives_refl. Qed.
End Fields.

Lemma hca5_PB_hout sh l q : Zlength l = 32 -> hbytes sh l q |-- hout sh 32 q.
Proof. intros HL. unfold hout, hbytes. rewrite HL. apply data_at_data_at_. Qed.

Lemma hca5_PB_split (pk q: val) PSK : (pk = nullval \/ pk = q) -> isptr q ->
  hbytes Tsh PSK q |--
  (if eq_dec pk nullval then emp else hbytes Tsh PSK pk) * (if eq_dec pk nullval then hbytes Tsh PSK q else emp).
Proof.
  intros [-> | ->] Hq.
  - rewrite !if_true by auto. cancel.
  - rewrite !if_false by (destruct q; try contradiction; discriminate). cancel.
Qed.

Lemma hca5_PB_merge (pk q: val) PSK : (pk = nullval \/ pk = q) -> Zlength PSK = 32 ->
  (if eq_dec pk nullval then emp else hbytes Tsh PSK pk) * (if eq_dec pk nullval then hbytes Tsh PSK q else emp)
  |-- hout Tsh 32 q.
Proof.
  intros Hpk HL. unfold hout, hbytes. rewrite HL.
  destruct (eq_dec pk nullval); [| destruct Hpk; [contradiction | subst]]; normalize; apply data_at_data_at_.
Qed.

Lemma hca5_PB_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SA x25519 gv L FR w)
    hca5_PB
    (overridePost (hca5_SB x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_SA, hca5_Delta, hca5_R, hca5_PB. simplify_func_tycontext. abbreviate_semax.
  Intros R S PUB PSK u.
  unfold hca5_globs, hca5_snap0, hca5_scr, hca5_lvars; cbn [app].
  forward_if (temp HC._t'3 (if Z.eq_dec u 0 then nullval else l_psk L)).
  { forward. destruct (Z.eq_dec u 0); [subst; contradiction|]. entailer!. }
  { forward. destruct (Z.eq_dec u 0); [|exfalso; apply n; destruct H2 as [H2a H2b]; assert (u = 0 \/ u = 1) as [|] by lia; subst; [reflexivity|discriminate]]. entailer!. }
  assert_PROP (isptr (l_psk L)) as Hpsk by entailer!.
  assert (Hpk: (if Z.eq_dec u 0 then nullval else l_psk L) = nullval \/
               (if Z.eq_dec u 0 then nullval else l_psk L) = l_psk L) by (destruct (Z.eq_dec u 0); auto).
  forget (if Z.eq_dec u 0 then nullval else l_psk L) as pk.
  sep_apply (hca5_PB_split _ (l_psk L) PSK Hpk Hpsk).
  forward_call (gv, Tsh, l_p L, Tsh, l_wa L, hca5_D x25519 R L, nullval, Tsh, l_pub L, PUB, pk, PSK, Int64.repr 1).
  { cancel. }
  sep_apply (hca5_PB_merge pk (l_psk L) PSK Hpk H1).
  assert (Hcl: Zlength (mi_priv (hca5_I x25519 R)) = 32).
  { unfold hca5_I, mident_of; cbn [mi_priv]. destruct H as [Hr _]. unfold clamp; list_solve. }
  forward_call (Tsh, l_dh L, Tsh, l_ia L, hca5_I x25519 R, Tsh, l_pub L, PUB).
  destruct HH as (Hx & _).
  set (P := setup_peer_val x25519 (hca5_D x25519 R L) (l_wa L) (l_p L) nullval PUB
              (if eq_dec pk nullval then zeros32 else PSK) (Int64.repr 1)).
  set (SS := m_precomputed_model x25519 (hca5_I x25519 R) PUB).
  assert (Ess: hs_ss (p_hs P) = SS) by reflexivity.
  assert (LSS: Zlength SS = 32).
  { unfold SS, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  assert (Q1: bytes_eqb (hs_ss (p_hs P)) SS = true) by (rewrite Ess; apply hca5_PB_eqb_refl).
  rewrite (hca5_PB_peer_open Tsh (l_p L)). Intros.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 152 (hs_addr (l_p L)), hs_ss (p_hs P), Tsh, l_dh L, SS).
    { rewrite Ess, LSS. entailer!. }
    { rewrite Ess, LSS; rep_lia. }
    rewrite Q1.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hca5_PB_peer_close Tsh (l_p L) P).
  sep_apply (prot_rep3_pool_add Tsh (l_ita L) (mkT [] []) (hs_addr (l_p L)) Tsh
               (mkEntry (l_p L) IDX_HANDSHAKE Int.zero) writable_share_top).
  unfold hca5_SB.
  Exists R S P (mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] []).
  unfold hca5_world, hca5_globs, hca5_snap0, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  change (d_ptab (hca5_D x25519 R L)) with (l_pta L).
  change (t_add {| t_D := []; t_L := [] |} (hs_addr (l_p L)) Tsh (mkEntry (l_p L) IDX_HANDSHAKE Int.zero))
    with (mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] []).
  assert (Hpok: hca5_pok L P []).
  { unfold hca5_pok. split3; [reflexivity | reflexivity |].
    split; [| split; [reflexivity | repeat constructor; left; reflexivity]].
    unfold P, setup_peer_val, prot_specs3.hs_initial; cbn [p_hs hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
    unfold hs_ok; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
    assert (Lpre: forall I q, Zlength (precomputed x25519 I q) = 32).
    { intros I q. unfold precomputed. destruct (_ && _)%bool; [apply Hx | reflexivity]. }
    rewrite Lpre. destruct (eq_dec pk nullval); repeat split; auto. }
  assert (Hpool: hca5_pool (l_p L) []
    (mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] [])).
  { unfold hca5_pool. split; [| split].
    - exists (mkEntry (l_p L) IDX_HANDSHAKE Int.zero). split3; reflexivity.
    - cbn. constructor; [intros [] | constructor].
    - intros x []. }
  pose proof H as (Lraw & _).
  sep_apply (hca5_PB_hout Tsh (r_raw R) (l_raw L) Lraw).
  sep_apply (hca5_PB_hout Tsh PUB (l_pub L) H0).
  sep_apply (hca5_PB_hout Tsh SS (l_dh L) LSS).
  entailer!.
Qed.
