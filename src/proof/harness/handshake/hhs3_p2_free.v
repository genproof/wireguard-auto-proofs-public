(* law handshake: main's phase P2, the early return of segment B: every object back to main's stack frame (hhs3_p2_free_stmt).
*)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p2_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Helpers.

(* a device dissolves into its struct (cf. hhs3_p1_free_dev0) *)
Lemma hhs3_p2_free_dev0 sh wg D : device_rep sh wg D |-- @data_at_ Noise.CS sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep. Intros lk1 lk2.
  unfold_data_at (@data_at_ Noise.CS sh t_dev wg).
  assert (E1: id_addr wg = @field_address Noise.CS t_dev (DOT I._static_identity) wg) by
    (unfold id_addr, OFS_DEV_IDENTITY; rewrite field_address_offset by auto with field_compatible; reflexivity).
  assert (E2: cc_addr wg = @field_address Noise.CS t_dev (DOT I._cookie_checker) wg) by
    (unfold cc_addr, OFS_DEV_CHECKER; rewrite field_address_offset by auto with field_compatible; reflexivity).
  rewrite E1, E2.
  rewrite (@field_at_data_at Noise.CS sh t_dev (DOT noise.code._static_identity)),
          (@field_at_data_at Noise.CS sh t_dev (DOT noise.code._cookie_checker)).
  rewrite <- !sepcon_assoc.
  repeat apply sepcon_derives;
    first [ (eapply derives_trans; [apply field_at_field_at_|]; apply derives_refl)
          | (eapply derives_trans; [apply data_at_data_at_|]; apply derives_refl) ].
Qed.

Lemma hhs3_p2_free_dev sh wg D : device_rep sh wg D |-- @data_at_ W_handshake sh t_dev wg.
Proof. rewrite <- hhs3_conv_dev. apply hhs3_p2_free_dev0. Qed.

(* an index table whose pool is exactly one peer's handshake entry, and that peer *)
Lemma hhs3_p2_free_tabpeer :
  hhs3_rep -> forall tab p P T E, t_D T = [(hs_addr p, Tsh, E)] ->
  itable Tsh tab T * peer_rep Tsh p P |--
  @data_at_ W_handshake Tsh t_itab tab * @data_at_ W_handshake Tsh t_peer p.
Proof.
  intros Hrep tab p P T E HT.
  sep_apply (hhs3_itable_dissolve Tsh tab T).
  rewrite HT. simpl VST.msl.iter_sepcon.iter_sepcon. unfold hhs3_pool_entry. Intros n h.
  destruct Hrep as (_ & _ & _ & _ & _ & _ & Hpe & _).
  sep_apply (Hpe Tsh p P E n h).
  rewrite <- hhs3_conv_itab, <- hhs3_conv_peer. cancel.
Qed.

Lemma hhs3_p2_free_ptab sh tab h : ptable sh tab h |-- @data_at_ W_handshake sh t_ptab tab.
Proof. unfold ptable. rewrite <- hhs3_conv_ptab. apply data_at_data_at_. Qed.

Lemma hhs3_p2_free_mident sh v p : @data_at HCS sh t_mident v p |-- @data_at_ W_handshake sh t_mident p.
Proof. rewrite <- hhs3_conv_mident. apply data_at_data_at_. Qed.

Lemma hhs3_p2_free_bytes sh bs p :
  Zlength bs = 32 -> hbytes sh bs p |-- @data_at_ W_handshake sh (tarray tuchar 32) p.
Proof. intros H. rewrite <- hhs3_conv_bytes. unfold hbytes, hout. rewrite H. apply data_at_data_at_. Qed.

Lemma hhs3_p2_free_pre x25519 I pub :
  x25519_props x25519 -> Zlength (m_precomputed_model x25519 I pub) = 32.
Proof.
  intros Hx. unfold m_precomputed_model. destruct (mi_ok I && dh_ok x25519 (mi_priv I) pub)%bool; [apply Hx | reflexivity].
Qed.

End Helpers.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.

Lemma hhs3_p2_free_ok : hhs3_rep -> hhs3_p2_free_stmt x25519.
Proof.
  intros Hrep Hx gv L FR R S Ta Tb Ea Eb PB PA Hok HTa HTb.
  destruct Hok as (Ha & Hb & Hp & _).
  unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp, hhs3_p2_frame.
  simpl app. simpl fold_right_sepcon.
  sep_apply (hhs3_p2_free_dev Tsh (l_wa L) (hhs3_DA x25519 R L)).
  sep_apply (hhs3_p2_free_dev Tsh (l_wb L) (hhs3_DB x25519 R L)).
  sep_apply (hhs3_p2_free_ptab Tsh (l_pta L) (l_pb L)).
  sep_apply (hhs3_p2_free_ptab Tsh (l_ptb L) (l_pa L)).
  sep_apply (hhs3_p2_free_mident Tsh (mident_val (hhs3_IA x25519 R)) (l_ia L)).
  sep_apply (hhs3_p2_free_mident Tsh (mident_val (hhs3_IB x25519 R)) (l_ib L)).
  sep_apply (hhs3_p2_free_bytes Tsh (r_rawa R) (l_rawa L) Ha).
  sep_apply (hhs3_p2_free_bytes Tsh (r_rawb R) (l_rawb L) Hb).
  sep_apply (hhs3_p2_free_bytes Tsh (r_psk R) (l_psk L) Hp).
  sep_apply (hhs3_p2_free_bytes Tsh (hhs3_ssa x25519 R) (l_ssa L) (hhs3_p2_free_pre _ _ _ Hx)).
  sep_apply (hhs3_p2_free_bytes Tsh (hhs3_ssb x25519 R) (l_ssb L) (hhs3_p2_free_pre _ _ _ Hx)).
  sep_apply (hhs3_p2_free_tabpeer Hrep (l_ita L) (l_pb L) PB Ta Ea HTa).
  sep_apply (hhs3_p2_free_tabpeer Hrep (l_itb L) (l_pa L) PA Tb Eb HTb).
  rewrite !hhs3_conv_bytes, hhs3_conv_minit, hhs3_conv_mcinit, hhs3_conv_mresp, hhs3_conv_mstate,
          hhs3_conv_hsnap.
  cancel.
Qed.

End Seg.
