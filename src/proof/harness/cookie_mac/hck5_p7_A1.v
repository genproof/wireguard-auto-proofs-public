(* law cookie_mac, phase P7, segment A1: s82 = m_mac(mac1, wb's mac1 key, 32, copy, len - 32): S6 -> T1 (v1 hck3_p7_A1.v.old + hck3_p7_A1_lemmas.v.old).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_lemmas.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* the message buffer: its first k bytes as an input buffer (hin) and the rest *)
Definition hck5_p7_A1_mrest (sh: share) (bs: list byte) (p: val) (k: Z) : mpred :=
  ((if Z.eq_dec k 0 then @data_at HCS sh (tarray tuchar 0) [] p else emp) *
   @data_at HCS sh (tarray tuchar (Zlength bs - k)) (sublist k (Zlength bs) (bytes bs))
     (@field_address0 HCS (tarray tuchar (Zlength bs)) [ArraySubsc k] p))%logic.

Lemma hck5_p7_A1_msplit sh bs p k : 0 <= k <= Zlength bs ->
  hbytes sh bs p = (hin sh (sublist 0 k bs) p * hck5_p7_A1_mrest sh bs p k)%logic.
Proof.
  intros Hk. unfold hbytes, hin, hck5_p7_A1_mrest. rewrite Zlength_sublist by lia. replace (k - 0) with k by lia.
  rewrite (@split2_data_at_Tarray_tuchar HCS sh (Zlength bs) k) by (unfold bytes; rewrite ?Zlength_map; lia).
  destruct (Z.eq_dec k 0).
  - subst k. rewrite emp_sepcon. f_equal.
  - rewrite emp_sepcon. unfold hbytes. rewrite Zlength_sublist by lia. replace (k - 0) with k by lia.
    unfold bytes. rewrite sublist_map. reflexivity.
Qed.

(* a key buffer of nonzero length as an input buffer *)
Lemma hck5_p7_A1_hin sh bs p : Zlength bs <> 0 -> hbytes sh bs p = hin sh bs p.
Proof. intros H. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hck5_p7_A1_mac_len K M : Zlength (MAC K M) = 16.
Proof. unfold MAC, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Section P7A1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_A1_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S6 x25519 gv L FR) hck5_p7_s82
    (overridePost (hck5_T1 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S6, hck5_Delta, hck5_R, hck5_p7_s82. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode. Intros C ck MSG1 C1 MSG2 corrupted. Intros chk rl r VR.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wb L)) as FCwb by (unfold hck5_drest; entailer!).
  rewrite hck5_p7_cc_open by exact FCwb. Intros. rename H7 into HCC. pose proof HCC as (L1 & L2 & L3).
  assert (Hn: Zlength MSG2 = q_n Q) by (apply H6).
  pose proof H1 as (Hn1 & _).
  rewrite (hck5_p7_A1_msplit Ews MSG2 c (q_n Q - 32)) by lia.
  rewrite (hck5_p7_A1_hin Tsh (cc_mkey (snd VR))) by lia.
  unfold wg_consts. Intros.
  forward_call (gv, Tsh, l_mac1 L, Tsh, offset_val 64 (cc_addr (l_wb L)), cc_mkey (snd VR), Ews, c,
                sublist 0 (q_n Q - 32) MSG2).
  { entailer!. rewrite Zlength_sublist by lia. rewrite L3. destruct (l_wb L); try contradiction. simpl.
    rewrite Z.sub_0_r. reflexivity. }
  { split; [lia | rewrite Zlength_sublist by lia; rep_lia]. }
  assert (exists M1, hck5_is M1 (mac1_of (cc_mkey (snd VR)) MSG2)) as [M1 HM1] by (eexists; reflexivity).
  assert (EM: MAC (cc_mkey (snd VR)) (sublist 0 (q_n Q - 32) MSG2) = M1)
    by (rewrite HM1; unfold mac1_of; rewrite Hn; reflexivity).
  assert (LM1: Zlength M1 = 16) by (rewrite <- EM; apply hck5_p7_A1_mac_len).
  rewrite EM. clear EM.
  unfold hck5_T1. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists chk rl r VR. Exists M1.
  unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  rewrite hck5_p7_cc_open by exact FCwb. unfold wg_consts.
  rewrite (hck5_p7_A1_hin Tsh (cc_mkey (snd VR))) by lia.
  rewrite (hck5_p7_A1_msplit Ews MSG2 c (q_n Q - 32)) by lia.
  entailer!.
Qed.

End P7A1.
