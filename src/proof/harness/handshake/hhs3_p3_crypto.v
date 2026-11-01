(* law handshake, phase P3: B decrypts A's timestamp, completeness 1 (pure).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

(* the kernel's create_initiation at success: its conditions and the message's crypto fields *)
Lemma hhs3_p3_crypto_ci (x25519: list byte -> list byte -> list byte)
  (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
  ID H M r ts idx M1 H1 :
  create_initiation_model x25519 aead_enc ID H M r ts idx = (true, M1, H1) ->
  id_has ID = true /\ dh_ok x25519 (clamp r) (hs_rstatic H) = true /\
  memneq_bool (hs_ss H) zeros32 = true /\
  im_eph M1 = x25519 (clamp r) basepoint9 /\
  im_encs M1 = aead_enc (kdf2 (kdf1 init_ck (x25519 (clamp r) basepoint9)) (x25519 (clamp r) (hs_rstatic H))) 0
                 (mix_hash (mix_hash init_hash (hs_rstatic H)) (x25519 (clamp r) basepoint9)) (id_pub ID) /\
  im_enct M1 = aead_enc (kdf2 (kdf1 (kdf1 init_ck (x25519 (clamp r) basepoint9)) (x25519 (clamp r) (hs_rstatic H)))
                           (hs_ss H)) 0
                 (mix_hash (mix_hash (mix_hash init_hash (hs_rstatic H)) (x25519 (clamp r) basepoint9)) (im_encs M1)) ts.
Proof.
  intros HC. unfold create_initiation_model in HC. cbv zeta in HC.
  destruct (id_has ID); [| discriminate]. cbn [negb] in HC.
  destruct (memneq_bool (clamp r) zeros32); [| discriminate]. cbn [negb] in HC.
  destruct (memneq_bool (x25519 (clamp r) basepoint9) zeros32); [| discriminate]. cbn [negb] in HC.
  destruct (dh_ok x25519 (clamp r) (hs_rstatic H)); [| discriminate]. cbn [negb] in HC.
  destruct (memneq_bool (hs_ss H) zeros32); [| discriminate]. cbn [negb] in HC.
  inversion HC; subst; clear HC. cbn [im_eph im_encs im_enct]. auto 10.
Qed.

(* ts_newer t over zeros: t is not zero *)
Lemma hhs3_p3_crypto_newer_rep (t: list byte) :
  ts_newer t (repeat Byte.zero (length t)) = negb (bytes_eqb t (repeat Byte.zero (length t))).
Proof.
  induction t as [| x t IH]; [reflexivity |].
  cbn [length repeat ts_newer]. unfold bytes_eqb in *.
  destruct (Byte.eq x Byte.zero) eqn:Ex.
  - apply Byte.same_if_eq in Ex. subst x. rewrite IH.
    destruct (list_eq_dec Byte.eq_dec t (repeat Byte.zero (length t))) as [E1 | N1];
    destruct (list_eq_dec Byte.eq_dec (Byte.zero :: t) (Byte.zero :: repeat Byte.zero (length t))) as [E2 | N2];
    try reflexivity.
    + exfalso. apply N2. rewrite <- E1. reflexivity.
    + exfalso. apply N1. injection E2 as E3. exact E3.
  - destruct (list_eq_dec Byte.eq_dec (x :: t) (Byte.zero :: repeat Byte.zero (length t))) as [E2 | N2].
    + inversion E2; subst x. rewrite Byte.eq_true in Ex. discriminate.
    + cbn [negb]. apply Z.gtb_lt. pose proof (Byte.unsigned_range x).
      assert (Byte.unsigned x <> 0).
      { intro Z0. assert (x = Byte.zero).
        { rewrite <- (Byte.repr_unsigned x), Z0. reflexivity. }
        subst x. rewrite Byte.eq_true in Ex. discriminate. }
      change (Byte.unsigned Byte.zero) with 0. lia.
Qed.

Lemma hhs3_p3_crypto_newer (t: list byte) :
  Zlength t = 12 -> is_zero t = false -> ts_newer t (zeros 12) = true.
Proof.
  intros HL HZ. unfold is_zero in HZ. rewrite HL in HZ.
  assert (E: zeros 12 = repeat Byte.zero (length t)).
  { unfold zeros, Zrepeat. rewrite <- HL, Zlength_correct, Nat2Z.id. reflexivity. }
  rewrite E in *. rewrite hhs3_p3_crypto_newer_rep, HZ. reflexivity.
Qed.

Lemma hhs3_p3_crypto_tslen (I: hhs3_ini) : Zlength (hhs3_ts I) = 12.
Proof. unfold hhs3_ts, tai64n, be64, be32. rewrite Zlength_correct. reflexivity. Qed.

Lemma hhs3_p3_crypto_flood (nowb: int64) :
  0 <= Int64.unsigned nowb < 2 ^ 62 -> Int64.ltu nowb (Int64.repr 20000000) = false ->
  not_flood Int64.zero nowb = true.
Proof.
  intros HR HL. unfold not_flood, s64_le. rewrite Int64.add_zero_l.
  unfold Int64.ltu in HL. unfold Int64.lt.
  rewrite Int64.signed_eq_unsigned by (unfold Int64.max_signed, Int64.half_modulus, Int64.modulus,
    Int64.wordsize, Wordsize_64.wordsize; simpl; lia).
  rewrite Int64.signed_repr by (unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus,
    Int64.modulus, Int64.wordsize, Wordsize_64.wordsize; simpl; lia).
  rewrite Int64.unsigned_repr in HL by (unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize,
    Wordsize_64.wordsize; simpl; lia).
  destruct (zlt (Int64.unsigned nowb) 20000000); [discriminate | reflexivity].
Qed.

(* X25519 commutes on the clamped keys of the harness *)
(* the only use of hhs3_comm's commutativity: at 32-byte scalars (the suite's interface gives no more) *)
Lemma hhs3_p3_dh (x25519: list byte -> list byte -> list byte) :
  hhs3_comm x25519 -> forall a b, Zlength a = 32 -> Zlength b = 32 ->
  x25519 a (x25519 b basepoint9) = x25519 b (x25519 a basepoint9).
Proof. intros [_ H] a b Ha Hb. apply H; assumption. Qed.

Lemma hhs3_p3_crypto_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros H. unfold clamp. rewrite !Zlength_upd_Znth. exact H. Qed.

Lemma hhs3_p3_crypto_sw (x25519: list byte -> list byte -> list byte) a b :
  hhs3_comm x25519 -> Zlength a = 32 -> Zlength b = 32 ->
  x25519 (clamp a) (x25519 b basepoint9) = x25519 (clamp b) (x25519 a basepoint9).
Proof. intros Hc Ha Hb. pose proof Hc as [C1 _]. rewrite !C1. apply hhs3_p3_dh; assumption. Qed.

Lemma hhs3_p3_crypto_ida (x25519: list byte -> list byte -> list byte) R L :
  mi_ok (hhs3_IA x25519 R) = true ->
  d_id (hhs3_DA x25519 R L) = mkId (mi_pub (hhs3_IA x25519 R)) (mi_priv (hhs3_IA x25519 R)) true.
Proof.
  unfold hhs3_DA, setup_dev, setup_identity, identity_of, hhs3_IA, mident_of. cbn [d_id mi_ok mi_pub mi_priv].
  destruct (memneq_bool (r_rawa R) zeros32); [| discriminate]. cbn [andb]. intros ->. reflexivity.
Qed.

Lemma hhs3_p3_crypto_ok (x25519: list byte -> list byte -> list byte) (aead_enc: list byte -> Z -> list byte -> list byte -> list byte) (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) :
  hhs3_p3_crypto_stmt x25519 aead_enc aead_dec.
Proof.
  intros Hc Hx Ha R L I M1 H1 MI nowb Hrun Hai Hnow.
  assert (Hrlen: Zlength (i_r I) = 32) by (destruct Hai as (_ & _ & _ & _ & _ & Hr & _); exact Hr).
  destruct Hrun as (HlA & HlB & _).
  destruct Hai as (okA & Hci & _).
  unfold hhs3_ci in Hci. apply hhs3_p3_crypto_ci in Hci.
  destruct Hci as (_ & Hdh & Hssnz & Heph & Hencs & Henct).
  rewrite (hhs3_p3_crypto_ida _ R L okA) in Hencs. cbn [id_pub] in Hencs.
  assert (Hrs: hs_rstatic (p_hs (hhs3_PB0 x25519 R L)) = mi_pub (hhs3_IB x25519 R)) by reflexivity.
  assert (Hss: hs_ss (p_hs (hhs3_PB0 x25519 R L)) = hhs3_ssa x25519 R).
  { unfold hhs3_PB0, setup_peer_val, hs_initial. cbn [p_hs hs_ss].
    rewrite (hhs3_p3_crypto_ida _ R L okA). unfold precomputed, hhs3_ssa, m_precomputed_model.
    cbn [id_has id_priv]. rewrite okA. reflexivity. }
  rewrite Hrs in Hdh, Hencs, Henct. rewrite Hss in Hssnz, Henct.
  assert (Hdhe: x25519 (mi_priv (hhs3_IB x25519 R)) (x25519 (clamp (i_r I)) basepoint9) =
                x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))).
  { pose proof Hc as [C1 _]. unfold hhs3_IB, mident_of. cbn [mi_priv mi_pub]. rewrite C1.
    apply hhs3_p3_dh; [exact Hc | exact HlB | apply hhs3_p3_crypto_clamp_len; exact Hrlen]. }
  assert (Hcs1: hhs3_cs1 x25519 aead_dec R M1 =
    Some (mi_pub (hhs3_IA x25519 R),
          kdf2 (kdf1 init_ck (x25519 (clamp (i_r I)) basepoint9)) (x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))),
          kdf1 (kdf1 init_ck (x25519 (clamp (i_r I)) basepoint9)) (x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))),
          mix_hash (mix_hash (mix_hash init_hash (mi_pub (hhs3_IB x25519 R))) (x25519 (clamp (i_r I)) basepoint9))
            (im_encs M1))).
  { unfold hhs3_cs1, m_consume_init1_model, consume_init_stage1. cbn [im_eph im_encs id_pub id_priv].
    unfold dh_ok in Hdh |- *. rewrite Heph, Hdhe, Hdh. cbn [negb].
    rewrite Hencs, (aead_dec_enc _ _ Ha). reflexivity. }
  assert (Hssab: mi_ok (hhs3_IB x25519 R) = true -> hhs3_ssb x25519 R = hhs3_ssa x25519 R).
  { intros okB. unfold hhs3_ssb, hhs3_ssa, m_precomputed_model, dh_ok. rewrite okA, okB. cbn [andb].
    assert (Hx2: x25519 (mi_priv (hhs3_IB x25519 R)) (mi_pub (hhs3_IA x25519 R)) =
                 x25519 (mi_priv (hhs3_IA x25519 R)) (mi_pub (hhs3_IB x25519 R))).
    { unfold hhs3_IA, hhs3_IB, mident_of. cbn [mi_priv mi_pub]. apply hhs3_p3_crypto_sw; assumption. }
    rewrite Hx2. reflexivity. }
  assert (Hcs2: mi_ok (hhs3_IB x25519 R) = true -> exists ck h,
    hhs3_p3_cs2 x25519 aead_dec R M1
      (mi_pub (hhs3_IA x25519 R),
       kdf2 (kdf1 init_ck (x25519 (clamp (i_r I)) basepoint9)) (x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))),
       kdf1 (kdf1 init_ck (x25519 (clamp (i_r I)) basepoint9)) (x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))),
       mix_hash (mix_hash (mix_hash init_hash (mi_pub (hhs3_IB x25519 R))) (x25519 (clamp (i_r I)) basepoint9))
         (im_encs M1)) = Some (hhs3_ts I, ck, h)).
  { intros okB. unfold hhs3_p3_cs2, m_consume_init2_model, consume_init_stage2. cbn [im_enct].
    rewrite (Hssab okB), Hssnz. cbn [negb]. rewrite Henct, (aead_dec_enc _ _ Ha).
    eexists; eexists; reflexivity. }
  split.
  - intros CI1 CI2 okB HC1 HC2. rewrite Hcs1 in HC1.
    destruct (Hcs2 okB) as (ck & h & E2).
    assert (HE: CI2 = (hhs3_ts I, ck, h)) by congruence. subst CI2. reflexivity.
  - intros Hok3. unfold hhs3_ok3 in Hok3. destruct MI as [[[[[E encs] enct] ep] ck] h].
    unfold hhs3_ok2 in Hok3. rewrite !andb_true_iff in Hok3.
    destruct Hok3 as (((((((okB & Htsnz) & Hlt) & _) & _) & _) & _) & _).
    unfold hhs3_p3_acc. rewrite okB, Hcs1. cbv beta iota zeta.
    destruct (Hcs2 okB) as (ck2 & h2 & E2). rewrite E2. cbv beta iota zeta.
    assert (Hra: hs_rstatic (p_hs (hhs3_PA0 x25519 R L)) = mi_pub (hhs3_IA x25519 R)) by reflexivity.
    assert (Hta: hs_ts (p_hs (hhs3_PA0 x25519 R L)) = zeros 12) by reflexivity.
    assert (Hla: hs_lic (p_hs (hhs3_PA0 x25519 R L)) = Int64.zero) by reflexivity.
    rewrite Hra, Hta, Hla.
    rewrite hhs3_p3_crypto_newer; [| apply hhs3_p3_crypto_tslen | apply negb_true_iff; exact Htsnz].
    rewrite hhs3_p3_crypto_flood; [| exact Hnow | apply negb_true_iff; exact Hlt].
    unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec _ _) as [_ | N]; [reflexivity | congruence].
Qed.

