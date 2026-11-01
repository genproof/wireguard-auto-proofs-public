(* law handshake, phase P5: completeness 3 (pure).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hhs3_p5_crypto_beq (a b: list byte) : bytes_eqb a b = true -> a = b.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b); [auto | discriminate]. Qed.

Lemma hhs3_p5_crypto_ida (x25519: list byte -> list byte -> list byte) R L :
  mi_ok (hhs3_IA x25519 R) = true ->
  d_id (hhs3_DA x25519 R L) = mkId (mi_pub (hhs3_IA x25519 R)) (mi_priv (hhs3_IA x25519 R)) true.
Proof.
  unfold hhs3_DA, setup_dev, setup_identity, identity_of, hhs3_IA, mident_of. cbn [d_id mi_ok mi_pub mi_priv].
  destruct (memneq_bool (r_rawa R) zeros32); [| discriminate]. cbn [andb]. intros ->. reflexivity.
Qed.

Lemma hhs3_p5_crypto_idb (x25519: list byte -> list byte -> list byte) R L :
  mi_ok (hhs3_IB x25519 R) = true ->
  d_id (hhs3_DB x25519 R L) = mkId (mi_pub (hhs3_IB x25519 R)) (mi_priv (hhs3_IB x25519 R)) true.
Proof.
  unfold hhs3_DB, setup_dev, setup_identity, identity_of, hhs3_IB, mident_of. cbn [d_id mi_ok mi_pub mi_priv].
  destruct (memneq_bool (r_rawb R) zeros32); [| discriminate]. cbn [andb]. intros ->. reflexivity.
Qed.

(* the kernel's create_initiation at success: the message's fields *)
Lemma hhs3_p5_crypto_ci (x25519: list byte -> list byte -> list byte)
  (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
  ID H M r ts idx M1 H1 :
  create_initiation_model x25519 aead_enc ID H M r ts idx = (true, M1, H1) ->
  im_sender M1 = idx /\
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
  inversion HC; subst; clear HC. cbn [im_sender im_eph im_encs im_enct]. auto 10.
Qed.

(* destruct the tests of a model run known to succeed (false branches discriminated) *)
Ltac hhs3_p5_ifs H :=
  repeat (match type of H with context [if negb ?c then _ else _] => destruct c; cbn [negb] in H; try discriminate H end).
Ltac hhs3_p5_opts H :=
  repeat (match type of H with context [match ?d with Some _ => _ | None => _ end] =>
            let x := fresh "x" in destruct d as [x |]; [| discriminate H] end).

Lemma hhs3_p5_crypto_ok (x25519: list byte -> list byte -> list byte) (aead_enc: list byte -> Z -> list byte -> list byte -> list byte) (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) :
  hhs3_p5_crypto_stmt x25519 aead_enc aead_dec.
Proof.
  intros Hc Hx Ha R L I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR Hrun Hai Hcin Hresp Hok4.
  destruct Hai as (okA & Hci & Hmi & _).
  destruct Hcin as (Hcin & Hcs1 & Hcs2 & _).
  destruct Hresp as (Hcr & Hmr & _).
  (* A's initiation: the message and the model *)
  unfold hhs3_ci in Hci. apply hhs3_p5_crypto_ci in Hci.
  destruct Hci as (Hsnd & Heph & Hencs & Henct).
  rewrite (hhs3_p5_crypto_ida _ R L okA) in Hencs. cbn [id_pub] in Hencs.
  assert (Hrs: hs_rstatic (p_hs (hhs3_PB0 x25519 R L)) = mi_pub (hhs3_IB x25519 R)) by reflexivity.
  assert (Hss: hs_ss (p_hs (hhs3_PB0 x25519 R L)) = hhs3_ssa x25519 R).
  { unfold hhs3_PB0, setup_peer_val, hs_initial. cbn [p_hs hs_ss].
    rewrite (hhs3_p5_crypto_ida _ R L okA). unfold precomputed, hhs3_ssa, m_precomputed_model.
    cbn [id_has id_priv]. rewrite okA. reflexivity. }
  rewrite Hrs in Hencs, Henct. rewrite Hss in Henct.
  unfold hhs3_mi, m_create_initiation_model in Hmi. cbv zeta in Hmi.
  rewrite (hhs3_p5_crypto_ida _ R L okA) in Hmi. cbn [id_pub] in Hmi.
  destruct (negb (dh_ok x25519 (clamp (i_r I)) basepoint9)); [discriminate Hmi |].
  destruct (negb (dh_ok x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R)))); [discriminate Hmi |].
  destruct (is_zero (hhs3_ssa x25519 R)); [discriminate Hmi |].
  rewrite <- Hencs in Hmi. rewrite <- Henct in Hmi.
  injection Hmi as HMI.
  change (x25519 (r_rawb R) basepoint9) with (mi_pub (hhs3_IB x25519 R)) in HMI.
  subst MI.
  (* the completeness flags *)
  destruct MR as [[[[Er encn] epr] ckr] hr].
  unfold hhs3_ok4, hhs3_ok3, hhs3_ok2 in Hok4. rewrite !andb_true_iff in Hok4.
  repeat (match goal with H: _ /\ _ |- _ => destruct H end).
  rename H into okB, H11 into Hes, H9 into Hssab, H8 into Hdee, H7 into Hee, H5 into Hdse, H4 into Hse.
  (* B's consume_initiation: pa's handshake *)
  assert (Hst1: consume_init_stage1 x25519 aead_dec (d_id (hhs3_DB x25519 R L)) (hhs3_M1m x25519 R M1) =
                hhs3_cs1 x25519 aead_dec R M1).
  { rewrite (hhs3_p5_crypto_idb _ R L okB). unfold hhs3_cs1, m_consume_init1_model. rewrite okB. reflexivity. }
  assert (Hst2: forall ck h, consume_init_stage2 aead_dec (hs_ss (p_hs (hhs3_PA0 x25519 R L))) ck h (hhs3_M1m x25519 R M1) =
                m_consume_init2_model aead_dec (hhs3_ssb x25519 R) ck h (im_enct M1)).
  { intros ck h. unfold hhs3_PA0, setup_peer_val, hs_initial. cbn [p_hs hs_ss].
    rewrite (hhs3_p5_crypto_idb _ R L okB). unfold precomputed, hhs3_ssb, m_precomputed_model.
    cbn [id_has id_priv]. rewrite okB. reflexivity. }
  unfold hhs3_cin, consume_initiation_model in Hcin.
  rewrite Hst1, (hhs3_p5_crypto_idb _ R L okB), Hcs1 in Hcin. cbn [id_has negb] in Hcin.
  destruct CI1 as [[[s key1] ck1] h1].
  cbn [pk_find] in Hcin.
  destruct (bytes_eqb (hs_rstatic (p_hs (hhs3_PA0 x25519 R L))) s); [| discriminate Hcin].
  assert (Hpg: peer_get (hhs3_PA0 x25519 R L) =
               Some (p_set_refs (hhs3_PA0 x25519 R L) (Int.add Int.one Int.one))) by reflexivity.
  rewrite Hpg in Hcin.
  rewrite Hst2, Hcs2 in Hcin.
  destruct CI2 as [[t ck2] h2].
  destruct (orb _ _); [discriminate Hcin |].
  injection Hcin as HPA1. subst PA1.
  (* B's response: the message and the model *)
  unfold hhs3_cr, hhs3_PA2, create_response_model in Hcr.
  cbn [p_hs p_set_refs p_set_hs hs_state hs_rindex hs_reph hs_rstatic hs_psk hs_hash hs_ck hhs3_PA0
       setup_peer_val hs_initial hhs3_M1m im_set_macs im_eph im_sender] in Hcr.
  rewrite Int.eq_true in Hcr. cbv zeta in Hcr. cbn [negb] in Hcr.
  hhs3_p5_ifs Hcr.
  injection Hcr as HM2 _. subst M2.
  unfold hhs3_mr, m_create_response_model in Hmr.
  cbn [p_hs p_set_refs p_set_hs hs_rstatic hhs3_PA0 setup_peer_val hs_initial] in Hmr.
  cbv zeta in Hmr. hhs3_p5_ifs Hmr.
  injection Hmr as <- <- <- <- <-.
  (* B's chain after stage 2 *)
  unfold hhs3_cs1, m_consume_init1_model, consume_init_stage1 in Hcs1.
  cbv zeta in Hcs1. cbn [id_pub id_priv im_eph im_encs] in Hcs1.
  hhs3_p5_ifs Hcs1. hhs3_p5_opts Hcs1.
  injection Hcs1 as <- <- <- <-.
  unfold m_consume_init2_model, consume_init_stage2 in Hcs2.
  cbv zeta in Hcs2. cbn [im_enct] in Hcs2.
  hhs3_p5_ifs Hcs2. hhs3_p5_opts Hcs2.
  injection Hcs2 as <- <- <-.
  (* A's consume_response *)
  unfold hhs3_p5_acc, hhs3_mcr, m_consume_response_model, consume_resp_crypto.
  cbv zeta. cbn [rm_eph rm_encn rm_receiver hs_eph hs_hash hs_ck hs_psk].
  rewrite okA, Hsnd, Int.eq_true. cbn [andb].
  rewrite Hdee, Hdse. cbn [negb].
  rewrite <- (hhs3_p5_crypto_beq _ _ Hee), <- (hhs3_p5_crypto_beq _ _ Hse).
  rewrite Heph.
  change (clamp (r_rawb R)) with (mi_priv (hhs3_IB x25519 R)).
  change (x25519 (r_rawb R) basepoint9) with (mi_pub (hhs3_IB x25519 R)).
  change (x25519 (r_rawa R) basepoint9) with (mi_pub (hhs3_IA x25519 R)).
  rewrite <- (hhs3_p5_crypto_beq _ _ Hes), <- (hhs3_p5_crypto_beq _ _ Hssab).
  rewrite (aead_dec_enc _ _ Ha).
  split; reflexivity.
Qed.
