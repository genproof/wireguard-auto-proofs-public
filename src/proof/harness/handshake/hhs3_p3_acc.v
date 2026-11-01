(* law handshake, phase P3: the kernel's consume_initiation vs the harness's acc1 (pure).
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

Lemma hhs3_p3_acc_memcmp (t l: list byte) : Z.leb (WgNoise.proof.libc.spec.memcmp_Z t l) 0 = negb (ts_newer t l).
Proof.
  revert l; induction t as [|x t IH]; intros [|y l]; try reflexivity.
  simpl. destruct (Byte.eq_dec x y) as [E|E].
  - subst. rewrite Byte.eq_true. apply IH.
  - rewrite Byte.eq_false by exact E. destruct (Z.leb_spec (Byte.unsigned x - Byte.unsigned y) 0);
    destruct (Z.gtb_spec (Byte.unsigned x) (Byte.unsigned y)); simpl; try reflexivity; lia.
Qed.

Lemma hhs3_p3_acc_eqb_sym (a b: list byte) : bytes_eqb a b = bytes_eqb b a.
Proof.
  unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b), (list_eq_dec Byte.eq_dec b a);
  congruence.
Qed.

Section Acc.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_acc_has R L : id_has (d_id (hhs3_DB x25519 R L)) = mi_ok (hhs3_IB x25519 R).
Proof. reflexivity. Qed.

Lemma hhs3_p3_acc_id R L : mi_ok (hhs3_IB x25519 R) = true ->
  d_id (hhs3_DB x25519 R L) =
  mkId (mi_pub (hhs3_IB x25519 R)) (mi_priv (hhs3_IB x25519 R)) (mi_ok (hhs3_IB x25519 R)).
Proof.
  unfold hhs3_DB, setup_dev, setup_identity, identity_of, hhs3_IB, mident_of.
  cbn [d_id mi_ok mi_pub mi_priv].
  intros H. apply andb_prop in H. destruct H as [H1 _]. rewrite H1. reflexivity.
Qed.

Lemma hhs3_p3_acc_ss R L : hs_ss (p_hs (hhs3_PA0 x25519 R L)) = hhs3_ssb x25519 R.
Proof. reflexivity. Qed.

Lemma hhs3_p3_acc_get R L : peer_get (hhs3_PA0 x25519 R L) =
  Some (p_set_refs (hhs3_PA0 x25519 R L) (rc_add1 (p_refs (hhs3_PA0 x25519 R L)))).
Proof. reflexivity. Qed.

Lemma hhs3_p3_acc_st1 ID R M1 :
  consume_init_stage1 x25519 aead_dec ID (hhs3_M1m x25519 R M1) =
  consume_init_stage1 x25519 aead_dec ID (mkIM Int.zero Int.zero (im_eph M1) (im_encs M1) [] [] []).
Proof. reflexivity. Qed.

Lemma hhs3_p3_acc_st2 ss ck h R M1 :
  consume_init_stage2 aead_dec ss ck h (hhs3_M1m x25519 R M1) =
  m_consume_init2_model aead_dec ss ck h (im_enct M1).
Proof. reflexivity. Qed.

End Acc.

Lemma hhs3_p3_acc_ok (x25519: list byte -> list byte -> list byte) (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) :
  hhs3_p3_acc_stmt x25519 aead_dec.
Proof.
  intros R L M1 nowb _.
  assert (KEY: hhs3_cin x25519 aead_dec R L M1 nowb =
    if hhs3_p3_acc x25519 aead_dec R L M1 nowb then
      match hhs3_cs1 x25519 aead_dec R M1 with
      | Some CI1 => match hhs3_p3_cs2 x25519 aead_dec R M1 CI1 with
                    | Some CI2 => Some (l_pa L, hhs3_p3_new x25519 R L M1 nowb CI2)
                    | None => None end
      | None => None end
    else None).
  { unfold hhs3_cin, consume_initiation_model, hhs3_p3_acc, hhs3_p3_cs2.
    rewrite hhs3_p3_acc_has.
    destruct (mi_ok (hhs3_IB x25519 R)) eqn:Hok; [| reflexivity].
    cbn [negb andb].
    rewrite (hhs3_p3_acc_id x25519 R L Hok), hhs3_p3_acc_st1.
    change (consume_init_stage1 x25519 aead_dec _ (mkIM Int.zero Int.zero (im_eph M1) (im_encs M1) [] [] []))
      with (hhs3_cs1 x25519 aead_dec R M1).
    destruct (hhs3_cs1 x25519 aead_dec R M1) as [[[[s key] ck1] h1]|]; [| reflexivity].
    cbn [pk_find]. rewrite hhs3_p3_acc_eqb_sym.
    destruct (bytes_eqb s (hs_rstatic (p_hs (hhs3_PA0 x25519 R L)))); [| reflexivity].
    cbn [andb]. rewrite hhs3_p3_acc_get, hhs3_p3_acc_st2.
    change (hs_ss (p_hs (p_set_refs ?P ?r))) with (hs_ss (p_hs P)).
    rewrite hhs3_p3_acc_ss.
    destruct (m_consume_init2_model aead_dec (hhs3_ssb x25519 R) ck1 h1 (im_enct M1))
      as [[[t ck2] h2]|]; [| reflexivity].
    rewrite hhs3_p3_acc_memcmp.
    unfold not_flood.
    destruct (ts_newer t _), (s64_le _ nowb); reflexivity. }
  split; [| split].
  - intros H. rewrite KEY, H. reflexivity.
  - intros CI1 CI2 H1 H2 H3. rewrite KEY, H3, H1, H2. reflexivity.
  - intros a P H. rewrite KEY in H.
    destruct (hhs3_p3_acc x25519 aead_dec R L M1 nowb); [| discriminate].
    destruct (hhs3_cs1 x25519 aead_dec R M1) as [CI1|]; [| discriminate].
    destruct (hhs3_p3_cs2 x25519 aead_dec R M1 CI1) as [[[t ck2] h2]|]; [| discriminate].
    inversion H; subst. split; reflexivity.
Qed.

