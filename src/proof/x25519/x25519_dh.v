(* ======================================================================
   The X25519 Diffie-Hellman agreement, a theorem.

   The law handshake checks UNCONDITIONALLY that B decrypts A's timestamp and derives A's transport keys: this
   needs the two sides' Diffie-Hellman values to agree, i.e. that X25519 commutes on multiples of the base point:
       X25519(a, X25519(b, 9)) = X25519(b, X25519(a, 9))      for 32-byte scalars a, b,
   about x25519_m, the Coq transliteration of curve25519-fiat32.c's curve25519_generic that the body proofs show
   the C code computes (src/proof/x25519/x25519_model.v, x25519_part3.v).  x25519fiat/ (logical root X25519)
   shows that x25519_m refines fiat-crypto's verified Montgomery ladder and derives the agreement from the group
   law of fiat-crypto's Montgomery curve (fiat-crypto, Coqprime and Rewriter, vendored unmodified under
   vendor/fiat-crypto/, see vendor/fiat-crypto/PIN).

   Everything else here is proved: clamping is idempotent, so curve25519_generic does not depend on whether its
   scalar was clamped already. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.x25519.x25519_model.
Require X25519.x25519_dh_agree_proved.   (* x25519fiat/: proved from fiat-crypto *)

Local Open Scope Z_scope.

Theorem x25519_m_dh_agree : forall a b : list byte,
  Zlength a = 32 -> Zlength b = 32 ->
  x25519_m a (x25519_m b basepoint9) = x25519_m b (x25519_m a basepoint9).
Proof. exact X25519.x25519_dh_agree_proved.x25519_m_dh_agree. Qed.

Lemma byte_all (P: byte -> bool) :
  forallb (fun z => P (Byte.repr z)) (map Z.of_nat (seq 0 256)) = true -> forall x, P x = true.
Proof.
  intros H x. rewrite forallb_forall in H. rewrite <- (Byte.repr_unsigned x). apply H.
  pose proof (Byte.unsigned_range x) as R. change Byte.modulus with 256 in R.
  apply in_map_iff. exists (Z.to_nat (Byte.unsigned x)). split; [rewrite Z2Nat.id; lia |].
  apply in_seq. lia.
Qed.

Lemma clamp0_idem x : Byte.and (Byte.and x (Byte.repr 248)) (Byte.repr 248) = Byte.and x (Byte.repr 248).
Proof.
  pose proof (byte_all (fun x => if Byte.eq_dec (Byte.and (Byte.and x (Byte.repr 248)) (Byte.repr 248))
                                       (Byte.and x (Byte.repr 248)) then true else false) ltac:(vm_compute; reflexivity) x) as H.
  cbv beta in H. match goal with H: (if ?c then _ else _) = true |- _ => destruct c; [auto | discriminate] end.
Qed.

Lemma clamp31_idem x :
  Byte.or (Byte.and (Byte.or (Byte.and x (Byte.repr 127)) (Byte.repr 64)) (Byte.repr 127)) (Byte.repr 64) =
  Byte.or (Byte.and x (Byte.repr 127)) (Byte.repr 64).
Proof.
  pose proof (byte_all (fun x => if Byte.eq_dec
      (Byte.or (Byte.and (Byte.or (Byte.and x (Byte.repr 127)) (Byte.repr 64)) (Byte.repr 127)) (Byte.repr 64))
      (Byte.or (Byte.and x (Byte.repr 127)) (Byte.repr 64)) then true else false) ltac:(vm_compute; reflexivity) x) as H.
  cbv beta in H. match goal with H: (if ?c then _ else _) = true |- _ => destruct c; [auto | discriminate] end.
Qed.

Lemma clamp_idem : forall s, clamp (clamp s) = clamp s.
Proof.
  intros s. unfold clamp.
  destruct (zlt 31 (Zlength s)) as [L|L]; [| destruct (zlt 0 (Zlength s)) as [L0|L0]].
  - rewrite (upd_Znth_diff 0 31) by list_solve. rewrite !upd_Znth_same by list_solve.
    rewrite clamp0_idem, clamp31_idem. list_solve.
  - assert (U: forall (l: list byte) v, Zlength l <= 31 -> upd_Znth 31 l v = l)
      by (intros; unfold upd_Znth; destruct (Sumbool.sumbool_and _ _ _ _ _ _); [lia | auto]).
    rewrite !U by list_solve. rewrite upd_Znth_same by list_solve. rewrite clamp0_idem. list_solve.
  - assert (s = []) by (destruct s; [auto | rewrite Zlength_cons in L0; pose proof (Zlength_nonneg s); lia]).
    subst. reflexivity.
Qed.

Lemma x25519_m_clamp : forall s p, x25519_m (clamp s) p = x25519_m s p.
Proof. intros. unfold x25519_m. rewrite clamp_idem. reflexivity. Qed.
