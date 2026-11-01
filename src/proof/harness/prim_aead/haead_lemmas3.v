(*
   the model facts themselves are the hypothesis haead_hyps (haead_defs3.v).  Add proven lemmas freely. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Export WgNoise.proof.harness.prim_aead.haead_defs3.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the block counter                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma haead_advance_length st k : Zlength st = 16 -> Zlength (chacha_advance st k) = 16.
Proof. intros H. unfold chacha_advance. rewrite upd_Znth_Zlength; lia. Qed.

Lemma haead_advance_0 st : Zlength st = 16 -> chacha_advance st 0 = st.
Proof.
  intros H. unfold chacha_advance. rewrite Int.add_zero.
  apply Znth_eq_ext; [rewrite upd_Znth_Zlength; lia |]. intros i Hi. rewrite upd_Znth_Zlength in Hi by lia.
  destruct (Z.eq_dec i 12); [subst; rewrite upd_Znth_same by lia | rewrite upd_Znth_diff by lia]; auto; lia.
Qed.

Lemma haead_advance_repr st k : chacha_advance st (Int.unsigned (Int.repr k)) = chacha_advance st k.
Proof. unfold chacha_advance. rewrite Int.repr_unsigned. reflexivity. Qed.

Lemma haead_advance_add st a b : Zlength st = 16 ->
  chacha_advance (chacha_advance st a) b = chacha_advance st (a + b).
Proof.
  intros H. unfold chacha_advance. rewrite upd_Znth_twice by lia. rewrite upd_Znth_same by lia.
  rewrite Int.add_assoc. f_equal. f_equal. rewrite Int.add_unsigned. apply Int.eqm_samerepr.
  apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

(* ---------------------------------------------------------------------- *)
(* the hypotheses, unpacked                                                *)
(* ---------------------------------------------------------------------- *)

Lemma haead_xaead_enc (HX: haead_facts) key nonce a m : Zlength key = 32 -> Zlength nonce = 24 ->
  aead_enc (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) a m = xaead_enc key nonce a m.
Proof.
  intros. destruct HX as (_ & _ & _ & _ & _ & _ & X). unfold aead_enc, xaead_enc. rewrite X by auto. reflexivity.
Qed.

Lemma haead_xaead_dec (HX: haead_facts) key nonce a c : Zlength key = 32 -> Zlength nonce = 24 ->
  aead_dec (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) a c = xaead_dec key nonce a c.
Proof.
  intros. destruct HX as (_ & _ & _ & _ & _ & _ & X). unfold aead_dec, xaead_dec. rewrite X by auto. reflexivity.
Qed.
