(* prim_out (prot_dec3.v: an output byte buffer, emp when empty) vs data_at, for the AEAD piece whose
   chacha_crypt_generic / chacha_crypt / chacha20_crypt specifications (aead_spec3.v) take a NULL-tolerant
   destination since the series patch P23. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_bytes.

Local Open Scope Z_scope.

Section Out3.
Context {cs: compspecs}.

Lemma out3_nz sh (v: list val) p :
  Zlength v <> 0 -> prim_out sh v p = data_at sh (tarray tuchar (Zlength v)) v p.
Proof. intros H. unfold prim_out. rewrite if_false by auto. reflexivity. Qed.

Lemma out3_z sh (v: list val) p : Zlength v = 0 -> prim_out sh v p = emp.
Proof. intros H. unfold prim_out. rewrite if_true by auto. reflexivity. Qed.

Lemma out3_intro_ sh n p :
  0 <= n -> data_at_ sh (tarray tuchar n) p |-- prim_out sh (Zrepeat Vundef n) p.
Proof.
  intros Hn. rewrite data_at__tarray. change (default_val tuchar) with Vundef.
  unfold prim_out. rewrite Zlength_Zrepeat by lia.
  if_tac; [entailer!; rewrite data_at_zero_array_eq; auto | apply derives_refl].
Qed.

Lemma out3_elim sh (v: list val) n p :
  Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  prim_out sh v p |-- data_at sh (tarray tuchar n) v p.
Proof.
  intros <- Hf. unfold prim_out. if_tac.
  - apply Zlength_nil_inv in H. subst v. rewrite data_at_zero_array_eq; auto.
  - apply derives_refl.
Qed.

End Out3.

Lemma out3_cs {cs1 cs2: compspecs} sh (v: list val) p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

(* the AEAD's padding length 0x10 - (len & 0xf), in size_t (series P22: poly1305_update takes a size_t) *)
Lemma out3_pad_len64 z : 0 <= z <= Int64.max_unsigned ->
  Int64.sub (Int64.repr (Int.signed (Int.repr 16)))
    (Int64.and (Int64.repr z) (Int64.repr (Int.signed (Int.repr 15)))) = Int64.repr (16 - z mod 16).
Proof.
  intros Hz. change (Int.signed (Int.repr 16)) with 16. change (Int.signed (Int.repr 15)) with 15.
  assert (Ha: Int64.and (Int64.repr z) (Int64.repr 15) = Int64.repr (z mod 16)).
  { change (Int64.repr 15) with (Int64.sub (Int64.repr 16) Int64.one).
    rewrite <- (Int64.modu_and _ _ (Int64.repr 4)) by reflexivity.
    unfold Int64.modu. rewrite !Int64.unsigned_repr by (rep_lia || (split; [cbv; congruence | rep_lia])).
    reflexivity. }
  rewrite Ha. pose proof (Z.mod_pos_bound z 16).
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.
