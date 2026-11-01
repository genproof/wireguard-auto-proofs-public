(* Byte arrays are the same in every compspecs (tarray tuchar has no composite): for calls across the units
   of the AEAD piece (the same lemma as libc_bytes.v of the libc piece, which is not in this piece's base). *)
Require Import VST.floyd.proofauto.

Lemma aead_align_tuchar_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuchar n) z -> align_compatible_rec ce2 (tarray tuchar n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma aead_field_compatible_tuchar_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (aead_align_tuchar_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (aead_align_tuchar_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma aead_data_at_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply aead_field_compatible_tuchar_cs.
Qed.

Lemma aead_data_at__tuchar_cs {cs1 cs2: compspecs} sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  unfold data_at_, field_at_, field_at. f_equal. f_equal. apply prop_ext. apply aead_field_compatible_tuchar_cs.
Qed.

