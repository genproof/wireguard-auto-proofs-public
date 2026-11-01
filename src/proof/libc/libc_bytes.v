(* Byte buffers across compspecs.

   A byte array `tarray tuchar n` has no composite: its data_at / data_at_ / memory_block are the same
   predicates in every compspecs.  These lemmas convert between two ARBITRARY compspecs (no
   change_composite_env instance needed), e.g. between the world's CSw (malloc_spec', calloc_spec) and
   a unit's own compspecs. *)
Require Import VST.floyd.proofauto.

Section Bytes.
Context {cs1 cs2: compspecs}.

Lemma align_compatible_rec_tarray_tuchar: forall (ce: composite_env) n z,
  align_compatible_rec ce (tarray tuchar n) z.
Proof.
  intros. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma field_compatible_tarray_tuchar_cs: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (align_compatible_rec_tarray_tuchar (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (align_compatible_rec_tarray_tuchar (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma data_at_tarray_tuchar_cs: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply field_compatible_tarray_tuchar_cs.
Qed.

Lemma data_at__tarray_tuchar_cs: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply data_at_tarray_tuchar_cs.
Qed.

End Bytes.
