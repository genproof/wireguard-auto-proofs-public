(* a struct of the small compspecs CS4 malloc'd / freed at
   ANY world compspecs CSw with cspecs_sub CS4 CSw: its size, legality and alignment at CSw are those at CS4, and
   its memory (data_at_ with the malloc token) is the same at both. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import WgNoise.proof.harness.common4.hc4_cs.

Section Sub.
Variable CSw: compspecs.
Hypothesis HSUB: cspecs_sub CS4 CSw.
Variable id: ident.
Hypothesis HCO: (Maps.PTree.get id (@cenv_cs CS4)) <> None.
Hypothesis HHA: (Maps.PTree.get id (@ha_env_cs CS4)) <> None.
Hypothesis HLA: (Maps.PTree.get id (@la_env_cs CS4)) <> None.

Lemma hc4b_hn_sub_co : (Maps.PTree.get id (@cenv_cs CSw)) = (Maps.PTree.get id (@cenv_cs CS4)).
Proof.
  destruct HSUB as [C _]. specialize (C id). red in C.
  destruct ((Maps.PTree.get id (@cenv_cs CS4))); [auto | contradiction].
Qed.

Lemma hc4b_hn_sub_ha : (Maps.PTree.get id (@ha_env_cs CSw)) = (Maps.PTree.get id (@ha_env_cs CS4)).
Proof.
  destruct HSUB as [_ [C _]]. specialize (C id). red in C.
  destruct ((Maps.PTree.get id (@ha_env_cs CS4))); [auto | contradiction].
Qed.

Lemma hc4b_hn_sub_la : (Maps.PTree.get id (@la_env_cs CSw)) = (Maps.PTree.get id (@la_env_cs CS4)).
Proof.
  destruct HSUB as [_ [_ C]]. specialize (C id). red in C.
  destruct ((Maps.PTree.get id (@la_env_cs CS4))); [auto | contradiction].
Qed.

Lemma hc4b_hn_sub_sizeof a : @sizeof CSw (Tstruct id a) = @sizeof CS4 (Tstruct id a).
Proof. simpl. rewrite hc4b_hn_sub_co. reflexivity. Qed.

Lemma hc4b_hn_sub_cl a : @complete_legal_cosu_type (@cenv_cs CSw) (Tstruct id a) = @complete_legal_cosu_type (@cenv_cs CS4) (Tstruct id a).
Proof. simpl. rewrite hc4b_hn_sub_co. reflexivity. Qed.

Lemma hc4b_hn_sub_na na a : @natural_aligned CSw na (Tstruct id a) = @natural_aligned CS4 na (Tstruct id a).
Proof.
  pose proof hc4b_hn_sub_ha as Hha. pose proof hc4b_hn_sub_la as Hla.
  unfold natural_aligned, is_aligned, hardware_alignof, legal_alignas_type. cbv beta iota. rewrite Hha.
  change (@Maps.PTree.get bool id (@la_env_cs CSw)) with (@Maps.PTree.get legal_alignas_obs id (@la_env_cs CSw)).
  rewrite Hla. reflexivity.
Qed.

(* the memory of a malloc'd struct, at CSw and at CS4 *)
Lemma hc4b_hn_sub_to4 sh p :
  @complete_legal_cosu_type (@cenv_cs CS4) (Tstruct id noattr) = true ->
  @natural_aligned CS4 natural_alignment (Tstruct id noattr) = true ->
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CSw sh (Tstruct id noattr) p |--
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CS4 sh (Tstruct id noattr) p.
Proof.
  intros Hcl Hna.
  sep_apply (malloc_token_local_facts Ews (Tstruct id noattr) p). Intros.
  rewrite !data_at__memory_block. Intros. rewrite hc4b_hn_sub_sizeof.
  apply andp_right; [|cancel]. apply prop_right.
  apply malloc_compatible_field_compatible; auto.
  rewrite <- hc4b_hn_sub_sizeof; auto.
Qed.

Lemma hc4b_hn_sub_tow sh p :
  @complete_legal_cosu_type (@cenv_cs CS4) (Tstruct id noattr) = true ->
  @natural_aligned CS4 natural_alignment (Tstruct id noattr) = true ->
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CS4 sh (Tstruct id noattr) p |--
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CSw sh (Tstruct id noattr) p.
Proof.
  intros Hcl Hna.
  sep_apply (malloc_token_local_facts Ews (Tstruct id noattr) p). Intros.
  rewrite !data_at__memory_block. Intros. rewrite hc4b_hn_sub_sizeof.
  apply andp_right; [|cancel]. apply prop_right.
  apply malloc_compatible_field_compatible; auto.
  - rewrite hc4b_hn_sub_cl; auto.
  - rewrite hc4b_hn_sub_na; auto.
Qed.

End Sub.
