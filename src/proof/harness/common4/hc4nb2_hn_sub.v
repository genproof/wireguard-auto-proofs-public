(* a struct of the small compspecs CS4nb malloc'd / freed at
   ANY world compspecs CSw with cspecs_sub CS4nb CSw: its size, legality and alignment at CSw are those at CS4nb, and
   its memory (data_at_ with the malloc token) is the same at both. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4a_lib.

Section Sub.
Variable CSw: compspecs.
Hypothesis HSUB: cspecs_sub CS4nb CSw.
Variable id: ident.
Hypothesis HCO: (Maps.PTree.get id (@cenv_cs CS4nb)) <> None.
Hypothesis HHA: (Maps.PTree.get id (@ha_env_cs CS4nb)) <> None.
Hypothesis HLA: (Maps.PTree.get id (@la_env_cs CS4nb)) <> None.

Lemma hc4nb2_hn_sub_co : (Maps.PTree.get id (@cenv_cs CSw)) = (Maps.PTree.get id (@cenv_cs CS4nb)).
Proof.
  destruct HSUB as [C _]. specialize (C id). red in C.
  destruct ((Maps.PTree.get id (@cenv_cs CS4nb))); [auto | contradiction].
Qed.

Lemma hc4nb2_hn_sub_ha : (Maps.PTree.get id (@ha_env_cs CSw)) = (Maps.PTree.get id (@ha_env_cs CS4nb)).
Proof.
  destruct HSUB as [_ [C _]]. specialize (C id). red in C.
  destruct ((Maps.PTree.get id (@ha_env_cs CS4nb))); [auto | contradiction].
Qed.

Lemma hc4nb2_hn_sub_la : (Maps.PTree.get id (@la_env_cs CSw)) = (Maps.PTree.get id (@la_env_cs CS4nb)).
Proof.
  destruct HSUB as [_ [_ C]]. specialize (C id). red in C.
  destruct ((Maps.PTree.get id (@la_env_cs CS4nb))); [auto | contradiction].
Qed.

Lemma hc4nb2_hn_sub_sizeof a : @sizeof CSw (Tstruct id a) = @sizeof CS4nb (Tstruct id a).
Proof. simpl. rewrite hc4nb2_hn_sub_co. reflexivity. Qed.

Lemma hc4nb2_hn_sub_cl a : @complete_legal_cosu_type (@cenv_cs CSw) (Tstruct id a) = @complete_legal_cosu_type (@cenv_cs CS4nb) (Tstruct id a).
Proof. simpl. rewrite hc4nb2_hn_sub_co. reflexivity. Qed.

Lemma hc4nb2_hn_sub_na na a : @natural_aligned CSw na (Tstruct id a) = @natural_aligned CS4nb na (Tstruct id a).
Proof.
  pose proof hc4nb2_hn_sub_ha as Hha. pose proof hc4nb2_hn_sub_la as Hla.
  unfold natural_aligned, is_aligned, hardware_alignof, legal_alignas_type. cbv beta iota. rewrite Hha.
  change (@Maps.PTree.get bool id (@la_env_cs CSw)) with (@Maps.PTree.get legal_alignas_obs id (@la_env_cs CSw)).
  rewrite Hla. reflexivity.
Qed.

(* the memory of a malloc'd struct, at CSw and at CS4nb *)
Lemma hc4nb2_hn_sub_to4 sh p :
  @complete_legal_cosu_type (@cenv_cs CS4nb) (Tstruct id noattr) = true ->
  @natural_aligned CS4nb natural_alignment (Tstruct id noattr) = true ->
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CSw sh (Tstruct id noattr) p |--
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CS4nb sh (Tstruct id noattr) p.
Proof.
  intros Hcl Hna.
  sep_apply (malloc_token_local_facts Ews (Tstruct id noattr) p). Intros.
  rewrite !data_at__memory_block. Intros. rewrite hc4nb2_hn_sub_sizeof.
  apply andp_right; [|cancel]. apply prop_right.
  apply malloc_compatible_field_compatible; auto.
  rewrite <- hc4nb2_hn_sub_sizeof; auto.
Qed.

Lemma hc4nb2_hn_sub_tow sh p :
  @complete_legal_cosu_type (@cenv_cs CS4nb) (Tstruct id noattr) = true ->
  @natural_aligned CS4nb natural_alignment (Tstruct id noattr) = true ->
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CS4nb sh (Tstruct id noattr) p |--
  @malloc_token CSw Ews (Tstruct id noattr) p * @data_at_ CSw sh (Tstruct id noattr) p.
Proof.
  intros Hcl Hna.
  sep_apply (malloc_token_local_facts Ews (Tstruct id noattr) p). Intros.
  rewrite !data_at__memory_block. Intros. rewrite hc4nb2_hn_sub_sizeof.
  apply andp_right; [|cancel]. apply prop_right.
  apply malloc_compatible_field_compatible; auto.
  - rewrite hc4nb2_hn_sub_cl; auto.
  - rewrite hc4nb2_hn_sub_na; auto.
Qed.

End Sub.

(* the hypothesis of the statements (cspecs_sub CS4 CSw) gives the one at CS4nb *)
Lemma hc4nb2_hn_sub_nb4 : cspecs_sub CS4nb CS4.
Proof. hc4a_cssub. Qed.

Lemma hc4nb2_hn_sub_trans (CSw: compspecs) : cspecs_sub CS4 CSw -> cspecs_sub CS4nb CSw.
Proof.
  intros [A [B C]]. destruct hc4nb2_hn_sub_nb4 as [A' [B' C']].
  split3; [exact (cenv_sub_trans A' A) | exact (ha_env_cs_sub_trans B' B) | exact (la_env_cs_sub_trans C' C)].
Qed.
