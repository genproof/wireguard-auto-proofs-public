(* assembly glue for the laws over the AEAD piece.
   - The byte-buffer specifications the AEAD units import (aead_imports3 cs: memcpy, memset, memzero_explicit,
     get_unaligned_le32, crypto_memneq) are owned at another compspecs (Libc.CS, Blake2s.CS, Curve25519.CS):
     the owner's instance is a funspec_sub of the importer's, given change_composite_env (make_cs_preserve).
   - A piece given by an existential G (blake2s3_ok): its entries have the calling convention of the
     interface entries they cover. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.subsume_funspec.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.assembly.asm_lib.

Section XCS.
Context {cs1 cs2: compspecs} {CCE: change_composite_env cs1 cs2}.

Lemma xa3_data_at_tuchar sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  rewrite (@data_at_change_composite cs1 cs2 CCE sh (tarray tuchar n) v v); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma xa3_data_at__tuchar sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  rewrite (@data_at__change_composite cs1 cs2 CCE sh (tarray tuchar n)); reflexivity.
Qed.

Lemma xa3_memcpy_sub : funspec_sub (snd (@memcpy_spec cs1)) (snd (@memcpy_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[[[dsh ssh] dst] src] n] bs]. simpl.
  Exists (dsh, ssh, dst, src, n, bs) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xa3_data_at_tuchar, !xa3_data_at__tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

Lemma xa3_memset_sub : funspec_sub (snd (@memset_spec cs1)) (snd (@memset_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[sh p] c] n]. simpl.
  Exists (sh, p, c, n) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xa3_data_at__tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx. simpl.
  rewrite xa3_data_at_tuchar. auto.
Qed.

Lemma xa3_memzero_explicit_sub :
  funspec_sub (snd (@memzero_explicit_spec cs1)) (snd (@memzero_explicit_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[sh p] n]. simpl.
  Exists (sh, p, n) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xa3_data_at__tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx. simpl.
  rewrite xa3_data_at_tuchar. auto.
Qed.

Lemma xa3_get_unaligned_le32_sub :
  funspec_sub (snd (@get_unaligned_le32_spec cs1)) (snd (@get_unaligned_le32_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[sh p] i] bs]. simpl.
  Exists (sh, p, i, bs) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xa3_data_at_tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx. simpl.
  try rewrite !xa3_data_at_tuchar. auto.
Qed.

Lemma xa3_crypto_memneq_sub :
  funspec_sub (snd (@crypto_memneq_spec cs1)) (snd (@crypto_memneq_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[[[[sh1 sh2] p1] p2] n] a] b]. simpl.
  Exists (sh1, sh2, p1, p2, n, a, b) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xa3_data_at_tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx. simpl.
  try rewrite !xa3_data_at_tuchar. auto.
Qed.

End XCS.

(* the entries of a piece G that covers an interface G0 with the same identifiers have G0's calling
   conventions *)
Lemma xa3_cc_of_covers (G G0: funspecs) :
  list_norepet (map fst G) -> map fst G = map fst G0 -> asm_covers G G0 ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G0 ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G.
Proof.
  intros LNR IDS COV CC. unfold asm_covers in COV. rewrite Forall_forall in COV, CC |- *.
  intros [i s] Hin.
  assert (Hi: In i (map fst G0)) by (rewrite <- IDS; apply (in_map fst _ _ Hin)).
  apply in_map_iff in Hi as [[i0 t] [Ei Ht]]; simpl in Ei; subst i0.
  destruct (COV _ Ht) as [s' [Fs' Sub]]; simpl in Fs'.
  rewrite (initial_world.find_id_i _ _ _ Hin LNR) in Fs'. inv Fs'.
  specialize (CC _ Ht); simpl in CC |- *.
  destruct s' as [sig1 cc1 A1 P1 Q1 ? ?], t as [sig2 cc2 A2 P2 Q2 ? ?]; simpl in Sub, CC |- *.
  destruct Sub as [[_ ->] _]. exact CC.
Qed.
