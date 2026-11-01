(* the byte-buffer specifications of libc (memcpy, memset; src/proof/libc/spec.v) at two compspecs:
   the instance of the owner (Libc.CS) is a funspec_sub of the instance an importing unit sees (its own
   compspecs), given a change_composite_env between them (make_cs_preserve).  Used by the assemblies
   (asm_covers of a piece's imports). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.subsume_funspec.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.libc.spec.

Section XCS.
Context {cs1 cs2: compspecs} {CCE: change_composite_env cs1 cs2}.

Lemma xcs_data_at_tuchar sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  rewrite (@data_at_change_composite cs1 cs2 CCE sh (tarray tuchar n) v v); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma xcs_data_at__tuchar sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  rewrite (@data_at__change_composite cs1 cs2 CCE sh (tarray tuchar n)); reflexivity.
Qed.

Lemma xcs_memcpy_sub : funspec_sub (snd (@memcpy_spec cs1)) (snd (@memcpy_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[[[dsh ssh] dst] src] n] bs]. simpl.
  Exists (dsh, ssh, dst, src, n, bs) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xcs_data_at_tuchar, !xcs_data_at__tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

Lemma xcs_memset_sub : funspec_sub (snd (@memset_spec cs1)) (snd (@memset_spec cs2)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[sh p] c] n]. simpl.
  Exists (sh, p, c, n) (@emp mpred _ _).
  rewrite emp_sepcon. rewrite !xcs_data_at__tuchar.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx. simpl.
  rewrite xcs_data_at_tuchar. auto.
Qed.

End XCS.
