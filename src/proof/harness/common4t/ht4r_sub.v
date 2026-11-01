(* ref_aead_decrypt's
   NULL-tolerant specification (ht4r_spec.v) at W_prim_aead (the body's) covers its copy at ANY compspecs (a law's
   main imports it at its world): only byte arrays and the u32 array minusp are involved. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.subsume_funspec.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.

Local Open Scope Z_scope.

Lemma ht4r_align_tuint_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuint n) z -> align_compatible_rec ce2 (tarray tuint n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma ht4r_field_compatible_tuint_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuint n) [] p <-> @field_compatible cs2 (tarray tuint n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (ht4r_align_tuint_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (ht4r_align_tuint_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma ht4r_minusp_cs {cs1 cs2: compspecs} mp gv : @ht4_minusp cs1 mp gv = @ht4_minusp cs2 mp gv.
Proof.
  unfold ht4_minusp, data_at, field_at. f_equal. f_equal. apply prop_ext. apply ht4r_field_compatible_tuint_cs.
Qed.

Lemma ht4r_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

Lemma ht4r_prim_out_cs {cs1 cs2: compspecs} sh v p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

Lemma ht4r_dec_sub (cs: compspecs) (mp: ident) :
  funspec_sub (snd (ref_aead_decrypt_spec_n W_prim_aead mp)) (snd (ref_aead_decrypt_spec_n cs mp)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl.
  rewrite emp_sepcon.
  rewrite !(@ht4r_prim_bytes_cs W_prim_aead cs), (@ht4r_prim_out_cs W_prim_aead cs),
    (@aead_data_at_tuchar_cs W_prim_aead cs), (@ht4r_minusp_cs W_prim_aead cs).
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right; intros rho; rewrite emp_sepcon; apply andp_left2.
  rewrite !(@ht4r_prim_bytes_cs cs W_prim_aead), (@ht4r_prim_out_cs cs W_prim_aead),
    (@aead_data_at_tuchar_cs cs W_prim_aead), (@ht4r_minusp_cs cs W_prim_aead).
  apply derives_refl.
Qed.
