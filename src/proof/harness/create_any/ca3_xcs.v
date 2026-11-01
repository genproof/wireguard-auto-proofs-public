(* law create_any: assembly glue.  The byte-buffer specifications
   (libc, the shared inlines, the primitive templates) mention only byte arrays, the same in every compspecs:
   the owner's instance (at its unit's compspecs) is a funspec_sub of any importer's instance. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.assembly.asm_lib.

Section X.
Context {cs1 cs2: compspecs}.

Lemma ca3_prim_bytes_cs sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. if_tac; auto. apply data_at_tarray_tuchar_cs. Qed.

Lemma ca3_prim_out_cs sh v p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. if_tac; auto. apply data_at_tarray_tuchar_cs. Qed.

Lemma ca3_zero_page_cs gv : @zero_page cs1 gv = @zero_page cs2 gv.
Proof. unfold zero_page. apply data_at_tarray_tuchar_cs. Qed.

Lemma ca3_curve25519_globals_cs gv : @curve25519_globals cs1 gv = @curve25519_globals cs2 gv.
Proof. unfold curve25519_globals. rewrite !(@data_at_tarray_tuchar_cs cs1 cs2). reflexivity. Qed.

Ltac ca3_rw :=
  repeat first [ rewrite (@data_at_tarray_tuchar_cs cs1 cs2)
               | rewrite (@data_at__tarray_tuchar_cs cs1 cs2)
               | rewrite ca3_prim_bytes_cs | rewrite ca3_prim_out_cs | rewrite ca3_zero_page_cs
               | rewrite ca3_curve25519_globals_cs ].

Ltac ca3_sub :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; ca3_rw;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; ca3_rw;
  first [apply derives_refl | auto].

Lemma ca3_memcpy_sub : funspec_sub (snd (@memcpy_spec cs1)) (snd (@memcpy_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_memset_sub : funspec_sub (snd (@memset_spec cs1)) (snd (@memset_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_memcmp_sub : funspec_sub (snd (@memcmp_spec cs1)) (snd (@memcmp_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_memzero_explicit_sub :
  funspec_sub (snd (@memzero_explicit_spec cs1)) (snd (@memzero_explicit_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_get_unaligned_le32_sub :
  funspec_sub (snd (@get_unaligned_le32_spec cs1)) (snd (@get_unaligned_le32_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_crypto_memneq_sub :
  funspec_sub (snd (@crypto_memneq_spec cs1)) (snd (@crypto_memneq_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3___crypto_memneq_sub :
  funspec_sub (snd (@__crypto_memneq_spec cs1)) (snd (@__crypto_memneq_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_clamp_secret_sub :
  funspec_sub (snd (@curve25519_clamp_secret_spec cs1)) (snd (@curve25519_clamp_secret_spec cs2)).
Proof. ca3_sub. Qed.
Lemma ca3_curve25519_generic_sub x :
  funspec_sub (snd (@curve25519_generic_spec_of cs1 x)) (snd (@curve25519_generic_spec_of cs2 x)).
Proof. ca3_sub. Qed.
Lemma ca3_curve25519_sub x :
  funspec_sub (snd (@curve25519_spec_of cs1 x)) (snd (@curve25519_spec_of cs2 x)).
Proof. ca3_sub. Qed.
Lemma ca3_generate_public_sub x :
  funspec_sub (snd (@curve25519_generate_public_spec_of cs1 x))
              (snd (@curve25519_generate_public_spec_of cs2 x)).
Proof. ca3_sub. Qed.
Lemma ca3_encrypt_sub enc :
  funspec_sub (snd (@chacha20poly1305_encrypt_spec_of cs1 enc)) (snd (@chacha20poly1305_encrypt_spec_of cs2 enc)).
Proof. ca3_sub. Qed.
Lemma ca3_xencrypt_sub xenc :
  funspec_sub (snd (@xchacha20poly1305_encrypt_spec_of cs1 xenc))
              (snd (@xchacha20poly1305_encrypt_spec_of cs2 xenc)).
Proof. ca3_sub. Qed.
Lemma ca3_decrypt3_sub dec :
  funspec_sub (snd (@chacha20poly1305_decrypt_spec_of3 cs1 dec))
              (snd (@chacha20poly1305_decrypt_spec_of3 cs2 dec)).
Proof. ca3_sub. Qed.
Lemma ca3_xdecrypt3_sub xdec :
  funspec_sub (snd (@xchacha20poly1305_decrypt_spec_of3 cs1 xdec))
              (snd (@xchacha20poly1305_decrypt_spec_of3 cs2 xdec)).
Proof. ca3_sub. Qed.

End X.

(* the entries of a piece G that covers an interface G0 with the same identifiers have G0's calling
   conventions *)
Lemma ca3_cc_of_covers (G G0: funspecs) :
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
