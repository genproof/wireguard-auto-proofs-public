(* the interfaces v3 (wg3_iface2.v / wg3_iface3.v) give the hypotheses of the
   laws' `<law>_safe3_from` lemmas: the AEAD piece covers prim_api's decrypt templates too
   (the NULL-tolerant templates of prot_dec3 are stronger: funspec_sub), and the default calling conventions. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.common.wg3_iface3.

Local Open Scope Z_scope.

Section Sub.
Context {cs: compspecs}.

Lemma prot3c_prim_out_ne sh (v: list val) p :
  Zlength v <> 0 -> @prim_out cs sh v p = data_at sh (tarray tuchar (Zlength v)) v p.
Proof. intros. unfold prim_out. rewrite if_false by auto. reflexivity. Qed.

Lemma prot3c_prim_out_nil sh p : @prim_out cs sh [] p = emp.
Proof. reflexivity. Qed.

Lemma prot3c_dec_sub enc dec : aead_props enc dec ->
  funspec_sub (snd (@chacha20poly1305_decrypt_spec_of3 cs dec)) (snd (@chacha20poly1305_decrypt_spec_of cs dec)).
Proof.
  intros AP. do_funspec_sub.
  destruct w as [[[[[[[[[[[[[dsh dst] old] ssh] src] c] ash] ad] a] nonce] ksh] key] k] gv].
  destruct (Z.eq_dec (Zlength old) 0) as [E0|NE].
  - apply Zlength_nil_inv in E0. subst old.
    Exists (dsh, dst, @nil val, ssh, src, c, ash, ad, a, nonce, ksh, key, k, gv)
           (data_at dsh (tarray tuchar (Zlength (@nil val))) (@nil val) dst).
    rewrite prot3c_prim_out_nil. entailer!.
    intros. Intros. rewrite Zlength_nil in *.
    destruct (dec k nonce a c) as [pt|] eqn:D.
    + assert (pt = []) as ->.
      { apply (aead_dec_length _ _ AP) in D. apply Zlength_nil_inv. pose proof (Zlength_nonneg pt). lia. }
      simpl map. rewrite prot3c_prim_out_nil. entailer!.
    + rewrite prot3c_prim_out_nil. entailer!.
  - Exists (dsh, dst, old, ssh, src, c, ash, ad, a, nonce, ksh, key, k, gv) emp.
    rewrite prot3c_prim_out_ne by auto. entailer!.
    intros. Intros.
    destruct (dec k nonce a c) as [pt|] eqn:D.
    + assert (Zlength (map Vubyte pt) = Zlength old) as EL.
      { apply (aead_dec_length _ _ AP) in D. rewrite Zlength_map. lia. }
      rewrite prot3c_prim_out_ne by lia. rewrite EL. entailer!.
    + rewrite prot3c_prim_out_ne by auto. entailer!.
Qed.

Lemma prot3c_xdec_sub enc dec : xaead_props enc dec ->
  funspec_sub (snd (@xchacha20poly1305_decrypt_spec_of3 cs dec)) (snd (@xchacha20poly1305_decrypt_spec_of cs dec)).
Proof.
  intros AP. do_funspec_sub.
  destruct w as [[[[[[[[[[[[[[[dsh dst] old] ssh] src] c] ash] ad] a] nsh] np] nonce] ksh] key] k] gv].
  destruct (Z.eq_dec (Zlength old) 0) as [E0|NE].
  - apply Zlength_nil_inv in E0. subst old.
    Exists (dsh, dst, @nil val, ssh, src, c, ash, ad, a, nsh, np, nonce, ksh, key, k, gv)
           (data_at dsh (tarray tuchar (Zlength (@nil val))) (@nil val) dst).
    rewrite prot3c_prim_out_nil. entailer!.
    intros. Intros. rewrite Zlength_nil in *.
    destruct (dec k nonce a c) as [pt|] eqn:D.
    + assert (pt = []) as ->.
      { apply (xaead_dec_length _ _ AP) in D. apply Zlength_nil_inv. pose proof (Zlength_nonneg pt). lia. }
      simpl map. rewrite prot3c_prim_out_nil. entailer!.
    + rewrite prot3c_prim_out_nil. entailer!.
  - Exists (dsh, dst, old, ssh, src, c, ash, ad, a, nsh, np, nonce, ksh, key, k, gv) emp.
    rewrite prot3c_prim_out_ne by auto. entailer!.
    intros. Intros.
    destruct (dec k nonce a c) as [pt|] eqn:D.
    + assert (Zlength (map Vubyte pt) = Zlength old) as EL.
      { apply (xaead_dec_length _ _ AP) in D. rewrite Zlength_map. lia. }
      rewrite prot3c_prim_out_ne by lia. rewrite EL. entailer!.
    + rewrite prot3c_prim_out_ne by auto. entailer!.
Qed.
End Sub.

Lemma prot3c_covers_sub G i s1 s2 :
  asm_covers G [(i, s1)] -> funspec_sub s1 s2 -> asm_covers G [(i, s2)].
Proof.
  intros C S. inv C. destruct H1 as (s' & F & S1). constructor; [| constructor].
  exists s'. split; [exact F |]. eapply funspec_sub_trans; eauto.
Qed.

Lemma prot3c_covers_cons G a l : asm_covers G (a :: l) <-> asm_covers G [a] /\ asm_covers G l.
Proof.
  split; [intros C; inv C; split; [constructor; [auto | constructor] | auto] |].
  intros [C1 C2]. inv C1. constructor; auto.
Qed.

(* the AEAD clause of every law's `<law>_safe3_from` *)
Lemma prot3c_aead : aead3b_ok ->
  exists (G: funspecs) enc dec xenc xdec,
     aead_props enc dec /\ xaead_props xenc xdec /\
     piece_ok aead_units3 aead_imports3 G /\ map fst G = aead_idents3 /\
     asm_covers G (aead_iface3 enc dec xenc xdec) /\
     asm_covers G [@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS dec;
                   @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xdec] /\
     Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G.
Proof.
  intros (G & enc & dec & xenc & xdec & AP & XP & HP & HI & HC & HCC).
  exists G, enc, dec, xenc, xdec. split; [exact AP |]. split; [exact XP |]. split; [exact HP |].
  split; [exact HI |].
  unfold aead_iface3b in HC.
  apply prot3c_covers_cons in HC. destruct HC as [C1 HC].
  apply prot3c_covers_cons in HC. destruct HC as [C2 HC].
  apply prot3c_covers_cons in HC. destruct HC as [C3 C4].
  split; [| split; [| exact HCC]].
  - unfold aead_iface3.
    apply prot3c_covers_cons. split; [exact C1 |].
    apply prot3c_covers_cons. split; [eapply prot3c_covers_sub; [exact C2 | apply (prot3c_dec_sub enc); exact AP] |].
    apply prot3c_covers_cons. split; [exact C3 |].
    eapply prot3c_covers_sub; [exact C4 | apply (prot3c_xdec_sub xenc); exact XP].
  - apply prot3c_covers_cons. split; [exact C2 | exact C4].
Qed.

(* the x25519 clause of every law's `<law>_safe3_from` (handshake: plus the two X25519 facts) *)
Lemma prot3c_x25519 : x25519_ok3c ->
  exists (G: funspecs) x,
     x25519_props x /\ piece_ok x25519_units3 x25519_imports3 G /\ map fst G = x25519_idents3 /\
     asm_covers G (x25519_iface3 x) /\
     Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G /\
     x25519_clamp_inv x /\ x25519_dh_agree x.
Proof.
  intros (G & x & XP & HP & HI & HC & HCC & CI & DA).
  exists G, x. tauto.
Qed.
