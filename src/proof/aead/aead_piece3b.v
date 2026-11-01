(* the AEAD piece with NULL-tolerant decryption (aead_spec3b.aead_G3b).
   - the three new entries are funspec_sub of aead_G3's (an empty destination is emp instead of a data_at of
     length 0; the field_compatible fact of the old precondition is carried in the frame), so every body of
     aead_piece3 (proved against aead_imports3 ++ aead_G3) lifts to aead_imports3 ++ aead_G3b;
   - the three new bodies: aead_decrypt_body3b, aead_entry_body3b.  (the P23 helper
     chacha20_crypt_long and its body aead_long_body3b are gone; aead_G3's chacha20_crypt is NULL-tolerant.) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.common.wg3_iface2.
Require Import WgNoise.proof.aead.aead_spec3b.
Require WgNoise.proof.aead.aead_models_props3.
Require WgNoise.proof.aead.aead_piece3.
Require WgNoise.proof.aead.aead_decrypt_body3b WgNoise.proof.aead.aead_entry_body3b.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* prim_out vs data_at                                                     *)
(* ---------------------------------------------------------------------- *)

Section PrimOut.
Context {cs: compspecs}.

Lemma ap3b_out_intro sh (v: list val) p :
  data_at sh (tarray tuchar (Zlength v)) v p |--
  !! field_compatible (tarray tuchar (Zlength v)) [] p && prim_out sh v p.
Proof.
  unfold prim_out. assert_PROP (field_compatible (tarray tuchar (Zlength v)) [] p) by entailer!.
  if_tac.
  - apply andp_right; [apply prop_right; auto |].
    apply Zlength_nil_inv in H0. subst v. entailer!.
    change (Zlength (@nil val)) with 0 in *. rewrite data_at_zero_array_eq; auto.
  - entailer!.
Qed.

Lemma ap3b_out_elim sh (v: list val) n p :
  Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  prim_out sh v p |-- data_at sh (tarray tuchar n) v p.
Proof.
  intros <- Hf. unfold prim_out. if_tac.
  - apply Zlength_nil_inv in H. subst v. rewrite data_at_zero_array_eq; auto.
  - apply derives_refl.
Qed.

Lemma ap3b_out_intro_ sh n p :
  0 <= n -> data_at_ sh (tarray tuchar n) p |-- prim_out sh (Zrepeat Vundef n) p.
Proof.
  intros Hn. rewrite data_at__tarray. change (default_val tuchar) with Vundef.
  unfold prim_out. rewrite Zlength_Zrepeat by lia. if_tac; [entailer!; rewrite data_at_zero_array_eq; auto | apply derives_refl].
Qed.

Lemma ap3b_out_intro' sh (v: list val) p :
  data_at sh (tarray tuchar (Zlength v)) v p |-- prim_out sh v p.
Proof. sep_apply ap3b_out_intro. apply andp_left2, derives_refl. Qed.

End PrimOut.

Lemma ap3b_dec_len st a c old :
  Zlength st = 16 -> Zlength old = Z.max 0 (Zlength c - 16) ->
  Zlength (match aead_dec_st st a c with Some pt => map Vubyte pt | None => old end) = Zlength old.
Proof.
  intros Hs Ho. destruct (aead_dec_st st a c) eqn:E; auto.
  rewrite Zlength_map. rewrite (aead_models_props3.amp3_dec_len _ _ _ _ Hs E).
  destruct (Z_lt_dec (Zlength c) 16).
  - rewrite (aead_models_props3.amp3_dec_short st a c l0) in E. discriminate.
  - lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* the new specifications are funspec_sub of aead_G3's                     *)
(* ---------------------------------------------------------------------- *)

Lemma ap3b_sub_ddec : funspec_sub (snd __chacha20poly1305_decrypt_spec3b) (snd __chacha20poly1305_decrypt_spec3).
Proof.
  do_funspec_sub. destruct w as [[[[[[[[[[[[dsh dst] old] ssh] src] c] ash] ad] a] csh] state] st] gv].
  Exists (dsh, dst, old, ssh, src, c, ash, ad, a, csh, state, st, gv)
         (!! @field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength old)) [] dst && emp).
  simpl. Intros. try apply andp_left2.
  assert_PROP (@field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength old)) [] dst) as FC by entailer!.
  apply andp_right.
  2: rewrite emp_sepcon; sep_apply (@ap3b_out_intro' Chacha20poly1305.CS dsh old dst); cancel.
  apply prop_right. split; [| split; [exact FC | tauto]].
  intros rho. Intros. rewrite emp_sepcon.
  sep_apply (@ap3b_out_elim Chacha20poly1305.CS dsh
    (match aead_dec_st st a c with Some pt => map Vubyte pt | None => old end) (Zlength old) dst).
  { apply ap3b_dec_len; auto. }
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma ap3b_sub_adec : funspec_sub (snd chacha20poly1305_decrypt_spec3b) (snd chacha20poly1305_decrypt_spec3).
Proof.
  do_funspec_sub. destruct w as [[[[[[[[[[[[[dsh dst] old] ssh] src] c] ash] ad] a] nonce] ksh] key] k] gv].
  Exists (dsh, dst, old, ssh, src, c, ash, ad, a, nonce, ksh, key, k, gv)
         (!! @field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength old)) [] dst && emp).
  simpl. Intros. try apply andp_left2.
  assert_PROP (@field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength old)) [] dst) as FC by entailer!.
  apply andp_right.
  2: rewrite emp_sepcon; sep_apply (@ap3b_out_intro' Chacha20poly1305.CS dsh old dst); cancel.
  apply prop_right. split; [| split; [exact FC | tauto]].
  intros rho. Intros. rewrite emp_sepcon.
  sep_apply (@ap3b_out_elim Chacha20poly1305.CS dsh
    (match aead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) (Zlength old) dst).
  { apply ap3b_dec_len; auto; apply aead_models_props3.amp3_aead_st_len. }
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma ap3b_sub_xdec : funspec_sub (snd xchacha20poly1305_decrypt_spec3b) (snd xchacha20poly1305_decrypt_spec3).
Proof.
  do_funspec_sub. destruct w as [[[[[[[[[[[[[[[dsh dst] old] ssh] src] c] ash] ad] a] nsh] np] nonce] ksh] key] k] gv].
  Exists (dsh, dst, old, ssh, src, c, ash, ad, a, nsh, np, nonce, ksh, key, k, gv)
         (!! @field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength old)) [] dst && emp).
  simpl. Intros. try apply andp_left2.
  assert_PROP (@field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength old)) [] dst) as FC by entailer!.
  apply andp_right.
  2: rewrite emp_sepcon; sep_apply (@ap3b_out_intro' Chacha20poly1305.CS dsh old dst); cancel.
  apply prop_right. split; [| split; [exact FC | tauto]].
  intros rho. Intros. rewrite emp_sepcon.
  sep_apply (@ap3b_out_elim Chacha20poly1305.CS dsh
    (match xaead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) (Zlength old) dst).
  { apply ap3b_dec_len; auto; apply aead_models_props3.amp3_xaead_st_len. }
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

(* ---------------------------------------------------------------------- *)
(* lifting the bodies of aead_piece3 from aead_G3 to aead_G3b              *)
(* ---------------------------------------------------------------------- *)

Lemma ap3b_covers (cs: compspecs) :
  asm_covers (aead_imports3 cs ++ aead_G3b) (aead_imports3 cs ++ aead_G3).
Proof.
  unfold asm_covers, aead_imports3, aead_G3.
  repeat apply Forall_cons; try apply Forall_nil; cbv beta;
  lazymatch goal with
  | |- exists s', _ /\ funspec_sub s' (snd __chacha20poly1305_decrypt_spec3) =>
      exists (snd __chacha20poly1305_decrypt_spec3b); split; [reflexivity | exact ap3b_sub_ddec]
  | |- exists s', _ /\ funspec_sub s' (snd chacha20poly1305_decrypt_spec3) =>
      exists (snd chacha20poly1305_decrypt_spec3b); split; [reflexivity | exact ap3b_sub_adec]
  | |- exists s', _ /\ funspec_sub s' (snd xchacha20poly1305_decrypt_spec3) =>
      exists (snd xchacha20poly1305_decrypt_spec3b); split; [reflexivity | exact ap3b_sub_xdec]
  | |- exists s', _ /\ funspec_sub s' (snd ?x) =>
      exists (snd x); split; [reflexivity | apply funspec_sub_refl]
  end.
Qed.

(* asm_lib.asm_body_lift without the change of compspecs *)
Lemma ap3b_body_lift {cs: compspecs} (V: varspecs) (Gu Gw: funspecs) f ip:
  list_norepet (map fst V ++ map fst Gw) ->
  asm_covers Gw Gu ->
  @semax_body V Gu cs f ip -> @semax_body V Gw cs f ip.
Proof.
  intros LNR HG SB; unfold asm_covers in HG.
  apply (semax_body_subsumption _ _ _ _ _ _ _ SB).
  apply tycontext_sub_i99. split; intro i.
  - rewrite !asm_make_tycontext_g.
    destruct (initial_world.find_id i Gu) as [s|] eqn:E.
    + apply asm_find_id_In in E.
      rewrite Forall_forall in HG; destruct (HG _ E) as [s' [E' S]]; simpl in E'.
      rewrite E'; simpl; rewrite (asm_funspec_sub_type _ _ S); auto.
    + destruct (initial_world.find_id i V) as [t|] eqn:E2; simpl; auto.
      rewrite (asm_norepet_V_G _ _ _ _ LNR E2); auto.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i Gu) as [s|] eqn:E; simpl; auto.
    apply asm_find_id_In in E.
    rewrite Forall_forall in HG; destruct (HG _ E) as [s' [E' S]]; simpl in E'.
    exists s'; split; [exact E'|]. apply seplog.funspec_sub_sub_si. apply funspec_sub_iff. exact S.
Qed.

Lemma ap3b_lnr u : In u aead_units3 ->
  list_norepet (map fst (u_V u) ++ map fst (aead_imports3 (u_cs u) ++ aead_G3b)).
Proof.
  intros Hu. rewrite map_app, aead_G3b_ids.
  simpl in Hu; repeat destruct Hu as [<-|Hu]; try contradiction;
  apply compute_list_norepet_e; vm_compute; reflexivity.
Qed.

Lemma ap3b_verified u ip : In u aead_units3 ->
  verified_in u (aead_imports3 (u_cs u) ++ aead_G3) ip -> verified_in u (aead_imports3 (u_cs u) ++ aead_G3b) ip.
Proof.
  intros Hu [f [Hf SB]]. exists f; split; [exact Hf |].
  exact (ap3b_body_lift _ _ _ f ip (ap3b_lnr u Hu) (ap3b_covers (u_cs u)) SB).
Qed.

(* the templates of prot_dec3.v (lengths < 2^32): same WITH, PARAMS, SEP, POST, stronger PROP *)
Ltac ap3b_sub :=
  do_funspec_sub; lazymatch goal with w: (_ * _)%type |- _ => Exists w emp end;
  repeat match goal with p: (_ * _)%type |- _ => destruct p end;
  simpl; entailer!; try (intros; entailer!).

Lemma ap3b_sub_tdec :
  funspec_sub (snd chacha20poly1305_decrypt_spec3b) (snd (@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS aead_dec)).
Proof. ap3b_sub. Qed.

Lemma ap3b_sub_txdec :
  funspec_sub (snd xchacha20poly1305_decrypt_spec3b) (snd (@xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xaead_dec)).
Proof. ap3b_sub. Qed.

Ltac ap3b_in u H :=
  exists u; split; [simpl; tauto |]; eexists; split; [reflexivity | exact H].

Theorem aead_piece3b :
  piece_ok aead_units3 aead_imports3 aead_G3b /\
  asm_covers aead_G3b (aead_iface3b aead_enc aead_dec xaead_enc xaead_dec).
Proof.
  split.
  2:{ unfold asm_covers, aead_iface3b.
      repeat apply Forall_cons; try apply Forall_nil; cbv beta.
      - exists (snd chacha20poly1305_encrypt_spec3); split; [reflexivity | exact aead_piece3.ap3_sub_aenc].
      - exists (snd chacha20poly1305_decrypt_spec3b); split; [reflexivity | exact ap3b_sub_tdec].
      - exists (snd xchacha20poly1305_encrypt_spec3); split; [reflexivity | exact aead_piece3.ap3_sub_xenc].
      - exists (snd xchacha20poly1305_decrypt_spec3b); split; [reflexivity | exact ap3b_sub_txdec]. }
  split; [rewrite aead_G3b_ids; apply compute_list_norepet_e; vm_compute; reflexivity |].
  destruct aead_piece3.aead_piece3 as [[_ P] _].
  assert (L: Forall (fun ip => exists u, In u aead_units3 /\ verified_in u (aead_imports3 (u_cs u) ++ aead_G3b) ip)
               aead_G3).
  { revert P. apply Forall_impl. intros ip [u [Hu Hv]]. exists u; split; [exact Hu | exact (ap3b_verified u ip Hu Hv)]. }
  clear P. unfold aead_G3 in L at 1. unfold aead_G3b at 2.
  do 28 (apply Forall_cons; [exact (Forall_inv L) |]; apply Forall_inv_tail in L).
  apply Forall_cons; [ap3b_in u_chacha20poly1305 aead_decrypt_body3b.aead_decrypt_bodies3b |];
    apply Forall_inv_tail in L.
  apply Forall_cons; [exact (Forall_inv L) |]; apply Forall_inv_tail in L.
  apply Forall_cons; [ap3b_in u_chacha20poly1305 (proj1 aead_entry_body3b.aead_entry_bodies3b) |];
    apply Forall_inv_tail in L.
  apply Forall_cons; [exact (Forall_inv L) |]; apply Forall_inv_tail in L.
  apply Forall_cons; [ap3b_in u_chacha20poly1305 (proj2 aead_entry_body3b.aead_entry_bodies3b) |].
  apply Forall_nil.
Qed.
