(*
   The bodies: the proofs against aead_spec.aead_G_def (aead_permute_body, aead_block_body,
   aead_chacha_body, aead_poly_small_body: proven) lifted to aead_G3 by funspec_sub (asm_lib.asm_body_lift
   with the same compspecs), and the new aead_*_body3.v files.  chacha_crypt_generic,
   chacha_crypt and chacha20_crypt are aead_chacha_body3.v's (NULL-tolerant destination, size_t), the P23 helper
   bodies are gone. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require WgNoise.proof.aead.aead_permute_body WgNoise.proof.aead.aead_block_body
        WgNoise.proof.aead.aead_chacha_body WgNoise.proof.aead.aead_poly_small_body.
Require WgNoise.proof.aead.aead_small_body3 WgNoise.proof.aead.aead_donna_blocks_body3
        WgNoise.proof.aead.aead_donna_emit_body3 WgNoise.proof.aead.aead_poly_update_body3
        WgNoise.proof.aead.aead_poly_final_body3 WgNoise.proof.aead.aead_chacha_crypt3
        WgNoise.proof.aead.aead_encrypt_body3 WgNoise.proof.aead.aead_decrypt_body3
        WgNoise.proof.aead.aead_entry_body3.
Require Import WgNoise.proof.protocol.prot_dec3 WgNoise.proof.aead.aead_out3.
Require WgNoise.proof.aead.aead_long3_model.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the new specifications are funspec_sub of the old ones (weaker PROP)    *)
(* ---------------------------------------------------------------------- *)

Ltac ap3_sub :=
  do_funspec_sub; lazymatch goal with w: (_ * _)%type |- _ => Exists w emp end;
  repeat match goal with p: (_ * _)%type |- _ => destruct p end;
  simpl; entailer!; try (intros; entailer!).

Lemma ap3_sub_update : funspec_sub (snd poly1305_update_spec3) (snd poly1305_update_spec).
Proof. unfold poly1305_update_spec3. apply funspec_sub_refl. Qed.

(* the NULL-tolerant destination (prim_out) of aead_G3's chacha functions vs aead_spec.v's data_at_
   (the field_compatible fact of the old precondition is carried in the frame) *)
Lemma ap3_sub_generic : funspec_sub (snd chacha_crypt_generic_spec3) (snd chacha_crypt_generic_spec).
Proof.
  do_funspec_sub. destruct w as [[[[[[[[ssh state] st] dsh] dst] msh] src] m] nr].
  Exists (ssh, state, st, dsh, dst, msh, src, m, nr)
         (!! @field_compatible Chacha.CS (tarray tuchar (Zlength m)) [] dst && emp).
  simpl. Intros. try apply andp_left2.
  assert_PROP (@field_compatible Chacha.CS (tarray tuchar (Zlength m)) [] dst) as FC by entailer!.
  apply andp_right.
  2: rewrite emp_sepcon; sep_apply (@out3_intro_ Chacha.CS dsh (Zlength m) dst (Zlength_nonneg m)); cancel.
  apply prop_right. split; [| split; [exact FC | tauto]].
  intros rho. Intros. rewrite emp_sepcon.
  change (let (q, _) := Z.div_eucl nr 2 in q) with (nr / 2).
  sep_apply (@out3_elim Chacha.CS dsh (map Vubyte (chacha_xor (Z.to_nat (nr / 2)) st m)) (Zlength m) dst).
  { rewrite Zlength_map. apply aead_long3_model.lg3_Zlength_chacha_xor; auto. }
  cancel.
Qed.

Lemma ap3_sub_crypt : funspec_sub (snd chacha_crypt_spec3) (snd chacha_crypt_spec).
Proof.
  do_funspec_sub. destruct w as [[[[[[[[ssh state] st] dsh] dst] msh] src] m] nr].
  Exists (ssh, state, st, dsh, dst, msh, src, m, nr)
         (!! @field_compatible Chacha.CS (tarray tuchar (Zlength m)) [] dst && emp).
  simpl. Intros. try apply andp_left2.
  assert_PROP (@field_compatible Chacha.CS (tarray tuchar (Zlength m)) [] dst) as FC by entailer!.
  apply andp_right.
  2: rewrite emp_sepcon; sep_apply (@out3_intro_ Chacha.CS dsh (Zlength m) dst (Zlength_nonneg m)); cancel.
  apply prop_right. split; [| split; [exact FC | tauto]].
  intros rho. Intros. rewrite emp_sepcon.
  change (let (q, _) := Z.div_eucl nr 2 in q) with (nr / 2).
  sep_apply (@out3_elim Chacha.CS dsh (map Vubyte (chacha_xor (Z.to_nat (nr / 2)) st m)) (Zlength m) dst).
  { rewrite Zlength_map. apply aead_long3_model.lg3_Zlength_chacha_xor; auto. }
  cancel.
Qed.

Lemma ap3_sub_c20 : funspec_sub (snd chacha20_crypt_spec3) (snd chacha20_crypt_spec).
Proof.
  do_funspec_sub. destruct w as [[[[[[[ssh state] st] dsh] dst] msh] src] m].
  Exists (ssh, state, st, dsh, dst, msh, src, m)
         (!! @field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength m)) [] dst && emp).
  simpl. Intros. try apply andp_left2.
  assert_PROP (@field_compatible Chacha20poly1305.CS (tarray tuchar (Zlength m)) [] dst) as FC by entailer!.
  apply andp_right.
  2: rewrite emp_sepcon; sep_apply (@out3_intro_ Chacha20poly1305.CS dsh (Zlength m) dst (Zlength_nonneg m)); cancel.
  apply prop_right. split; [| split; [exact FC | tauto]].
  intros rho. Intros. rewrite emp_sepcon.
  sep_apply (@out3_elim Chacha20poly1305.CS dsh (map Vubyte (chacha_xor 10 st m)) (Zlength m) dst).
  { rewrite Zlength_map. apply aead_long3_model.lg3_Zlength_chacha_xor; auto. }
  cancel.
Qed.

Lemma ap3_sub_enc : funspec_sub (snd __chacha20poly1305_encrypt_spec3) (snd __chacha20poly1305_encrypt_spec).
Proof. ap3_sub. Qed.

Lemma ap3_sub_dec : funspec_sub (snd __chacha20poly1305_decrypt_spec3) (snd __chacha20poly1305_decrypt_spec).
Proof. ap3_sub. Qed.

Lemma ap3_sub_aenc : funspec_sub (snd chacha20poly1305_encrypt_spec3) (snd chacha20poly1305_encrypt_spec).
Proof. ap3_sub. Qed.

Lemma ap3_sub_adec : funspec_sub (snd chacha20poly1305_decrypt_spec3) (snd chacha20poly1305_decrypt_spec).
Proof. ap3_sub. Qed.

Lemma ap3_sub_xenc : funspec_sub (snd xchacha20poly1305_encrypt_spec3) (snd xchacha20poly1305_encrypt_spec).
Proof. ap3_sub. Qed.

Lemma ap3_sub_xdec : funspec_sub (snd xchacha20poly1305_decrypt_spec3) (snd xchacha20poly1305_decrypt_spec).
Proof. ap3_sub. Qed.

(* ---------------------------------------------------------------------- *)
(* lifting the bodies from aead_imports_def ++ aead_G_def *)
(* ---------------------------------------------------------------------- *)

Lemma ap3_covers (cs: compspecs) :
  asm_covers (aead_imports3 cs ++ aead_G3) (aead_imports_def cs ++ aead_G_def).
Proof.
  unfold asm_covers, aead_imports_def, aead_G_def.
  repeat apply Forall_cons; try apply Forall_nil; cbv beta;
  lazymatch goal with
  | |- exists s', _ /\ funspec_sub s' (snd poly1305_update_spec) =>
      exists (snd poly1305_update_spec3); split; [reflexivity | exact ap3_sub_update]
  | |- exists s', _ /\ funspec_sub s' (snd chacha_crypt_generic_spec) =>
      exists (snd chacha_crypt_generic_spec3); split; [reflexivity | exact ap3_sub_generic]
  | |- exists s', _ /\ funspec_sub s' (snd chacha_crypt_spec) =>
      exists (snd chacha_crypt_spec3); split; [reflexivity | exact ap3_sub_crypt]
  | |- exists s', _ /\ funspec_sub s' (snd chacha20_crypt_spec) =>
      exists (snd chacha20_crypt_spec3); split; [reflexivity | exact ap3_sub_c20]
  | |- exists s', _ /\ funspec_sub s' (snd __chacha20poly1305_encrypt_spec) =>
      exists (snd __chacha20poly1305_encrypt_spec3); split; [reflexivity | exact ap3_sub_enc]
  | |- exists s', _ /\ funspec_sub s' (snd __chacha20poly1305_decrypt_spec) =>
      exists (snd __chacha20poly1305_decrypt_spec3); split; [reflexivity | exact ap3_sub_dec]
  | |- exists s', _ /\ funspec_sub s' (snd chacha20poly1305_encrypt_spec) =>
      exists (snd chacha20poly1305_encrypt_spec3); split; [reflexivity | exact ap3_sub_aenc]
  | |- exists s', _ /\ funspec_sub s' (snd chacha20poly1305_decrypt_spec) =>
      exists (snd chacha20poly1305_decrypt_spec3); split; [reflexivity | exact ap3_sub_adec]
  | |- exists s', _ /\ funspec_sub s' (snd xchacha20poly1305_encrypt_spec) =>
      exists (snd xchacha20poly1305_encrypt_spec3); split; [reflexivity | exact ap3_sub_xenc]
  | |- exists s', _ /\ funspec_sub s' (snd xchacha20poly1305_decrypt_spec) =>
      exists (snd xchacha20poly1305_decrypt_spec3); split; [reflexivity | exact ap3_sub_xdec]
  | |- exists s', _ /\ funspec_sub s' (snd ?x) =>
      exists (snd x); split; [reflexivity | apply funspec_sub_refl]
  end.
Qed.

Lemma ap3_V_self (V: varspecs) :
  list_norepet (map fst V) -> Forall (fun it => initial_world.find_id (fst it) V = Some (snd it)) V.
Proof.
  intros H. rewrite Forall_forall. intros [i t] HIn. apply initial_world.find_id_i; auto.
Qed.

Lemma ap3_lift (cs: compspecs) (V: varspecs) f ip :
  Forall (fun it => complete_type (@cenv_cs cs) (snd it) = true) (fn_vars f) ->
  list_norepet (map fst V ++ map fst (aead_imports3 cs ++ aead_G3)) ->
  @semax_body V (aead_imports_def cs ++ aead_G_def) cs f ip ->
  @semax_body V (aead_imports3 cs ++ aead_G3) cs f ip.
Proof.
  intros C N SB.
  apply (@asm_body_lift cs cs V V (aead_imports_def cs ++ aead_G_def) (aead_imports3 cs ++ aead_G3) f ip cspecs_sub_refl C N); auto.
  - apply ap3_V_self. apply list_norepet_append_inv in N. tauto.
  - apply ap3_covers.
Qed.

Ltac ap3_lnr :=
  rewrite map_app, aead_G3_ids; apply compute_list_norepet_e; vm_compute; reflexivity.

Lemma ap3_lnr_cb : list_norepet (map fst (Component.QPvarspecs ChachaBlock.qp) ++ map fst (aead_imports3 ChachaBlock.CS ++ aead_G3)).
Proof. ap3_lnr. Qed.
Lemma ap3_lnr_c : list_norepet (map fst (Component.QPvarspecs Chacha.qp) ++ map fst (aead_imports3 Chacha.CS ++ aead_G3)).
Proof. ap3_lnr. Qed.
Lemma ap3_lnr_cp : list_norepet (map fst (Component.QPvarspecs Chacha20poly1305.qp) ++ map fst (aead_imports3 Chacha20poly1305.CS ++ aead_G3)).
Proof. ap3_lnr. Qed.
Lemma ap3_lnr_p : list_norepet (map fst (Component.QPvarspecs Poly1305.qp) ++ map fst (aead_imports3 Poly1305.CS ++ aead_G3)).
Proof. ap3_lnr. Qed.

Ltac ap3_lift_tac lnr H :=
  apply ap3_lift; [cbv [fn_vars]; repeat constructor | exact lnr | exact H].

Lemma ap3_body_permute :
  @semax_body (Component.QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_permute chacha_permute_spec.
Proof. ap3_lift_tac ap3_lnr_cb (aead_permute_body.aead_permute_bodies). Qed.

Lemma ap3_body_block_generic :
  @semax_body (Component.QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_block_generic chacha_block_generic_spec.
Proof. ap3_lift_tac ap3_lnr_cb (proj1 aead_block_body.aead_block_bodies). Qed.

Lemma ap3_body_hblock_generic :
  @semax_body (Component.QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_hchacha_block_generic hchacha_block_generic_spec.
Proof. ap3_lift_tac ap3_lnr_cb (proj2 aead_block_body.aead_block_bodies). Qed.

Lemma ap3_body_hblock :
  @semax_body (Component.QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
    WgNoise.chacha.code.f_hchacha_block hchacha_block_spec.
Proof. ap3_lift_tac ap3_lnr_c (proj2 aead_chacha_body.aead_chacha_bodies). Qed.

Lemma ap3_body_core_init :
  @semax_body (Component.QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_core_init poly1305_core_init_spec.
Proof. ap3_lift_tac ap3_lnr_p (proj1 aead_poly_small_body.aead_poly_small_bodies). Qed.

Lemma ap3_body_block_init :
  @semax_body (Component.QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_block_init_generic poly1305_block_init_generic_spec.
Proof. ap3_lift_tac ap3_lnr_p (proj1 (proj2 aead_poly_small_body.aead_poly_small_bodies)). Qed.

Lemma ap3_body_blocks :
  @semax_body (Component.QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_blocks_generic poly1305_blocks_generic_spec.
Proof. ap3_lift_tac ap3_lnr_p (proj1 (proj2 (proj2 aead_poly_small_body.aead_poly_small_bodies))). Qed.

Lemma ap3_body_emit :
  @semax_body (Component.QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_emit_generic poly1305_emit_generic_spec.
Proof. ap3_lift_tac ap3_lnr_p (proj1 (proj2 (proj2 (proj2 aead_poly_small_body.aead_poly_small_bodies)))). Qed.

Lemma ap3_body_pinit :
  @semax_body (Component.QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_init poly1305_init_spec.
Proof. ap3_lift_tac ap3_lnr_p (proj2 (proj2 (proj2 (proj2 aead_poly_small_body.aead_poly_small_bodies)))). Qed.

Ltac ap3_in u H :=
  exists u; split; [simpl; tauto |]; eexists; split; [reflexivity | exact H].

Theorem aead_piece3 :
  aead_piece3_ok /\ asm_covers aead_G3 (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec).
Proof.
  split.
  2:{ unfold asm_covers, aead_iface3.
      repeat apply Forall_cons; try apply Forall_nil; cbv beta.
      - exists (snd chacha20poly1305_encrypt_spec3); split; [reflexivity | exact ap3_sub_aenc].
      - exists (snd chacha20poly1305_decrypt_spec3); split; [reflexivity | exact ap3_sub_adec].
      - exists (snd xchacha20poly1305_encrypt_spec3); split; [reflexivity | exact ap3_sub_xenc].
      - exists (snd xchacha20poly1305_decrypt_spec3); split; [reflexivity | exact ap3_sub_xdec]. }
  unfold aead_piece3_ok, piece_ok.
  split; [rewrite aead_G3_ids; apply compute_list_norepet_e; vm_compute; reflexivity |].
  destruct aead_small_body3.aead_small_bodies3 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  destruct aead_donna_emit_body3.aead_donna_emit_bodies3 as (D1 & D2).
  destruct aead_chacha_crypt3.aead_chacha_bodies3 as (C1 & C2 & C3).
  destruct aead_entry_body3.aead_entry_bodies3 as (E1 & E2 & E3 & E4 & E5).
  apply Forall_cons; [ap3_in u_shim S1 |].
  apply Forall_cons; [ap3_in u_chacha S2 |].
  apply Forall_cons; [ap3_in u_chacha C1 |].
  apply Forall_cons; [ap3_in u_chacha C2 |].
  apply Forall_cons; [ap3_in u_chacha ap3_body_hblock |].
  apply Forall_cons; [ap3_in u_chacha_block S3 |].
  apply Forall_cons; [ap3_in u_chacha_block S4 |].
  apply Forall_cons; [ap3_in u_chacha_block S5 |].
  apply Forall_cons; [ap3_in u_chacha_block ap3_body_permute |].
  apply Forall_cons; [ap3_in u_chacha_block ap3_body_block_generic |].
  apply Forall_cons; [ap3_in u_chacha_block ap3_body_hblock_generic |].
  apply Forall_cons; [ap3_in u_poly1305_donna32 D1 |].
  apply Forall_cons; [ap3_in u_poly1305_donna32 aead_donna_blocks_body3.aead_donna_blocks_bodies3 |].
  apply Forall_cons; [ap3_in u_poly1305_donna32 D2 |].
  apply Forall_cons; [ap3_in u_poly1305 ap3_body_core_init |].
  apply Forall_cons; [ap3_in u_poly1305 ap3_body_block_init |].
  apply Forall_cons; [ap3_in u_poly1305 ap3_body_blocks |].
  apply Forall_cons; [ap3_in u_poly1305 ap3_body_emit |].
  apply Forall_cons; [ap3_in u_poly1305 ap3_body_pinit |].
  apply Forall_cons; [ap3_in u_poly1305 aead_poly_update_body3.aead_poly_update_bodies3 |].
  apply Forall_cons; [ap3_in u_poly1305 aead_poly_final_body3.aead_poly_final_bodies3 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 S6 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 S7 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 S8 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 C3 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 S9 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 E1 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 aead_encrypt_body3.aead_encrypt_bodies3 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 aead_decrypt_body3.aead_decrypt_bodies3 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 E2 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 E3 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 E4 |].
  apply Forall_cons; [ap3_in u_chacha20poly1305 E5 |].
  apply Forall_nil.
Qed.
