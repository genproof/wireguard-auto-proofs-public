(* Law ae_fail_untouched (harness/ae_fail_untouched.c): the whole program is safe, given the small shared bodies
   of wl_kit.v and copy_of's (wl_copy_of.v), both discharged in ae_fail_untouched_safe.v. *)
Require Import QuickProof.Contract.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require Import WgNoise.proof.harness.wg_laws.wl_copy_of.
Require WgNoise.contracts.ae_fail_untouched.

(* The assembly (asm_assert.asm_harness_safe_gp, the x_ laws' assembly with gp_assert), as for ae_xroundtrip,
   whose program has the same units, from:
   - the libc piece's bodies (libc_piece.v: memcpy, memset, memcmp, calloc, the shim's __crypto_memneq) and the
     inline crypto_memneq on chacha20poly1305.c's copy (libc_memneq_novars.v): this program has no curve25519.c;
   - the AEAD piece (aead_piece3b.v: every function of the AEAD units, aead_G3b);
   - the kit (wl_kit_ok, wl_copy_of_ok): memzero_explicit, get_unaligned_le32 and the wg_laws.h helpers upto,
     any_u64, any_bytes, copy_of, bytes_eq, each proved for any compspecs, here the world's;
   - main (aefu_main.v). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.libc.libc_memneq_novars.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3b.
Require WgNoise.proof.aead.aead_piece3b.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.wg_laws.wl_copy_of.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_world.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_spec.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_main.
Require WgNoise.harness.ae_fail_untouched.code.
Require WgNoise.harness.ae_roundtrip.code.
Require WgNoise.chacha20poly1305.code.

Local Notation p := WgNoise.contracts.ae_fail_untouched.whole_prog.
Local Notation W := W_ae_fail_untouched.

(* the compspecs conversions of the byte-array specifications *)
Ltac afs_cce a b := make_cs_preserve a b.
#[local] Instance afs_cce_lw : change_composite_env Libc.CS W. Proof. afs_cce Libc.CS W. Defined.
#[local] Instance afs_cce_l1 : change_composite_env Libc.CS Chacha.CS. Proof. afs_cce Libc.CS Chacha.CS. Defined.
#[local] Instance afs_cce_l2 : change_composite_env Libc.CS ChachaBlock.CS. Proof. afs_cce Libc.CS ChachaBlock.CS. Defined.
#[local] Instance afs_cce_l3 : change_composite_env Libc.CS Poly1305.CS. Proof. afs_cce Libc.CS Poly1305.CS. Defined.
#[local] Instance afs_cce_l4 : change_composite_env Libc.CS Poly1305Donna32.CS. Proof. afs_cce Libc.CS Poly1305Donna32.CS. Defined.
#[local] Instance afs_cce_l5 : change_composite_env Libc.CS Chacha20poly1305.CS. Proof. afs_cce Libc.CS Chacha20poly1305.CS. Defined.
#[local] Instance afs_cce_l6 : change_composite_env Libc.CS Shim.CS. Proof. afs_cce Libc.CS Shim.CS. Defined.
#[local] Instance afs_cce_w1 : change_composite_env W Chacha.CS. Proof. afs_cce W Chacha.CS. Defined.
#[local] Instance afs_cce_w2 : change_composite_env W ChachaBlock.CS. Proof. afs_cce W ChachaBlock.CS. Defined.
#[local] Instance afs_cce_w3 : change_composite_env W Poly1305.CS. Proof. afs_cce W Poly1305.CS. Defined.
#[local] Instance afs_cce_w4 : change_composite_env W Poly1305Donna32.CS. Proof. afs_cce W Poly1305Donna32.CS. Defined.
#[local] Instance afs_cce_w5 : change_composite_env W Chacha20poly1305.CS. Proof. afs_cce W Chacha20poly1305.CS. Defined.
#[local] Instance afs_cce_w6 : change_composite_env W Shim.CS. Proof. afs_cce W Shim.CS. Defined.
#[local] Instance afs_cce_c1 : change_composite_env Curve25519.CS Chacha.CS. Proof. afs_cce Curve25519.CS Chacha.CS. Defined.
#[local] Instance afs_cce_c2 : change_composite_env Curve25519.CS ChachaBlock.CS. Proof. afs_cce Curve25519.CS ChachaBlock.CS. Defined.
#[local] Instance afs_cce_c3 : change_composite_env Curve25519.CS Poly1305.CS. Proof. afs_cce Curve25519.CS Poly1305.CS. Defined.
#[local] Instance afs_cce_c4 : change_composite_env Curve25519.CS Poly1305Donna32.CS. Proof. afs_cce Curve25519.CS Poly1305Donna32.CS. Defined.
#[local] Instance afs_cce_c5 : change_composite_env Curve25519.CS Chacha20poly1305.CS. Proof. afs_cce Curve25519.CS Chacha20poly1305.CS. Defined.
#[local] Instance afs_cce_c6 : change_composite_env Curve25519.CS Shim.CS. Proof. afs_cce Curve25519.CS Shim.CS. Defined.

(* ---------- the libc piece, with chacha20poly1305.c's crypto_memneq ---------- *)

(* chacha20poly1305.c without its varspecs: the unit of body_crypto_memneq_c20p *)
Definition u_c20p_novars : unit_ctx :=
  mk_unit Chacha20poly1305.CS nil WgNoise.chacha20poly1305.code.prog.

Lemma afs_libc_piece :
  piece_ok [u_libc; u_shim; u_c20p_novars] (libc_imports W) (libc_G W).
Proof.
  split.
  - apply compute_list_norepet_e. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memcpy. split; [reflexivity | apply body_memcpy].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memset. split; [reflexivity | apply body_memset].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memcmp. split; [reflexivity | apply body_memcmp].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_calloc. split; [reflexivity | apply body_calloc].
    + exists u_shim. split; [simpl; auto |].
      exists WgNoise.shim.code.f___crypto_memneq. split; [reflexivity | apply body___crypto_memneq].
    + exists u_c20p_novars. split; [simpl; auto |].
      exists WgNoise.chacha20poly1305.code.f_crypto_memneq. split; [reflexivity | apply body_crypto_memneq_c20p].
Qed.

(* ---------- the specifications of the program ---------- *)

(* the kit's byte inlines, at the world *)
Definition afs_Gk : funspecs := [@memzero_explicit_spec W; @get_unaligned_le32_spec W].

(* the harness's own functions, main excepted *)
Definition afs_Gh : funspecs :=
  [@upto_spec; @any_u64_spec; @any_bytes_spec W; @copy_of_spec W; @bytes_eq_spec W].

Definition afs_Gr : funspecs := libc_G W ++ aead_G3b ++ afs_Gk ++ afs_Gh.

Definition afs_ids : list ident :=
  ltac:(let l := eval compute in (map fst afs_Gr) in exact l).

Lemma afs_IDS : map fst afs_Gr = afs_ids.
Proof. reflexivity. Qed.

Lemma afs_check : asm_check_gp W p afs_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma afs_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma afs_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma afs_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) afs_Gr.
Proof. repeat constructor. Qed.

Local Notation Gw := (@asm_Gall_gp W p aefu_post afs_Gr afs_ids).

Lemma afs_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_gp_norepet; [apply afs_IDS | apply afs_check]. Qed.

Lemma afs_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_gp_norepet'; [apply afs_IDS | apply afs_check]. Qed.

Lemma afs_find_Gr i s : In (i, s) afs_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply afs_norepet']. apply asm_Gr_gp_incl; auto. Qed.

Lemma afs_find_E i s : In (i, s) (@env_specs_gp W) -> asm_present_ext p i = true ->
  initial_world.find_id i Gw = Some s.
Proof. intros H1 H2. apply initial_world.find_id_i; [| apply afs_norepet']. apply asm_E_gp_incl; auto. Qed.

Ltac afs_in := repeat (first [left; reflexivity | right]).

Lemma afs_cs_sub cs : In cs afw_unit_cs -> cspecs_sub cs W.
Proof. pose proof world_ok_ae_fail_untouched as HF. rewrite Forall_forall in HF. auto. Qed.

Ltac afs_in_cs := unfold afw_unit_cs; simpl; afs_in.

Ltac afs_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac afs_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the malloc import of the libc piece *)
Lemma afs_covers_malloc : asm_covers Gw [(_quickproof_malloc, @malloc_spec' W)].
Proof.
  constructor; [| constructor]. exists (@malloc_spec' W). split; [| apply funspec_sub_refl].
  apply afs_find_E; [left; reflexivity | reflexivity].
Qed.

(* ---------- libc ---------- *)
Lemma afs_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_c20p_novars] (libc_imports W) (libc_G W) afs_libc_piece).
  - apply afs_norepet.
  - intros x Hx. apply asm_Gr_gp_incl. unfold afs_Gr. apply in_app; left; auto.
  - constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply afs_cs_sub; afs_in_cs |]; split; [afs_varspecs |]; split; [apply afs_covers_malloc | afs_funs].
Qed.

(* ---------- AEAD ---------- *)
Lemma afs_covers_aead_imports cs (C1: change_composite_env Libc.CS cs) (C2: change_composite_env W cs)
    (C3: change_composite_env Curve25519.CS cs) :
  asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply afs_find_Gr. unfold afs_Gr. afs_in.
    + apply (@xa3_memcpy_sub Libc.CS cs C1).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply afs_find_Gr. unfold afs_Gr. afs_in.
    + apply (@xa3_memset_sub Libc.CS cs C1).
  - exists (snd (@memzero_explicit_spec W)). split.
    + apply afs_find_Gr. unfold afs_Gr. simpl. afs_in.
    + apply (@xa3_memzero_explicit_sub W cs C2).
  - exists (snd (@get_unaligned_le32_spec W)). split.
    + apply afs_find_Gr. unfold afs_Gr. simpl. afs_in.
    + apply (@xa3_get_unaligned_le32_sub W cs C2).
  - exists (snd (@crypto_memneq_spec Curve25519.CS)). split.
    + apply afs_find_Gr. unfold afs_Gr. simpl. afs_in.
    + apply (@xa3_crypto_memneq_sub Curve25519.CS cs C3).
Qed.

Lemma afs_bodies_aead : asm_bodies W p Gw aead_G3b.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3b (proj1 aead_piece3b.aead_piece3b)).
  - apply afs_norepet.
  - intros x Hx. apply asm_Gr_gp_incl. unfold afs_Gr. apply in_app; right; apply in_app; left; auto.
  - unfold aead_units3.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    all: split; [apply afs_cs_sub; afs_in_cs |]; split; [afs_varspecs |].
    all: split; [apply afs_covers_aead_imports; typeclasses eauto | afs_funs].
Qed.

(* ---------- the kit ---------- *)

(* one body proved at the world with the context Gu, as an entry of the program *)
Lemma afs_body_kit i f s (Gu: funspecs) :
  Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  Forall (fun it => complete_type (@cenv_cs W) (snd it) = true) (fn_vars f) ->
  asm_covers Gw Gu ->
  @semax_body nil Gu W f (i, s) ->
  exists f, Maps.PTree.get (fst (i, s)) (QP.prog_defs p) = Some (Gfun (Internal f)) /\
            @semax_body (QPvarspecs p) Gw W f (i, s).
Proof.
  intros Hd Hc Hg SB. exists f; split; [exact Hd |].
  apply (asm_body_lift nil (QPvarspecs p) Gu Gw f (i, s) cspecs_sub_refl Hc afs_norepet
           (Forall_nil _) Hg SB).
Qed.

Lemma afs_covers_memset : asm_covers Gw [@memset_spec W].
Proof.
  constructor; [| constructor]. exists (snd (@memset_spec Libc.CS)). split.
  - apply afs_find_Gr. unfold afs_Gr. afs_in.
  - apply (@xa3_memset_sub Libc.CS W afs_cce_lw).
Qed.

Lemma afs_defs :
  Maps.PTree.get WgNoise.chacha20poly1305.code._memzero_explicit (QP.prog_defs p) =
    Some (Gfun (Internal WgNoise.chacha20poly1305.code.f_memzero_explicit)) /\
  Maps.PTree.get WgNoise.chacha20poly1305.code._get_unaligned_le32 (QP.prog_defs p) =
    Some (Gfun (Internal WgNoise.chacha20poly1305.code.f_get_unaligned_le32)) /\
  Maps.PTree.get _upto (QP.prog_defs p) = Some (Gfun (Internal WgNoise.harness.ae_roundtrip.code.f_upto)) /\
  Maps.PTree.get _any_u64 (QP.prog_defs p) = Some (Gfun (Internal WgNoise.harness.ae_roundtrip.code.f_any_u64)) /\
  Maps.PTree.get _any_bytes (QP.prog_defs p) = Some (Gfun (Internal WgNoise.harness.ae_roundtrip.code.f_any_bytes)) /\
  Maps.PTree.get WgNoise.harness.ae_fail_untouched.code._copy_of (QP.prog_defs p) =
    Some (Gfun (Internal WgNoise.harness.ae_fail_untouched.code.f_copy_of)) /\
  Maps.PTree.get _bytes_eq (QP.prog_defs p) = Some (Gfun (Internal WgNoise.harness.ae_roundtrip.code.f_bytes_eq)).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* an external of the environment, present in the program, as an entry of the program *)
Lemma afs_covers_env (s: ident * funspec) :
  In s (@env_specs_gp W) -> asm_present_ext p (fst s) = true -> asm_covers Gw [s].
Proof.
  intros H1 H2. constructor; [| constructor]. exists (snd s). split; [| apply funspec_sub_refl].
  destruct s; apply afs_find_E; auto.
Qed.

Lemma afs_bodies_kit (K: wl_kit_ok) (C: wl_copy_of_ok) : asm_bodies W p Gw (afs_Gk ++ afs_Gh).
Proof.
  destruct K as (Kup & Ku64 & Kany & Keq & Kmz & Kgu).
  destruct afs_defs as (Dmz & Dgu & Dup & Du64 & Dany & Dcp & Deq).
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (afs_body_kit _ _ _ [@memset_spec W] Dmz); [repeat constructor | apply afs_covers_memset | apply Kmz].
  - apply (afs_body_kit _ _ _ nil Dgu); [repeat constructor | constructor | apply Kgu].
  - apply (afs_body_kit _ _ _ [nondet_size_spec] Dup); [repeat constructor | | apply Kup].
    apply afs_covers_env; [simpl; afs_in | reflexivity].
  - apply (afs_body_kit _ _ _ [nondet_u32_spec] Du64); [repeat constructor | | apply Ku64].
    apply afs_covers_env; [simpl; afs_in | reflexivity].
  - apply (afs_body_kit _ _ _ [(_quickproof_malloc, @malloc_spec' W); @asm_env.nondet_bytes_spec W] Dany); [repeat constructor | | apply Kany].
    constructor; [| constructor; [| constructor]].
    + exists (@malloc_spec' W). split; [| apply funspec_sub_refl].
      apply afs_find_E; [left; reflexivity | reflexivity].
    + exists (snd (@asm_env.nondet_bytes_spec W)). split; [| apply funspec_sub_refl].
      apply afs_find_E; [simpl; afs_in | reflexivity].
  - apply (afs_body_kit _ _ _ [(_quickproof_malloc, @malloc_spec' W)] Dcp); [repeat constructor | | apply C].
    constructor; [| constructor].
    exists (@malloc_spec' W). split; [| apply funspec_sub_refl].
    apply afs_find_E; [left; reflexivity | reflexivity].
  - apply (afs_body_kit _ _ _ nil Deq); [repeat constructor | constructor | apply Keq].
Qed.

(* ---------- main ---------- *)
Lemma afs_body_main :
  asm_bodies W p Gw [(QP.prog_main p, QPmain_spec_ext' p tt aefu_post)].
Proof.
  constructor; [| constructor].
  exists WgNoise.harness.ae_fail_untouched.code.f_main. split; [vm_compute; reflexivity |].
  apply (asm_body_lift aefu_V (QPvarspecs p) aefu_Gmain Gw _ aefu_main_spec cspecs_sub_refl);
    [repeat constructor | apply afs_norepet | afs_varspecs | | exact aefu_main_body].
  unfold aefu_Gmain, aefu_env. repeat apply Forall_cons; try apply Forall_nil.
  - exists (@malloc_spec' W). split; [| apply funspec_sub_refl].
    apply afs_find_E; [left; reflexivity | reflexivity].
  - exists (snd (@asm_env.nondet_bytes_spec W)). split; [| apply funspec_sub_refl].
    apply afs_find_E; [simpl; afs_in | reflexivity].
  - exists (snd nondet_u8_spec). split; [| apply funspec_sub_refl].
    apply afs_find_E; [simpl; afs_in | reflexivity].
  - exists (snd gp_assert_spec). split; [| apply funspec_sub_refl].
    apply afs_find_E; [simpl; afs_in | reflexivity].
  - exists (snd chacha20poly1305_encrypt_spec3). split; [| apply aefu_encrypt_sub].
    apply afs_find_Gr. unfold afs_Gr, aead_G3b. simpl. afs_in.
  - exists (snd chacha20poly1305_decrypt_spec3b). split; [| apply aefu_decrypt_sub].
    apply afs_find_Gr. unfold afs_Gr, aead_G3b. simpl. afs_in.
  - exists (snd xchacha20poly1305_encrypt_spec3). split; [| apply aefu_xencrypt_sub].
    apply afs_find_Gr. unfold afs_Gr, aead_G3b. simpl. afs_in.
  - exists (snd xchacha20poly1305_decrypt_spec3b). split; [| apply aefu_xdecrypt_sub].
    apply afs_find_Gr. unfold afs_Gr, aead_G3b. simpl. afs_in.
  - exists (snd (@upto_spec)). split; [| apply funspec_sub_refl].
    apply afs_find_Gr. unfold afs_Gr, afs_Gh. simpl. afs_in.
  - exists (snd (@any_u64_spec)). split; [| apply funspec_sub_refl].
    apply afs_find_Gr. unfold afs_Gr, afs_Gh. simpl. afs_in.
  - exists (snd (@any_bytes_spec W)). split; [| apply funspec_sub_refl].
    apply afs_find_Gr. unfold afs_Gr, afs_Gh. simpl. afs_in.
  - exists (snd (@copy_of_spec W)). split; [| apply funspec_sub_refl].
    apply afs_find_Gr. unfold afs_Gr, afs_Gh. simpl. afs_in.
  - exists (snd (@bytes_eq_spec W)). split; [| apply funspec_sub_refl].
    apply afs_find_Gr. unfold afs_Gr, afs_Gh. simpl. afs_in.
Qed.

Lemma afs_bodies (K: wl_kit_ok) (C: wl_copy_of_ok) :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt aefu_post) :: afs_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _
           (asm_bodies_incl _ _ _ _ _ _ afs_bodies_libc afs_bodies_aead (incl_refl _))
           (asm_bodies_incl _ _ _ _ _ _ (afs_bodies_kit K C) afs_body_main (incl_refl _))).
  intros x Hx. rewrite !in_app_iff. destruct Hx as [<-|Hx]; [right; right; left; reflexivity |].
  unfold afs_Gr in Hx. rewrite !in_app_iff in Hx. tauto.
Qed.

Lemma ae_fail_untouched_safe_kit :
  wl_kit_ok -> wl_copy_of_ok -> harness_safe WgNoise.contracts.ae_fail_untouched.whole_prog.
Proof.
  intros K C.
  exact (asm_harness_safe_gp p world_OK_whole_ae_fail_untouched W W_ae_fail_untouched_eq afs_cbc afs_ext_ok
           aefu_post afs_Gr afs_ids afs_IDS afs_check afs_cc (afs_bodies K C)).
Qed.
