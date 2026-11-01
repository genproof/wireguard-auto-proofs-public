(* Law ae_split_chacha20 (harness/ae_split_chacha20.c): the whole program is safe, i.e. its checks hold in every execution, given the
   small shared bodies of wl_kit.v (proved once for all ae_ laws, wl_kit_proof.v, and given in ae_laws_parts.v). *)
Require Import QuickProof.Contract.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require WgNoise.contracts.ae_split_chacha20.

(* The assembly (asm_assert.v, the x_ laws' assembly with gp_assert): the program is the harness, chacha.c,
   chacha-block-generic.c, wg_shim.c and libc.c, in the law's world W_ae_split_chacha20.  Every function main
   reaches has a body proved with a context of its callees only, so that it moves into this program:
   - memcpy, memset (libc_mem_piece.v); memzero_explicit, get_unaligned_le32, upto, any_bytes, bytes_eq (the
     kit, for any compspecs, here W);
   - __crypto_xor, crypto_xor_cpy, chacha_crypt_generic, chacha_crypt (chacha_stream_ctx.v), rol32,
     put_unaligned_le32, chacha_zeroize_state, chacha_block_generic (chacha_block_ctx.v), chacha_permute
     (chacha_permute_ctx.v), each in its unit's compspecs;
   - the harness's chacha_init_consts, chacha_init, chacha20_crypt (ae_split_chacha20_inline.v) and main
     (ae_split_chacha20_main.v), in W.
   The other functions of the program get vacuous specifications (asm_vac). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.assembly.asm_xcs3.
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_mem_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.chacha_block_ctx.
Require Import WgNoise.proof.aead.chacha_permute_ctx.
Require Import WgNoise.proof.aead.chacha_stream_ctx.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_world.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_spec.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_inline.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_main.
Require WgNoise.harness.ae_split_chacha20.code.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.shim.code WgNoise.libc.code.
Require WgNoise.chacha20poly1305.code WgNoise.harness.ae_roundtrip.code.

Local Notation find_id := initial_world.find_id.

Section Assembly.
Local Notation p := WgNoise.contracts.ae_split_chacha20.whole_prog.
Local Notation W := W_ae_split_chacha20.

(* the specifications of the functions main reaches, main excepted *)
Definition asc_Gr : funspecs :=
  [@memcpy_spec Libc.CS; @memset_spec Libc.CS; @memzero_explicit_spec W;
   __crypto_xor_spec; crypto_xor_cpy_spec; chacha_crypt_generic_spec3; chacha_crypt_spec3;
   rol32_spec; put_unaligned_le32_spec; chacha_zeroize_state_spec; chacha_permute_spec; chacha_block_generic_spec;
   @get_unaligned_le32_spec W; @chacha_init_consts_spec; chacha_init_spec; chacha20_crypt_spec3;
   upto_spec; @any_bytes_spec W; @bytes_eq_spec W].

Definition asc_ids : list ident := ltac:(let l := eval compute in (map fst asc_Gr) in exact l).

Local Notation Gw := (@asm_Gall_gp W p asc_post asc_Gr asc_ids).

Lemma asc_IDS : map fst asc_Gr = asc_ids.
Proof. reflexivity. Qed.

Lemma asc_check : asm_check_gp W p asc_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma asc_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_gp_norepet; [apply asc_IDS | apply asc_check]. Qed.

Lemma asc_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_gp_norepet'; [apply asc_IDS | apply asc_check]. Qed.

Lemma asc_cs_sub cs : In cs [Chacha.CS; ChachaBlock.CS; Shim.CS; Libc.CS] -> cspecs_sub cs W.
Proof.
  destruct world_ok_ae_split_chacha20 as (_ & _ & _ & HF). rewrite Forall_forall in HF.
  intros H. apply HF. right; auto.
Qed.

Lemma asc_find i s : In (i, s) Gw -> find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [exact H | apply asc_norepet']. Qed.

Lemma asc_find_Gr i s : In (i, s) asc_Gr -> find_id i Gw = Some s.
Proof. intros H. apply asc_find, asm_Gr_gp_incl, H. Qed.

(* a body proved in a unit (compspecs csu, varspecs Vu, context Gu), as a body of the whole program *)
Lemma asc_lift {csu: compspecs} (Vu: varspecs) (Gu: funspecs) (i: ident) (f: function) (s: funspec):
  Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  cspecs_sub csu W ->
  Forall (fun it => complete_type (@cenv_cs csu) (snd it) = true) (fn_vars f) ->
  Forall (fun it => find_id (fst it) (QPvarspecs p) = Some (snd it)) Vu ->
  asm_covers Gw Gu ->
  @semax_body Vu Gu csu f (i, s) ->
  exists f, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) /\
            @semax_body (QPvarspecs p) Gw W f (i, s).
Proof.
  intros Hget CS CO HV HG SB. exists f. split; [exact Hget |].
  exact (asm_body_lift Vu (QPvarspecs p) Gu Gw f (i, s) CS CO asc_norepet HV HG SB).
Qed.

(* a context whose entries are entries of asc_Gr or the environment's *)
Ltac asc_covers :=
  apply asm_covers_incl; [apply asc_norepet' |];
  intros x Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  first [ solve [apply asm_Gr_gp_incl; unfold asc_Gr; repeat (first [left; reflexivity | right])]
        | solve [apply asm_E_gp_incl; [unfold env_specs_gp, asm_env.env_specs; simpl;
                                       repeat (first [left; reflexivity | right]) | reflexivity]] ].

Ltac asc_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

#[local] Instance asc_cce_libc_W : change_composite_env Libc.CS W.
Proof. make_cs_preserve Libc.CS W. Defined.
#[local] Instance asc_cce_W_block : change_composite_env W ChachaBlock.CS.
Proof. make_cs_preserve W ChachaBlock.CS. Defined.

Lemma asc_bodies (KIT: wl_kit_ok) :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt asc_post) :: asc_Gr).
Proof.
  destruct KIT as (K_upto & _ & K_any_bytes & K_bytes_eq & K_memzero & K_le32).
  unfold asm_bodies. repeat apply Forall_cons; [.. | apply Forall_nil].
  - (* main *)
    apply (@asc_lift W asc_V asc_main_ctx _ WgNoise.harness.ae_split_chacha20.code.f_main);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | asc_varspecs | asc_covers |].
    exact body_main_asc.
  - (* memcpy *)
    apply (@asc_lift Libc.CS (QPvarspecs Libc.qp) (libc_mem_imports Libc.CS ++ libc_mem_G) _ WgNoise.libc.code.f_memcpy);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | asc_covers | exact body_memcpy_mem].
  - (* memset *)
    apply (@asc_lift Libc.CS (QPvarspecs Libc.qp) (libc_mem_imports Libc.CS ++ libc_mem_G) _ WgNoise.libc.code.f_memset);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | asc_covers | exact body_memset_mem].
  - (* memzero_explicit: the kit at W; its memset is libc's *)
    apply (@asc_lift W nil [@memset_spec W] _ WgNoise.chacha20poly1305.code.f_memzero_explicit);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | constructor | | exact (K_memzero W)].
    constructor; [| constructor]. exists (snd (@memset_spec Libc.CS)). split.
    + apply asc_find_Gr. unfold asc_Gr. right; left; reflexivity.
    + apply (@xcs_memset_sub Libc.CS W asc_cce_libc_W).
  - (* __crypto_xor *)
    apply (@asc_lift Shim.CS (QPvarspecs Shim.qp) nil _ WgNoise.shim.code.f___crypto_xor);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | constructor | exact body___crypto_xor_ctx].
  - apply (@asc_lift Chacha.CS (QPvarspecs Chacha.qp) [__crypto_xor_spec] _ WgNoise.chacha.code.f_crypto_xor_cpy);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | asc_covers | exact body_crypto_xor_cpy_ctx].
  - apply (@asc_lift Chacha.CS (QPvarspecs Chacha.qp) [chacha_block_generic_spec; crypto_xor_cpy_spec] _
             WgNoise.chacha.code.f_chacha_crypt_generic);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | asc_covers | exact body_chacha_crypt_generic_ctx].
  - apply (@asc_lift Chacha.CS (QPvarspecs Chacha.qp) [chacha_crypt_generic_spec3] _ WgNoise.chacha.code.f_chacha_crypt);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | asc_covers | exact body_chacha_crypt_ctx].
  - apply (@asc_lift ChachaBlock.CS (QPvarspecs ChachaBlock.qp) nil _ WgNoise.chacha_block.code.f_rol32);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | constructor | exact body_rol32_ctx].
  - apply (@asc_lift ChachaBlock.CS (QPvarspecs ChachaBlock.qp) nil _ WgNoise.chacha_block.code.f_put_unaligned_le32);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | constructor | exact body_put_unaligned_le32_ctx].
  - (* chacha_zeroize_state: memzero_explicit at W covers it at ChachaBlock.CS *)
    apply (@asc_lift ChachaBlock.CS (QPvarspecs ChachaBlock.qp) [@memzero_explicit_spec ChachaBlock.CS] _
             WgNoise.chacha_block.code.f_chacha_zeroize_state);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | | exact body_chacha_zeroize_state_ctx].
    constructor; [| constructor]. exists (snd (@memzero_explicit_spec W)). split.
    + apply asc_find_Gr. unfold asc_Gr. right; right; left; reflexivity.
    + apply (@xa3_memzero_explicit_sub W ChachaBlock.CS asc_cce_W_block).
  - apply (@asc_lift ChachaBlock.CS (QPvarspecs ChachaBlock.qp) permc_Gprog _ WgNoise.chacha_block.code.f_chacha_permute);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | unfold permc_Gprog; asc_covers | exact body_chacha_permute_ctx].
  - apply (@asc_lift ChachaBlock.CS (QPvarspecs ChachaBlock.qp)
             [chacha_permute_spec; put_unaligned_le32_spec; chacha_zeroize_state_spec] _
             WgNoise.chacha_block.code.f_chacha_block_generic);
      [vm_compute; reflexivity | apply asc_cs_sub; simpl; tauto | repeat constructor | asc_varspecs
      | asc_covers | exact body_chacha_block_generic_ctx].
  - apply (@asc_lift W nil nil _ WgNoise.chacha20poly1305.code.f_get_unaligned_le32);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | constructor | constructor
      | exact (K_le32 W)].
  - apply (@asc_lift W asc_V nil _ WgNoise.harness.ae_split_chacha20.code.f_chacha_init_consts);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | asc_varspecs | constructor
      | exact body_chacha_init_consts_asc].
  - apply (@asc_lift W asc_V [chacha_init_consts_spec; @get_unaligned_le32_spec W] _
             WgNoise.harness.ae_split_chacha20.code.f_chacha_init);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | asc_varspecs | asc_covers
      | exact body_chacha_init_asc].
  - apply (@asc_lift W asc_V [chacha_crypt_spec3] _ WgNoise.harness.ae_split_chacha20.code.f_chacha20_crypt);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | asc_varspecs | asc_covers
      | exact body_chacha20_crypt_asc].
  - apply (@asc_lift W nil [nondet_size_spec] _ WgNoise.harness.ae_roundtrip.code.f_upto);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | constructor | asc_covers
      | exact (K_upto W)].
  - apply (@asc_lift W nil [(_quickproof_malloc, @malloc_spec' W); @asm_env.nondet_bytes_spec W] _
             WgNoise.harness.ae_roundtrip.code.f_any_bytes);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | constructor | asc_covers
      | exact (K_any_bytes W)].
  - apply (@asc_lift W nil nil _ WgNoise.harness.ae_roundtrip.code.f_bytes_eq);
      [vm_compute; reflexivity | apply cspecs_sub_refl | repeat constructor | constructor | constructor
      | exact (K_bytes_eq W)].
Qed.

Lemma asc_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma asc_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma asc_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) asc_Gr.
Proof. repeat constructor. Qed.

End Assembly.

Lemma ae_split_chacha20_safe_kit : wl_kit_ok -> harness_safe WgNoise.contracts.ae_split_chacha20.whole_prog.
Proof.
  intros KIT.
  exact (asm_harness_safe_gp _ world_OK_whole_ae_split_chacha20 W_ae_split_chacha20 W_ae_split_chacha20_eq
           asc_cbc asc_ext_ok asc_post asc_Gr asc_ids asc_IDS asc_check asc_cc (asc_bodies KIT)).
Qed.
