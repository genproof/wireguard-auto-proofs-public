(* Law ae_roundtrip (harness/ae_roundtrip.c): the whole program is safe, i.e. its checks hold in every execution, given the
   small shared bodies of wl_kit.v (proved once for all ae_ laws, wl_kit_proof.v, and given in ae_laws_parts.v). *)
Require Import QuickProof.Contract.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require WgNoise.contracts.ae_roundtrip.

(* The assembly (asm_assert.asm_harness_safe_gp) in the world W_ae_roundtrip, from:
   - the libc bodies of libc_piece.v (memcpy, memset, memcmp, calloc, the shim's __crypto_memneq) and the inline
     crypto_memneq on chacha20poly1305.c's copy (libc_memneq_novars.v: this program has no curve25519.c, whose
     copy libc_piece.v proves), with the specifications libc_G;
   - the AEAD piece (aead_piece3.v: every function of chacha.c, chacha-block-generic.c, poly1305.c,
     poly1305-donna32.c, chacha20poly1305.c and the shim's __crypto_xor, with aead_G3);
   - the byte inlines memzero_explicit and get_unaligned_le32 and the wg_laws.h helpers upto, any_u64,
     any_bytes, bytes_eq (wl_kit_ok, any compspecs, callee-only contexts);
   - main (ae_roundtrip_main.v).
   Every other function of the program is unreachable from main and gets a vacuous specification. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32
        WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Shim WgNoise.units.Libc.
Require WgNoise.chacha20poly1305.code WgNoise.harness.ae_roundtrip.code.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.libc.libc_memneq_novars.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3.
Require WgNoise.proof.aead.aead_piece3.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_world.
Require Import WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_spec.
Require Import WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_main.

Local Notation p := WgNoise.contracts.ae_roundtrip.whole_prog.
Local Notation W := W_ae_roundtrip.
Local Notation C20P := Chacha20poly1305.CS.

(* the copies of chacha20poly1305.c's inlines that this program contains, under C20P *)
Definition ar_inlines : funspecs := [@memzero_explicit_spec C20P; @get_unaligned_le32_spec C20P].

(* the harness's helpers (wg_laws.h) *)
Definition ar_Gh : funspecs := [upto_spec; any_u64_spec; @any_bytes_spec W; @bytes_eq_spec W].

(* the real specifications, main excepted *)
Definition ar_Gr : funspecs := libc_G W ++ aead_G3 ++ ar_inlines ++ ar_Gh.

Definition ar_ids : list ident := ltac:(let l := eval compute in (map fst ar_Gr) in exact l).

Local Notation Gw := (@asm_Gall_gp W p ar_post ar_Gr ar_ids).

Lemma ar_IDS : map fst ar_Gr = ar_ids.
Proof. reflexivity. Qed.

Lemma ar_check : asm_check_gp W p ar_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma ar_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_gp_norepet; [apply ar_IDS | apply ar_check]. Qed.

Lemma ar_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_gp_norepet'; [apply ar_IDS | apply ar_check]. Qed.

Lemma ar_find_Gr i s : In (i, s) ar_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply ar_norepet']. apply asm_Gr_gp_incl; auto. Qed.

Lemma ar_in_libc ix : In ix (libc_G W) -> In ix ar_Gr.
Proof. intros H. unfold ar_Gr. apply in_app; left; auto. Qed.
Lemma ar_in_aead ix : In ix aead_G3 -> In ix ar_Gr.
Proof. intros H. unfold ar_Gr. apply in_app; right; apply in_app; left; auto. Qed.
Lemma ar_in_inl ix : In ix ar_inlines -> In ix ar_Gr.
Proof. intros H. unfold ar_Gr. apply in_app; right; apply in_app; right; apply in_app; left; auto. Qed.
Lemma ar_in_h ix : In ix ar_Gh -> In ix ar_Gr.
Proof. intros H. unfold ar_Gr. apply in_app; right; apply in_app; right; apply in_app; right; auto. Qed.

(* an external of the environment that the program calls *)
Lemma ar_env_in i s : In (i, s) (@env_specs_gp W) -> asm_present_ext p i = true -> In (i, s) Gw.
Proof. apply asm_E_gp_incl. Qed.

Ltac ar_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac ar_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac ar_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* ---------- libc ---------- *)

(* chacha20poly1305.c without varspecs: the unit of its crypto_memneq copy *)
Definition u_c20p_novars : unit_ctx := mk_unit C20P nil WgNoise.chacha20poly1305.code.prog.

Lemma ar_libc_piece : piece_ok [u_libc; u_shim; u_c20p_novars] (libc_imports W) (libc_G W).
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

Lemma ar_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_c20p_novars] (libc_imports W) (libc_G W) ar_libc_piece).
  - apply ar_norepet.
  - intros x Hx. apply asm_Gr_gp_incl, ar_in_libc; auto.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply ar_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply ar_env_in; [left; reflexivity | reflexivity]. }
    constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply cs_sub_ae_roundtrip; ar_in_cs |]; split; [ar_varspecs |]; split; [apply CI | ar_funs].
Qed.

(* ---------- AEAD ---------- *)
Ltac ar_cce a b := make_cs_preserve a b.
#[local] Instance ar_cce_l1 : change_composite_env Libc.CS Chacha.CS. Proof. ar_cce Libc.CS Chacha.CS. Defined.
#[local] Instance ar_cce_l2 : change_composite_env Libc.CS ChachaBlock.CS. Proof. ar_cce Libc.CS ChachaBlock.CS. Defined.
#[local] Instance ar_cce_l3 : change_composite_env Libc.CS Poly1305.CS. Proof. ar_cce Libc.CS Poly1305.CS. Defined.
#[local] Instance ar_cce_l4 : change_composite_env Libc.CS Poly1305Donna32.CS. Proof. ar_cce Libc.CS Poly1305Donna32.CS. Defined.
#[local] Instance ar_cce_l5 : change_composite_env Libc.CS Chacha20poly1305.CS. Proof. ar_cce Libc.CS Chacha20poly1305.CS. Defined.
#[local] Instance ar_cce_l6 : change_composite_env Libc.CS Shim.CS. Proof. ar_cce Libc.CS Shim.CS. Defined.
#[local] Instance ar_cce_a1 : change_composite_env C20P Chacha.CS. Proof. ar_cce C20P Chacha.CS. Defined.
#[local] Instance ar_cce_a2 : change_composite_env C20P ChachaBlock.CS. Proof. ar_cce C20P ChachaBlock.CS. Defined.
#[local] Instance ar_cce_a3 : change_composite_env C20P Poly1305.CS. Proof. ar_cce C20P Poly1305.CS. Defined.
#[local] Instance ar_cce_a4 : change_composite_env C20P Poly1305Donna32.CS. Proof. ar_cce C20P Poly1305Donna32.CS. Defined.
#[local] Instance ar_cce_a5 : change_composite_env C20P Chacha20poly1305.CS. Proof. ar_cce C20P Chacha20poly1305.CS. Defined.
#[local] Instance ar_cce_a6 : change_composite_env C20P Shim.CS. Proof. ar_cce C20P Shim.CS. Defined.
#[local] Instance ar_cce_c1 : change_composite_env Curve25519.CS Chacha.CS. Proof. ar_cce Curve25519.CS Chacha.CS. Defined.
#[local] Instance ar_cce_c2 : change_composite_env Curve25519.CS ChachaBlock.CS. Proof. ar_cce Curve25519.CS ChachaBlock.CS. Defined.
#[local] Instance ar_cce_c3 : change_composite_env Curve25519.CS Poly1305.CS. Proof. ar_cce Curve25519.CS Poly1305.CS. Defined.
#[local] Instance ar_cce_c4 : change_composite_env Curve25519.CS Poly1305Donna32.CS. Proof. ar_cce Curve25519.CS Poly1305Donna32.CS. Defined.
#[local] Instance ar_cce_c5 : change_composite_env Curve25519.CS Chacha20poly1305.CS. Proof. ar_cce Curve25519.CS Chacha20poly1305.CS. Defined.
#[local] Instance ar_cce_c6 : change_composite_env Curve25519.CS Shim.CS. Proof. ar_cce Curve25519.CS Shim.CS. Defined.

Lemma ar_covers_aead_imports cs (C1: change_composite_env Libc.CS cs) (C2: change_composite_env C20P cs)
    (C3: change_composite_env Curve25519.CS cs) :
  asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply ar_find_Gr, ar_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs C1).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply ar_find_Gr, ar_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs C1).
  - exists (snd (@memzero_explicit_spec C20P)). split.
    + apply ar_find_Gr, ar_in_inl. left; reflexivity.
    + apply (@xa3_memzero_explicit_sub C20P cs C2).
  - exists (snd (@get_unaligned_le32_spec C20P)). split.
    + apply ar_find_Gr, ar_in_inl. right; left; reflexivity.
    + apply (@xa3_get_unaligned_le32_sub C20P cs C2).
  - exists (snd (@crypto_memneq_spec Curve25519.CS)). split.
    + apply ar_find_Gr, ar_in_libc. unfold libc_G; simpl; repeat (first [left; reflexivity | right]).
    + apply (@xa3_crypto_memneq_sub Curve25519.CS cs C3).
Qed.

Lemma ar_bodies_aead : asm_bodies W p Gw aead_G3.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3 (proj1 aead_piece3.aead_piece3)).
  - apply ar_norepet.
  - intros x Hx. apply asm_Gr_gp_incl, ar_in_aead; auto.
  - unfold aead_units3.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    all: split; [apply cs_sub_ae_roundtrip; ar_in_cs |]; split; [ar_varspecs |].
    all: split; [apply ar_covers_aead_imports; typeclasses eauto | ar_funs].
Qed.

(* ---------- the kit: chacha20poly1305.c's byte inlines and the harness's helpers ---------- *)
Section Kit.
Variable K: wl_kit_ok.

Lemma ar_lift_one {csu: compspecs} (Gu: funspecs) f ip :
  cspecs_sub csu W ->
  Forall (fun it => complete_type (@cenv_cs csu) (snd it) = true) (fn_vars f) ->
  Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  asm_covers Gw Gu ->
  @semax_body nil Gu csu f ip ->
  exists f', Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f')) /\
             @semax_body (QPvarspecs p) Gw W f' ip.
Proof.
  intros CS CO D CG SB. exists f; split; auto.
  exact (asm_body_lift nil _ Gu Gw f ip CS CO ar_norepet (Forall_nil _) CG SB).
Qed.

Ltac ar_kit_one f csub body :=
  eapply (ar_lift_one _ f); [| | | | apply body]; [exact csub | repeat constructor | vm_compute; reflexivity |].

Ltac ar_kit_env :=
  apply asm_covers_incl; [apply ar_norepet' |]; intros [i s] Hx;
  repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx;
  (apply ar_env_in; [unfold env_specs_gp, asm_env.env_specs; simpl; auto 10 | reflexivity]).

Lemma ar_bodies_kit : asm_bodies W p Gw (ar_inlines ++ ar_Gh).
Proof.
  destruct K as (Kupto & Ku64 & Kbytes & Keq & Kmz & Kle).
  pose proof (cs_sub_ae_roundtrip C20P ltac:(ar_in_cs)) as SC.
  repeat apply Forall_cons; try apply Forall_nil.
  - ar_kit_one WgNoise.chacha20poly1305.code.f_memzero_explicit SC Kmz.
    constructor; [| constructor].
    exists (snd (@memset_spec Libc.CS)). split.
    + apply ar_find_Gr, ar_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS C20P ar_cce_l5).
  - ar_kit_one WgNoise.chacha20poly1305.code.f_get_unaligned_le32 SC Kle. constructor.
  - ar_kit_one WgNoise.harness.ae_roundtrip.code.f_upto (@cspecs_sub_refl W) Kupto. ar_kit_env.
  - ar_kit_one WgNoise.harness.ae_roundtrip.code.f_any_u64 (@cspecs_sub_refl W) Ku64. ar_kit_env.
  - ar_kit_one WgNoise.harness.ae_roundtrip.code.f_any_bytes (@cspecs_sub_refl W) Kbytes. ar_kit_env.
  - ar_kit_one WgNoise.harness.ae_roundtrip.code.f_bytes_eq (@cspecs_sub_refl W) Keq. constructor.
Qed.
End Kit.

(* ---------- main ---------- *)
Lemma ar_covers_main : asm_covers Gw ar_Gmain.
Proof.
  unfold ar_Gmain. apply asm_covers_app.
  - apply asm_covers_incl; [apply ar_norepet' |]. intros [i s] Hx.
    repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx;
      (apply ar_env_in; [unfold env_specs_gp, asm_env.env_specs; simpl; auto 10 | reflexivity]).
  - constructor; [| constructor; [| apply asm_covers_incl; [apply ar_norepet' |]]].
    + exists (snd chacha20poly1305_encrypt_spec3). split; [| apply ar_encrypt_sub].
      apply ar_find_Gr, ar_in_aead. unfold aead_G3; repeat (first [left; reflexivity | right]).
    + exists (snd chacha20poly1305_decrypt_spec3). split; [| apply ar_decrypt_sub].
      apply ar_find_Gr, ar_in_aead. unfold aead_G3; repeat (first [left; reflexivity | right]).
    + intros x Hx. apply asm_Gr_gp_incl, ar_in_h. exact Hx.
Qed.

Lemma ar_bodies_main : asm_bodies W p Gw [(QP.prog_main p, QPmain_spec_ext' p tt ar_post)].
Proof.
  constructor; [| constructor].
  exists WgNoise.harness.ae_roundtrip.code.f_main. split; [vm_compute; reflexivity |].
  replace (QP.prog_main p) with WgNoise.harness.ae_roundtrip.code._main by (vm_compute; reflexivity).
  apply (asm_body_lift ar_V _ ar_Gmain Gw _ _ (@cspecs_sub_refl W));
    [repeat constructor | exact ar_norepet | ar_varspecs | exact ar_covers_main | exact ar_main_body].
Qed.

Lemma ar_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) ar_Gr.
Proof. repeat constructor. Qed.

Lemma ar_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma ar_bodies (K: wl_kit_ok) :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt ar_post) :: ar_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _
           (asm_bodies_incl _ _ _ _ _ _ ar_bodies_main ar_bodies_libc (incl_refl _))
           (asm_bodies_incl _ _ _ _ _ _ ar_bodies_aead (ar_bodies_kit K) (incl_refl _))).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx]; [left; left; reflexivity |].
  unfold ar_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; right; auto |].
  right. exact Hx.
Qed.

Lemma ae_roundtrip_safe_kit : wl_kit_ok -> harness_safe WgNoise.contracts.ae_roundtrip.whole_prog.
Proof.
  intros K.
  exact (asm_harness_safe_gp p world_OK_whole_ae_roundtrip W W_ae_roundtrip_eq cbc_ae_roundtrip ar_ext_ok ar_post
           ar_Gr ar_ids ar_IDS ar_check ar_cc (ar_bodies K)).
Qed.
