(* The assembly of law ae_split_blake2s (harness/ae_split_blake2s.c), in the law's world W_aesb (aesb_world.v),
   from four groups of bodies:
   - memcpy and memset of libc.c (libc_mem_piece.v: their bodies with no imports);
   - the BLAKE2s piece: blake2s.c's bodies, and the blake2s.h inlines, here compiled into the harness's unit,
     proved under Blake2s.CS on their common Clight (b2s_inline_b2s3.v, blake2s_piece3_in);
   - the wg_laws.h helpers upto, any_bytes, bytes_eq, from the kit wl_kit_ok (bodies for any compspecs);
   - main (aesb_main_body.v).
   The program's externals are the nondet_ functions, quickproof_malloc and gp_assert (asm_assert.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.contracts.ae_split_blake2s.
Require WgNoise.harness.ae_split_blake2s.code.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.assembly.asm_xcs3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_mem_piece.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.blake2s.b2s_inline_b2s3.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require Import WgNoise.proof.harness.ae_split_blake2s.aesb_world.
Require Import WgNoise.proof.harness.ae_split_blake2s.aesb_spec.
Require Import WgNoise.proof.harness.ae_split_blake2s.aesb_main_body.

Section Assembly.
Local Notation p := WgNoise.contracts.ae_split_blake2s.whole_prog.
Local Notation W := W_aesb.
Local Notation hprog := WgNoise.harness.ae_split_blake2s.code.prog.

(* the real specifications, main excepted *)
Definition aesb_Gr : funspecs :=
  libc_mem_G ++ blake2s_G3 ++ filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) aesb_G.

Definition aesb_ids : list ident := ltac:(let l := eval compute in (map fst aesb_Gr) in exact l).

Local Notation Gw := (@asm_Gall_gp W p aesb_post aesb_Gr aesb_ids).

Lemma aesb_IDS : map fst aesb_Gr = aesb_ids.
Proof. reflexivity. Qed.

Lemma aesb_check : asm_check_gp W p aesb_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma aesb_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_gp_norepet; [apply aesb_IDS | apply aesb_check]. Qed.

Lemma aesb_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_gp_norepet'; [apply aesb_IDS | apply aesb_check]. Qed.

Lemma aesb_sub (cs: compspecs) : In cs [WgNoise.contracts.ae_split_blake2s.Harness.CS; Blake2s.CS; Libc.CS] ->
  cspecs_sub cs W.
Proof. destruct world_ok_aesb as (_ & _ & _ & H). rewrite Forall_forall in H. apply H. Qed.

Ltac aesb_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac aesb_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

Lemma aesb_find_libc i s : In (i, s) libc_mem_G -> initial_world.find_id i Gw = Some s.
Proof.
  intros H. apply initial_world.find_id_i; [| apply aesb_norepet'].
  apply asm_Gr_gp_incl. unfold aesb_Gr. apply in_app; left; auto.
Qed.

(* ---------- libc: memcpy, memset ---------- *)
Lemma aesb_bodies_libc : asm_bodies W p Gw libc_mem_G.
Proof.
  apply (asm_piece_lift W p Gw [u_libc] libc_mem_imports libc_mem_G libc_mem_piece).
  - apply aesb_norepet.
  - intros x Hx. apply asm_Gr_gp_incl. unfold aesb_Gr. apply in_app; left; auto.
  - constructor; [| constructor].
    split; [apply aesb_sub; simpl; auto |]. split; [aesb_varspecs |].
    split; [constructor | aesb_funs].
Qed.

(* ---------- BLAKE2s ---------- *)
#[local] Instance CCE_libc_b2s_aesb : change_composite_env Libc.CS Blake2s.CS.
Proof. make_cs_preserve Libc.CS Blake2s.CS. Defined.

Lemma aesb_covers_b2s_imports : asm_covers Gw (blake2s_imports3 Blake2s.CS).
Proof.
  constructor; [| constructor; [| constructor]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply aesb_find_libc. left; reflexivity.
    + apply (@xcs_memcpy_sub Libc.CS Blake2s.CS CCE_libc_b2s_aesb).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply aesb_find_libc. right; left; reflexivity.
    + apply (@xcs_memset_sub Libc.CS Blake2s.CS CCE_libc_b2s_aesb).
Qed.

Lemma aesb_bodies_b2s : asm_bodies W p Gw blake2s_G3.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_b2s_inl hprog] blake2s_imports3 blake2s_G3
           (blake2s_piece3_in hprog eq_refl eq_refl eq_refl eq_refl)).
  - apply aesb_norepet.
  - intros x Hx. apply asm_Gr_gp_incl. unfold aesb_Gr. apply in_app; right; apply in_app; left; auto.
  - constructor; [| constructor; [| constructor]].
    all: split; [apply aesb_sub; simpl; auto |]; split; [aesb_varspecs |].
    all: split; [apply aesb_covers_b2s_imports | aesb_funs].
Qed.

(* ---------- the harness: the wg_laws.h helpers (from the kit) and main ---------- *)
Lemma aesb_norepet_unit : list_norepet (map fst aesb_V ++ map fst aesb_Gprog).
Proof. apply compute_list_norepet_e. vm_compute. reflexivity. Qed.

Lemma aesb_in_imports ix : In ix (aesb_imports W) -> In ix aesb_Gprog.
Proof. intros H. unfold aesb_Gprog. apply in_app; left; auto. Qed.

Lemma aesb_kit_lift f ip (Gu: funspecs) :
  incl Gu (aesb_imports W) ->
  Forall (fun it => complete_type (@cenv_cs W) (snd it) = true) (fn_vars f) ->
  @semax_body nil Gu W f ip -> @semax_body aesb_V aesb_Gprog W f ip.
Proof.
  intros INC COMPL SB.
  apply (@asm_body_lift W W nil aesb_V Gu aesb_Gprog f ip cspecs_sub_refl COMPL aesb_norepet_unit
           (Forall_nil _)); auto.
  apply asm_covers_incl; [apply (list_norepet_append_right _ _ aesb_norepet_unit) |].
  intros x Hx. apply aesb_in_imports, INC, Hx.
Qed.

Lemma aesb_piece (KIT: wl_kit_ok) : piece_ok [u_aesb] aesb_imports aesb_G.
Proof.
  destruct KIT as (Hupto & _ & Hbytes & Heq & _ & _).
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  change (aesb_imports (u_cs u_aesb) ++ aesb_G) with aesb_Gprog.
  repeat constructor.
  all: exists u_aesb; split; [left; reflexivity |]; eexists; split; [reflexivity |].
  - apply (aesb_kit_lift _ _ [nondet_size_spec]); [| repeat constructor | apply (Hupto W)].
    intros x [<-|[]]. unfold aesb_imports. simpl; auto 10.
  - apply (aesb_kit_lift _ _ [(_quickproof_malloc, @malloc_spec' W); @asm_env.nondet_bytes_spec W]);
      [| repeat constructor | apply (Hbytes W)].
    intros x [<-|[<-|[]]]; unfold aesb_imports; simpl; auto 10.
  - apply (aesb_kit_lift _ _ nil); [intros x [] | repeat constructor | apply (Heq W)].
  - exact aesb_main_body.
Qed.

Lemma aesb_bodies_harness (KIT: wl_kit_ok) : asm_bodies W p Gw aesb_G.
Proof.
  apply (asm_piece_lift W p Gw [u_aesb] aesb_imports aesb_G (aesb_piece KIT)).
  - apply aesb_norepet.
  - intros x Hx. unfold aesb_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_gp_incl; unfold aesb_Gr; apply in_app; right; apply in_app; right; apply filter_In;
                split; [unfold aesb_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [| constructor]. split; [apply cspecs_sub_refl |]. split; [| split].
    + aesb_varspecs.
    + apply asm_covers_incl; [apply aesb_norepet' |].
      intros [i s] Hx. unfold aesb_imports in Hx.
      repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx;
        first [ apply asm_E_gp_incl; [unfold env_specs_gp, asm_env.env_specs; simpl;
                                      repeat (first [left; reflexivity | right]) | reflexivity]
              | apply asm_Gr_gp_incl; unfold aesb_Gr; apply in_app; right; apply in_app; left;
                unfold blake2s_G3; repeat (first [left; reflexivity | right]) ].
    + aesb_funs.
Qed.

Lemma aesb_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma aesb_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma aesb_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) aesb_Gr.
Proof. repeat constructor. Qed.

Lemma aesb_bodies (KIT: wl_kit_ok) :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt aesb_post) :: aesb_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _
           (asm_bodies_incl _ _ _ _ _ _ aesb_bodies_libc aesb_bodies_b2s (incl_refl _))
           (aesb_bodies_harness KIT)).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. unfold aesb_G. repeat (first [left; reflexivity | right]).
  - unfold aesb_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; apply in_app; left; auto |].
    apply in_app in Hx as [Hx|Hx]; [left; apply in_app; right; auto |].
    right. apply filter_In in Hx as [Hx _]; auto.
Qed.
End Assembly.

Theorem aesb_safe : wl_kit_ok -> harness_safe WgNoise.contracts.ae_split_blake2s.whole_prog.
Proof.
  intros KIT.
  exact (asm_harness_safe_gp _ world_OK_whole_aesb W_aesb W_aesb_eq aesb_cbc aesb_ext_ok
           aesb_post aesb_Gr aesb_ids aesb_IDS aesb_check aesb_cc (aesb_bodies KIT)).
Qed.
