(* law prim_blake2s assembled: one whole-program Component
   over prim_blake2s.whole_prog from three pieces: libc (libc_piece), BLAKE2s (b2s_piece3) and the harness
   (hb2s_piece). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.contracts.x_prim_blake2s.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_xcs3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.blake2s.b2s_piece3.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_piece.

Local Notation p := WgNoise.contracts.x_prim_blake2s.whole_prog.
Local Notation W := W_prim_blake2s.

(* the real specifications, main excepted *)
Definition hb2s_Gr : funspecs :=
  libc_G W ++ blake2s_G3 ++ filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) hb2s_G.

Definition hb2s_ids : list ident := ltac:(let l := eval compute in (map fst hb2s_Gr) in exact l).

Local Notation Gw := (@asm_Gall W p hb2s_post hb2s_Gr hb2s_ids).

Lemma hb2s_IDS : map fst hb2s_Gr = hb2s_ids.
Proof. reflexivity. Qed.

Lemma hb2s_check : asm_check W p hb2s_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hb2s_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hb2s_IDS | apply hb2s_check]. Qed.

Lemma hb2s_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hb2s_IDS | apply hb2s_check]. Qed.

Lemma hb2s_cs_sub cs : In cs all_unit_cs -> cspecs_sub cs W.
Proof.
  destruct world_ok_prim_blake2s as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. intros H. apply HF. right; auto.
Qed.

Ltac hb2s_in_cs := unfold all_unit_cs; simpl; repeat first [left; reflexivity | right].

Ltac hb2s_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hb2s_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

Lemma hb2s_in_Gr ix : In ix hb2s_Gr -> In ix Gw.
Proof. apply asm_Gr_incl. Qed.

(* ---------- libc ---------- *)
Lemma hb2s_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hb2s_norepet.
  - intros x Hx. apply hb2s_in_Gr. unfold hb2s_Gr. apply in_app; left; auto.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hb2s_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply hb2s_cs_sub; hb2s_in_cs |]; split; [hb2s_varspecs |]; split; [apply CI | hb2s_funs].
Qed.

(* ---------- BLAKE2s ---------- *)
#[local] Instance CCE_libc_b2s : change_composite_env Libc.CS Blake2s.CS.
Proof. make_cs_preserve Libc.CS Blake2s.CS. Defined.
#[local] Instance CCE_libc_cookie : change_composite_env Libc.CS Cookie.CS.
Proof. make_cs_preserve Libc.CS Cookie.CS. Defined.

Lemma hb2s_find_libc i s : In (i, s) (libc_G W) -> initial_world.find_id i Gw = Some s.
Proof.
  intros H. apply initial_world.find_id_i; [| apply hb2s_norepet'].
  apply hb2s_in_Gr. unfold hb2s_Gr. apply in_app; left; auto.
Qed.

Lemma hb2s_covers_b2s_imports cs (CCE: change_composite_env Libc.CS cs) :
  asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply hb2s_find_libc. left; reflexivity.
    + apply (@xcs_memcpy_sub Libc.CS cs CCE).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply hb2s_find_libc. right; left; reflexivity.
    + apply (@xcs_memset_sub Libc.CS cs CCE).
Qed.

Lemma hb2s_bodies_b2s : asm_bodies W p Gw blake2s_G3.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_cookie] blake2s_imports3 blake2s_G3 blake2s_piece3).
  - apply hb2s_norepet.
  - intros x Hx. apply hb2s_in_Gr. unfold hb2s_Gr. apply in_app; right; apply in_app; left; auto.
  - constructor; [| constructor; [| constructor]].
    + split; [apply hb2s_cs_sub; hb2s_in_cs |]. split; [hb2s_varspecs |].
      split; [apply (hb2s_covers_b2s_imports Blake2s.CS CCE_libc_b2s) | hb2s_funs].
    + split; [apply hb2s_cs_sub; hb2s_in_cs |]. split; [hb2s_varspecs |].
      split; [apply (hb2s_covers_b2s_imports Cookie.CS CCE_libc_cookie) | hb2s_funs].
Qed.

(* ---------- the harness ---------- *)
Lemma hb2s_bodies_harness : asm_bodies W p Gw hb2s_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hb2s] hb2s_imports hb2s_G hb2s_piece).
  - apply hb2s_norepet.
  - intros x Hx. unfold hb2s_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply hb2s_in_Gr; unfold hb2s_Gr; apply in_app; right; apply in_app; right; apply filter_In; split;
                [unfold hb2s_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [| constructor]. split; [apply cspecs_sub_refl |]. split; [| split].
    + hb2s_varspecs.
    + apply asm_covers_incl; [apply hb2s_norepet' |].
      intros [i s] Hx. apply in_app in Hx as [Hx|Hx].
      * apply asm_E_incl; auto. unfold asm_env.env_specs in Hx.
        repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
      * apply hb2s_in_Gr. unfold hb2s_Gr. apply in_app; right; apply in_app; left.
        repeat destruct Hx as [<-|Hx]; try contradiction; unfold blake2s_G3; repeat (first [left; reflexivity | right]).
    + hb2s_funs.
Qed.

Lemma hb2s_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hb2s_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hb2s_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hb2s_Gr.
Proof. repeat constructor. Qed.

Lemma hb2s_bodies : asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hb2s_post) :: hb2s_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ (asm_bodies_incl _ _ _ _ _ _ hb2s_bodies_libc hb2s_bodies_b2s (incl_refl _))
           hb2s_bodies_harness).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. unfold hb2s_G. repeat (first [left; reflexivity | right]).
  - unfold hb2s_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; apply in_app; left; auto |].
    apply in_app in Hx as [Hx|Hx]; [left; apply in_app; right; auto |].
    right. apply filter_In in Hx as [Hx _]; auto.
Qed.

Theorem prim_blake2s_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_prim_blake2s W W_prim_blake2s_eq hb2s_cbc hb2s_ext_ok hb2s_post
           hb2s_Gr hb2s_ids hb2s_IDS hb2s_check hb2s_cc hb2s_bodies).
Qed.
