(* Law rp_any_order, as stated by harness/rp_any_order.c and its first comment.
   The assembly of the law from its harness's piece (rp_any_order_piece.v) and the shared specification of
   counter_validate (src/proof/counter/), in the law's world (src/proof/harness/rp_common/rp_worlds.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.rp_any_order.
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_piece3.
Require Import WgNoise.proof.harness.rp_any_order.rp_any_order_spec.
Require Import WgNoise.proof.harness.rp_any_order.rp_any_order_piece.

(* The assembly: the program is the harness and counter_validate.c; its externals are the nondet_ functions
   and gp_assert (asm_assert.v). *)
Section Assembly.
Local Notation p := WgNoise.contracts.rp_any_order.whole_prog.

Definition rao_Gr : funspecs :=
  cnt_G ++ filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) rao_G.

Definition rao_ids : list ident := ltac:(let l := eval compute in (map fst rao_Gr) in exact l).

Local Notation Gw := (@asm_Gall_gp W_rp_any_order p rao_post rao_Gr rao_ids).

Lemma rao_IDS : map fst rao_Gr = rao_ids.
Proof. reflexivity. Qed.

Lemma rao_check : asm_check_gp W_rp_any_order p rao_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma rao_sub_counter : cspecs_sub Counter.CS W_rp_any_order.
Proof.
  destruct world_ok_rp_any_order as (_ & _ & _ & H).
  inversion H as [|? ? _ H1]; subst. inversion H1; subst; assumption.
Qed.

Lemma rao_bodies_counter : asm_bodies W_rp_any_order p Gw cnt_G.
Proof.
  apply (asm_piece_lift W_rp_any_order p Gw [u_counter] cnt_imports cnt_G cnt_piece3).
  - apply asm_Gall_gp_norepet; [apply rao_IDS | apply rao_check].
  - intros x Hx. apply asm_Gr_gp_incl. unfold rao_Gr. apply in_app; left; auto.
  - constructor; [|constructor]. split; [exact rao_sub_counter|]. split; [|split; [constructor|]].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma rao_bodies_harness : asm_bodies W_rp_any_order p Gw rao_G.
Proof.
  apply (asm_piece_lift W_rp_any_order p Gw [u_rao] rao_imports rao_G rao_piece).
  - apply asm_Gall_gp_norepet; [apply rao_IDS | apply rao_check].
  - intros x Hx. unfold rao_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_gp_incl; unfold rao_Gr; apply in_app; right; apply filter_In; split;
                [unfold rao_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [|constructor]. split; [apply cspecs_sub_refl|]. split; [|split].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + apply asm_covers_incl; [apply asm_Gall_gp_norepet'; [apply rao_IDS | apply rao_check]|].
      intros [i s] Hx. unfold rao_imports in Hx.
      repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx;
        first [ apply asm_E_gp_incl; [unfold env_specs_gp, asm_env.env_specs; simpl;
                                      repeat (first [left; reflexivity | right]) | reflexivity]
              | apply asm_Gr_gp_incl; unfold rao_Gr; apply in_app; left;
                unfold cnt_G; repeat (first [left; reflexivity | right]) ].
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma rao_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma rao_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma rao_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) rao_Gr.
Proof. repeat constructor. Qed.

Lemma rao_bodies :
  asm_bodies W_rp_any_order p Gw ((QP.prog_main p, QPmain_spec_ext' p tt rao_post) :: rao_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ rao_bodies_counter rao_bodies_harness).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. unfold rao_G. repeat (first [left; reflexivity | right]).
  - unfold rao_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; auto|].
    right. apply filter_In in Hx as [Hx _]; auto.
Qed.
End Assembly.

Theorem rp_any_order_safe : harness_safe WgNoise.contracts.rp_any_order.whole_prog.
Proof.
  exact (asm_harness_safe_gp _ world_OK_whole_rp_any_order W_rp_any_order W_rp_any_order_eq rao_cbc rao_ext_ok
           rao_post rao_Gr rao_ids rao_IDS rao_check rao_cc rao_bodies).
Qed.
