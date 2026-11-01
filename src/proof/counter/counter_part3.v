(* the law counter (the replay window counter_validate). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.
Require WgNoise.contracts.x_counter.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_piece3.
Require Import WgNoise.proof.harness.counter.hcnt_spec3.
Require Import WgNoise.proof.harness.counter.hcnt_piece3.

(* The assembly: the harness
   reaches only counter_validate.c, the harness's own functions and the external world, so the lower pieces
   (blake2s, aead, x25519) are not needed. *)
Section Assembly.
Local Notation p := WgNoise.contracts.x_counter.whole_prog.

Definition cnt3_Gr : funspecs :=
  cnt_G ++ filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) hcnt3_G.

Definition cnt3_ids : list ident := ltac:(let l := eval compute in (map fst cnt3_Gr) in exact l).

Local Notation Gw := (@asm_Gall W_counter p hcnt3_post cnt3_Gr cnt3_ids).

Lemma cnt3_IDS : map fst cnt3_Gr = cnt3_ids.
Proof. reflexivity. Qed.

Lemma cnt3_check : asm_check W_counter p cnt3_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma cnt3_sub_counter : cspecs_sub Counter.CS W_counter.
Proof.
  destruct world_ok_counter as (_ & _ & _ & H).
  inversion H as [|? ? _ H1]; subst. inversion H1 as [|? ? _ H2]; subst.
  inversion H2 as [|? ? _ H3]; subst. inversion H3; subst; assumption.
Qed.

Lemma cnt3_bodies_counter : asm_bodies W_counter p Gw cnt_G.
Proof.
  apply (asm_piece_lift W_counter p Gw [u_counter] cnt_imports cnt_G cnt_piece3).
  - apply asm_Gall_norepet; [apply cnt3_IDS | apply cnt3_check].
  - intros x Hx. apply asm_Gr_incl. unfold cnt3_Gr. apply in_app; left; auto.
  - constructor; [|constructor]. split; [exact cnt3_sub_counter|]. split; [|split; [constructor|]].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma cnt3_bodies_harness : asm_bodies W_counter p Gw hcnt3_G.
Proof.
  apply (asm_piece_lift W_counter p Gw [u_hcnt3] hcnt3_imports hcnt3_G hcnt_piece3).
  - apply asm_Gall_norepet; [apply cnt3_IDS | apply cnt3_check].
  - intros x Hx. unfold hcnt3_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_incl; unfold cnt3_Gr; apply in_app; right; apply filter_In; split;
                [unfold hcnt3_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [|constructor]. split; [apply cspecs_sub_refl|]. split; [|split].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + apply asm_covers_incl; [apply asm_Gall_norepet'; [apply cnt3_IDS | apply cnt3_check]|].
      intros [i s] Hx. apply in_app in Hx as [Hx|Hx].
      * apply asm_E_incl; auto. unfold asm_env.env_specs in Hx.
        repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
      * apply asm_Gr_incl. unfold cnt3_Gr. apply in_app; left.
        destruct Hx as [<-|Hx]; [|contradiction]. unfold cnt_G; repeat (first [left; reflexivity | right]).
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma cnt3_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma cnt3_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma cnt3_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) cnt3_Gr.
Proof. repeat constructor. Qed.

Lemma cnt3_bodies :
  asm_bodies W_counter p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hcnt3_post) :: cnt3_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ cnt3_bodies_counter cnt3_bodies_harness).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. unfold hcnt3_G. repeat (first [left; reflexivity | right]).
  - unfold cnt3_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; auto|].
    right. apply filter_In in Hx as [Hx _]; auto.
Qed.

Theorem cnt3_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_counter W_counter W_counter_eq cnt3_cbc cnt3_ext_ok hcnt3_post
           cnt3_Gr cnt3_ids cnt3_IDS cnt3_check cnt3_cc cnt3_bodies).
Qed.
End Assembly.

Theorem counter_part3 :
  blake2s3_ok -> aead3_ok -> x25519_ok3 ->
  harness_safe WgNoise.contracts.x_counter.whole_prog.
Proof.
  intros _ _ _. exact cnt3_safe.
Qed.
