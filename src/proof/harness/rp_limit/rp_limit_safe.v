(* Law rp_limit, as stated by harness/rp_limit.c and its first comment.
   The assembly of the law from its harness's main and the shared specification of counter_validate
   (src/proof/counter/), in the law's world (src/proof/harness/rp_common/rp_worlds.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.rp_limit.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_piece3.
Require Import WgNoise.proof.harness.rp_limit.rp_limit_spec.
Require Import WgNoise.proof.harness.rp_limit.rp_limit_piece.

(* The program reaches only counter_validate.c's four functions, the harness's own functions and the
   external world (nondet_u8, nondet_u32, nondet_size, gp_assert). *)
Section Assembly.
Local Notation p := WgNoise.contracts.rp_limit.whole_prog.

Definition rp_limit_Gr : funspecs :=
  cnt_G ++ filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) rp_limit_G.

Definition rp_limit_ids : list ident := ltac:(let l := eval compute in (map fst rp_limit_Gr) in exact l).

Local Notation Gw := (@asm_Gall_gp W_rp_limit p rp_limit_post rp_limit_Gr rp_limit_ids).

Lemma rp_limit_IDS : map fst rp_limit_Gr = rp_limit_ids.
Proof. reflexivity. Qed.

Lemma rp_limit_check : asm_check_gp W_rp_limit p rp_limit_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma rp_limit_sub_counter : cspecs_sub Counter.CS W_rp_limit.
Proof.
  destruct world_ok_rp_limit as (_ & _ & _ & H).
  inversion H as [|? ? _ H1]; subst. inversion H1; subst; assumption.
Qed.

Lemma rp_limit_bodies_counter : asm_bodies W_rp_limit p Gw cnt_G.
Proof.
  apply (asm_piece_lift W_rp_limit p Gw [u_counter] cnt_imports cnt_G cnt_piece3).
  - apply asm_Gall_gp_norepet; [apply rp_limit_IDS | apply rp_limit_check].
  - intros x Hx. apply asm_Gr_gp_incl. unfold rp_limit_Gr. apply in_app; left; auto.
  - constructor; [|constructor]. split; [exact rp_limit_sub_counter|]. split; [|split; [constructor|]].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma rp_limit_bodies_harness : asm_bodies W_rp_limit p Gw rp_limit_G.
Proof.
  apply (asm_piece_lift W_rp_limit p Gw [u_rp_limit] rp_limit_imports rp_limit_G rp_limit_piece).
  - apply asm_Gall_gp_norepet; [apply rp_limit_IDS | apply rp_limit_check].
  - intros x Hx. unfold rp_limit_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_gp_incl; unfold rp_limit_Gr; apply in_app; right; apply filter_In; split;
                [unfold rp_limit_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [|constructor]. split; [apply cspecs_sub_refl|]. split; [|split].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + apply asm_covers_incl; [apply asm_Gall_gp_norepet'; [apply rp_limit_IDS | apply rp_limit_check]|].
      intros [i s] Hx.
      unfold rp_limit_imports, QuickProof.Env.nondet_u8_spec, QuickProof.Env.nondet_u32_spec,
        QuickProof.Env.nondet_size_spec, QuickProof.Env.gp_assert_spec, wg_counter_validate_spec in Hx.
      repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx.
      5:{ apply asm_Gr_gp_incl. unfold rp_limit_Gr. apply in_app; left.
          unfold cnt_G, wg_counter_validate_spec; repeat (first [left; reflexivity | right]). }
      all: apply asm_E_gp_incl; [unfold env_specs_gp, asm_env.env_specs;
                                  repeat (first [left; reflexivity | right]) | reflexivity].
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma rp_limit_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma rp_limit_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma rp_limit_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) rp_limit_Gr.
Proof. repeat constructor. Qed.

Lemma rp_limit_bodies :
  asm_bodies W_rp_limit p Gw ((QP.prog_main p, QPmain_spec_ext' p tt rp_limit_post) :: rp_limit_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ rp_limit_bodies_counter rp_limit_bodies_harness).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. unfold rp_limit_G. repeat (first [left; reflexivity | right]).
  - unfold rp_limit_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; auto|].
    right. apply filter_In in Hx as [Hx _]; auto.
Qed.
End Assembly.

Theorem rp_limit_safe : harness_safe WgNoise.contracts.rp_limit.whole_prog.
Proof.
  exact (asm_harness_safe_gp _ world_OK_whole_rp_limit W_rp_limit W_rp_limit_eq rp_limit_cbc rp_limit_ext_ok
           rp_limit_post rp_limit_Gr rp_limit_ids rp_limit_IDS rp_limit_check rp_limit_cc rp_limit_bodies).
Qed.
