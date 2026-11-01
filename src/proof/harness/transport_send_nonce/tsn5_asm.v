(* Law transport_send_nonce: the assembly.  The harness reaches only its own functions and the external world: no piece of the code
   under test is needed, every other function of the 15 units gets asm_lib's vacuous specification. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_world.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_world_eq.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_spec.
Require Import WgNoise.proof.harness.transport_send_nonce.tsn5_piece.
Require WgNoise.contracts.x_transport_send_nonce.

Section Assembly.
Local Notation p := WgNoise.contracts.x_transport_send_nonce.whole_prog.

(* the real specifications, main excepted *)
Definition tsn5_Gr : funspecs := filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) tsn5_G.

Definition tsn5_ids : list ident := ltac:(let l := eval compute in (map fst tsn5_Gr) in exact l).

Local Notation Gw := (@asm_Gall W_tsn5 p tsn5_post tsn5_Gr tsn5_ids).

Lemma tsn5_IDS : map fst tsn5_Gr = tsn5_ids.
Proof. reflexivity. Qed.

Lemma tsn5_check : asm_check W_tsn5 p tsn5_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma tsn5_bodies_harness : asm_bodies W_tsn5 p Gw tsn5_G.
Proof.
  apply (asm_piece_lift W_tsn5 p Gw [u_tsn5] tsn5_imports tsn5_G tsn5_piece).
  - apply asm_Gall_norepet; [apply tsn5_IDS | apply tsn5_check].
  - intros x Hx. unfold tsn5_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_incl; unfold tsn5_Gr; apply filter_In; split;
                [unfold tsn5_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [|constructor]. split; [apply cspecs_sub_refl|]. split; [|split].
    + apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
        vm_compute; reflexivity.
    + apply asm_covers_incl; [apply asm_Gall_norepet'; [apply tsn5_IDS | apply tsn5_check]|].
      intros [i s] Hx. unfold tsn5_imports in Hx.
      apply asm_E_incl; auto. unfold asm_env.env_specs in Hx.
      repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma tsn5_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma tsn5_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma tsn5_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) tsn5_Gr.
Proof. repeat constructor. Qed.

Lemma tsn5_bodies :
  asm_bodies W_tsn5 p Gw ((QP.prog_main p, QPmain_spec_ext' p tt tsn5_post) :: tsn5_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ tsn5_bodies_harness tsn5_bodies_harness).
  intros x Hx. apply in_app. left. destruct Hx as [<-|Hx].
  - unfold tsn5_G. repeat (first [left; reflexivity | right]).
  - unfold tsn5_Gr in Hx. apply filter_In in Hx as [Hx _]; auto.
Qed.

Theorem tsn5_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p tsn5_OK W_tsn5 tsn5_eq tsn5_cbc tsn5_ext_ok tsn5_post
           tsn5_Gr tsn5_ids tsn5_IDS tsn5_check tsn5_cc tsn5_bodies).
Qed.
End Assembly.
