(* The harness piece of law ae_split_poly1305 (harness/ae_split_poly1305.c): upto, any_bytes, bytes_eq and main,
   proved in W_asp against the piece's context asp_Gprog (asp_spec.v).  The three wg_laws.h helpers come from
   wl_kit_ok (their bodies for any compspecs, with a context of their callees only, which asp_Gprog contains); main
   is asp_main_body.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require Import WgNoise.proof.harness.ae_split_poly1305.asp_spec.
Require Import WgNoise.proof.harness.ae_split_poly1305.asp_main_body.

#[local] Existing Instance W_asp.

Lemma asp_Gprog_norepet : list_norepet (map fst asp_V ++ map fst asp_Gprog).
Proof. apply compute_list_norepet_e; vm_compute; reflexivity. Qed.

(* a body of the kit, proved with a sublist Gu of the piece's context, holds with the whole context *)
Lemma asp_kit_lift (Gu: funspecs) f ip :
  incl Gu asp_Gprog -> fn_vars f = nil ->
  @semax_body nil Gu W_asp f ip -> @semax_body asp_V asp_Gprog W_asp f ip.
Proof.
  intros INC VARS SB.
  apply (@asm_body_lift W_asp W_asp nil asp_V Gu asp_Gprog f ip cspecs_sub_refl); auto.
  - rewrite VARS; constructor.
  - apply asp_Gprog_norepet.
  - apply asm_covers_incl; auto. apply list_norepet_append_right with (map fst asp_V). apply asp_Gprog_norepet.
Qed.

Ltac asp_incl := intros x Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  unfold asp_Gprog, asp_imports, asp_G; simpl; auto 20.

Theorem asp_piece : wl_kit_ok -> piece_ok [u_asp] asp_imports asp_G.
Proof.
  intros (Kup & _ & Kab & Kbe & _ & _).
  split; [apply compute_list_norepet_e; vm_compute; reflexivity |].
  change (asp_imports (u_cs u_asp) ++ asp_G) with asp_Gprog.
  repeat apply Forall_cons; try apply Forall_nil;
    (exists u_asp; split; [left; reflexivity |]; eexists; split; [reflexivity |]).
  - eapply asp_kit_lift; [| reflexivity | exact (Kup W_asp)]; asp_incl.
  - eapply asp_kit_lift; [| reflexivity | exact (Kab W_asp)]; asp_incl.
  - eapply asp_kit_lift; [| reflexivity | exact (Kbe W_asp)]; asp_incl.
  - apply asp_main_body.
Qed.
