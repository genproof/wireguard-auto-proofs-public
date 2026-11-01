(* law transport_order: the initial globals main keeps (main_pre's InitGPred of
   the whole program): the shim's zero page (read by the kernel AEAD) and rp_final's static minusp (read by the
   reference AEAD); the rest is dropped into TT.  As law prim_aead's hm3_init_globals (haead_main_body3_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.transport_order.ht4o_main_defs.
Require WgNoise.contracts.x_transport_order.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

Lemma ht4o_InitGPred_filter (f: ident * globdef (fundef function) type -> bool) al gv :
  InitGPred al gv |-- (InitGPred (filter f al) gv * TT)%logic.
Proof.
  induction al as [|a al IH]; simpl.
  - unfold InitGPred; simpl. cancel.
  - unfold InitGPred in *; simpl. destruct (f a); simpl.
    + rewrite sepcon_assoc. apply sepcon_derives; auto.
    + eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply IH] |].
      rewrite (sepcon_comm (fold_right _ _ _)), <- sepcon_assoc, TT_sepcon_TT. cancel.
Qed.

Definition ht4o_keep (x: ident * globdef (fundef function) type) : bool :=
  Pos.eqb (fst x) ht4o_mp || Pos.eqb (fst x) _quickproof_zero_page.

Definition ht4o_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter ht4o_keep (Vardefs WgNoise.contracts.x_transport_order.whole_prog)) in exact x).

Lemma ht4o_vardefs_eq :
  filter ht4o_keep (Vardefs WgNoise.contracts.x_transport_order.whole_prog) = ht4o_vardefs.
Proof. vm_compute. reflexivity. Qed.

Lemma ht4o_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_transport_order.whole_prog) gv |--
  (zero_page gv * ht4_minusp ht4o_mp gv * TT)%logic.
Proof.
  intros Hgv. eapply derives_trans; [apply (ht4o_InitGPred_filter ht4o_keep) |].
  rewrite ht4o_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred ht4o_vardefs gv |-- (fun g => zero_page g * ht4_minusp ht4o_mp g)%logic gv).
  eapply InitGPred_process_globvars; auto.
  let Delta := fresh "Delta" in let Delta' := fresh "Delta'" in
  set (Delta' := vardefs_tycontext _);
  set (Delta := @abbreviate tycontext Delta');
  change Delta' with Delta;
  hnf in Delta'; simpl in Delta'; subst Delta'.
  simpl vardefs_to_globvars.
  eapply derives_trans; [process_globals | ].
  clear Delta. apply finish_process_globvars'. unfold fold_right_sepcon at 1.
  simpl readonly2share. rewrite sepcon_emp.
  match goal with |- data_at ?sh (tarray tuint 17) ?l ?p * _ |-- _ =>
    replace l with (map Vint hrp_minusp) by
      (vm_compute; repeat match goal with |- cons _ _ = cons _ _ => f_equal
                                     | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity end) end.
  rewrite sepcon_comm.
  unfold zero_page, ht4_minusp. apply sepcon_derives; [| apply derives_refl].
  rewrite zero_val_tarray. replace (zero_val tuchar) with (Vubyte Byte.zero) by (rewrite zero_val_eq; reflexivity).
  match goal with |- data_at _ _ _ (gv ?i) |-- data_at _ _ _ (gv ?j) =>
    replace i with j by reflexivity end.
  apply derives_refl.
Qed.
