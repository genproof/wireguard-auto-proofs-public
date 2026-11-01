(* main's precondition in the hs_ programs: the initial values of the globals.

   The eight hs_ programs have the same global variables (Vardefs: the shim's, noise.c's, the primitives' tables;
   the harnesses only declare the shim's clocks and allocation count).  Their initial values, as main's
   precondition gives them (InitGPred, used with VST's main_pre_InitGpred), contain: the shim's state with every
   global zero (hs_shim0) and no refcount_t warning (hs_w0); noise.c's globals before wg_noise_init (initial hash
   and chaining key zero, keypair_counter 0); the read-only tables of the primitives (wg_consts5); the rest is
   dropped (TT). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require WgNoise.contracts.hs_begin_session_state WgNoise.contracts.hs_matching_keys
        WgNoise.contracts.hs_reject_initiation WgNoise.contracts.hs_reject_response
        WgNoise.contracts.hs_replay_initiation WgNoise.contracts.hs_response_state
        WgNoise.contracts.hs_session_erases WgNoise.contracts.hs_stale_response.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require WgNoise.proof.harness.consume_response_any.hcr5_globals.
Local Open Scope logic.

(* the shim's state at the start: every global zero *)
Definition hs_shim0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

(* no refcount_t warning yet *)
Definition hs_w0 : list int64 := repeat Int64.zero 5.

(* the globals at main's entry, from InitGPred of the program's variables *)
Definition hs_globals0 (gv: globals) : mpred :=
  shim_state4 gv hs_shim0 hs_w0 * noise_globals_raw gv zeros32 zeros32 Int64.zero * wg_consts5 gv * TT.

(* the same lemma for an x_ program, whose cs-generic helpers are reused: a 32-byte point initialized by one byte,
   keypair_counter, sigma flattened, the refcount_t warnings *)
Module G5 := WgNoise.proof.harness.consume_response_any.hcr5_globals.

(* the variables of the program with sigma (u8 [10][16]) seen as a flat byte array (as for the x_ programs:
   globvar2pred ignores gvar_info, and process_globals hangs on 2-D arrays) *)
Definition hs_glob_vardefs :=
  ltac:(let x := eval vm_compute in (map G5.hcr5_glob_flat (Vardefs WgNoise.contracts.hs_response_state.whole_prog))
        in exact x).

Lemma hs_glob_InitGPred_flat gv :
  InitGPred (Vardefs WgNoise.contracts.hs_response_state.whole_prog) gv = InitGPred hs_glob_vardefs gv.
Proof. reflexivity. Qed.

(* process_globals works at the world of the hs_ programs *)
#[local] Existing Instance W_hs_response_state.

#[local] Instance hs_glob_cceN : change_composite_env Noise.CS W_hs_response_state.
Proof. make_cs_preserve Noise.CS W_hs_response_state. Defined.
#[local] Instance hs_glob_cceB : change_composite_env WgNoise.units.Blake2s.CS W_hs_response_state.
Proof. make_cs_preserve WgNoise.units.Blake2s.CS W_hs_response_state. Defined.

(* one global of the processed list is one of the target: same object, values equal by computation *)
Lemma hs_glob_eq {cs: compspecs} sh t t' (v: reptype t) (v': reptype t') p p' :
  t = t' -> JMeq v v' -> p = p' -> data_at sh t v p = data_at sh t' v' p'.
Proof. intros -> E ->. apply JMeq_eq in E. subst. reflexivity. Qed.

(* turn the processed global at the target's address into the target's form (values equal by computation) *)
Ltac hs_glob_match gv :=
  match goal with |- ?L |-- ?R =>
    match R with context [@data_at W_hs_response_state ?sh' ?t' ?v' (gv ?i')] =>
      lazymatch L with context [@data_at W_hs_response_state sh' t' v' (gv i')] => fail | _ => idtac end;
      let j := eval compute in i' in
      match L with context [@data_at W_hs_response_state ?sh ?t ?v (gv j)] =>
        rewrite (hs_glob_eq sh t t' v v' (gv j) (gv i') eq_refl ltac:(G5.hcr5_glob_jmeq) eq_refl)
      end
    end
  end.

Lemma hs_init_globals gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_response_state.whole_prog) gv |-- hs_globals0 gv.
Proof.
  intros Hgv. rewrite hs_glob_InitGPred_flat.
  change (InitGPred hs_glob_vardefs gv |-- (fun g => hs_globals0 g) gv).
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
  repeat match goal with |- context [mapsto_zeros 31 ?sh (offset_val 1 (gv ?i))] =>
    match goal with |- context [mapsto sh tuchar (gv i) ?v] =>
      sep_apply (G5.hcr5_glob_pt gv i sh v Hgv readable_Ers) end end.
  match goal with |- context [mapsto ?sh tulong (gv ?i) (Vlong ?z)] =>
    sep_apply (G5.hcr5_glob_atomic gv i sh z Hgv) end.
  match goal with |- context [data_at ?sh (tarray tuchar 160) ?l ?p] =>
    replace l with (concat blake2s_sigma_val) by (vm_compute; reflexivity) end.
  rewrite G5.hcr5_glob_sigma_flat.
  unfold hs_globals0, shim_state4, shim_core, noise_globals_raw, wg_consts5, blake2s_globals, curve25519_globals,
    zero_page.
  rewrite (prop_true_andp (shim_ok hs_shim0)) by (split; reflexivity).
  rewrite (prop_true_andp (Zlength zeros32 = 32 /\ _)) by (split; reflexivity).
  repeat match goal with |- context [@data_at ?cs ?sh ?t ?v] =>
    lazymatch cs with W_hs_response_state => fail | _ => idtac end;
    rewrite (@data_at_change_composite cs W_hs_response_state _ sh t v v (JMeq_refl v)) by prove_cs_preserve_type
  end.
  autorewrite with zero_val.
  replace (zero_val tuchar) with (Vint Int.zero) by (unfold tuchar; rewrite zero_val_Tint; reflexivity).
  repeat hs_glob_match gv.
  sep_apply (G5.hcr5_glob_refwarn4 (cs := W_hs_response_state) gv _ eq_refl).
  change (refwarn4 gv WgNoise.proof.harness.consume_response_any.hcr5_defs.hcr5_w0) with (refwarn4 gv hs_w0).
  cancel.
Qed.

Lemma hs_init_globals_begin_session_state gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_begin_session_state.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_begin_session_state.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_matching_keys gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_matching_keys.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_matching_keys.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_reject_initiation gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_reject_initiation.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_reject_initiation.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_reject_response gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_reject_response.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_reject_response.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_replay_initiation gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_replay_initiation.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_replay_initiation.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_response_state gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_response_state.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_response_state.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_session_erases gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_session_erases.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_session_erases.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.

Lemma hs_init_globals_stale_response gv :
  globals_ok gv -> InitGPred (Vardefs WgNoise.contracts.hs_stale_response.whole_prog) gv |-- hs_globals0 gv.
Proof.
  replace (Vardefs WgNoise.contracts.hs_stale_response.whole_prog)
    with (Vardefs WgNoise.contracts.hs_response_state.whole_prog) by (vm_compute; reflexivity).
  apply hs_init_globals.
Qed.
