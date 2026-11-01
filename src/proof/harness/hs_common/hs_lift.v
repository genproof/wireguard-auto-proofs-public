(* The helpers of hs_laws.h / hs_unchanged.h in a law's piece.

   Each hs_ harness has its own copy of the helpers it uses, and only those: hs_response_state, for example, has
   no bytes_eq, copy_peer or same_peer.  A body proof lifts into a law's unit (hc3_lift) only if every entry of its
   context is in the law's context, which holds only the program's functions; so the helpers' bodies are stated
   here with their callees only (hs_helpers_ok), and hs_helper_entry moves such a body into the unit
   hs_asm.hs_unit of any hs_ law whose context has those callees. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.common.hc3_xcs.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require WgNoise.contracts.hs_reject_initiation.

(* the helpers' varspecs: those of hs_reject_initiation's harness (the shim's three clocks/counters it declares) *)
Definition hs_Vh : varspecs := QPvarspecs WgNoise.contracts.hs_reject_initiation.Harness.qp.

Section Helpers.
Variable x25519: list byte -> list byte -> list byte.

(* each helper's callees *)
Definition Ghs_any_u64 : funspecs := [nondet_u32_spec].
Definition Ghs_bytes_eq : funspecs := [].
Definition Ghs_any_clocks : funspecs := [nondet_u32_spec; any_u64_spec].
Definition Ghs_new_device : funspecs := [wg_noise_set_static_identity_private_key_spec x25519].
Definition Ghs_new_peer : funspecs := [wg_noise_handshake_init_spec x25519].
Definition Ghs_new_pair : funspecs :=
  [@asm_env.nondet_bytes_spec CSh; wg_noise_init_spec; new_device_spec x25519; new_peer_spec x25519].
Definition Ghs_copy_peer : funspecs := [].
Definition Ghs_same_peer : funspecs := [bytes_eq_spec].

(* the helpers' bodies, on hs_reject_initiation's copies (module H of hs_specs.v), each with its callees *)
Definition hs_helpers_ok : Prop :=
  @semax_body hs_Vh Ghs_any_u64 CSh H.f_any_u64 any_u64_spec /\
  @semax_body hs_Vh Ghs_bytes_eq CSh H.f_bytes_eq bytes_eq_spec /\
  @semax_body hs_Vh Ghs_any_clocks CSh H.f_any_clocks any_clocks_spec /\
  @semax_body hs_Vh Ghs_new_device CSh H.f_new_device (new_device_spec x25519) /\
  @semax_body hs_Vh Ghs_new_peer CSh H.f_new_peer (new_peer_spec x25519) /\
  @semax_body hs_Vh Ghs_new_pair CSh H.f_new_pair (new_pair_spec x25519) /\
  @semax_body hs_Vh Ghs_copy_peer CSh H.f_copy_peer copy_peer_spec /\
  @semax_body hs_Vh Ghs_same_peer CSh H.f_same_peer same_peer_spec.

End Helpers.

(* a helper's body, proved on hs_reject_initiation's copy against a context G0 whose entries are in the law's
   context G (up to funspec_sub), is an entry of the law's piece: the law's copy is the same function, the
   compspecs CSh is included in the world, the body's varspecs V0 are the program's *)
Lemma hs_helper_entry (W: compspecs) (p: QP.program function) (prog: Clight.program) (V0: varspecs) (G G0: funspecs)
    f ip :
  cspecs_sub CSh W ->
  @semax_body V0 G0 CSh f ip ->
  find_internal prog (fst ip) = Some f ->
  Forall (fun it => complete_type (@cenv_cs CSh) (snd it) = true) (fn_vars f) ->
  hc3_Gsub G0 G ->
  hc3_Vsub V0 (QPvarspecs p) G ->
  verified_in (hs_unit W p prog) G ip.
Proof. intros CS B F C HG HV. exact (hc3_lift (hs_unit W p prog) CSh V0 G0 f ip G B F CS C HG HV). Qed.

(* the entries of a callee context found in the law's context, the same specification (nondet_bytes: at another
   compspecs, the same on byte arrays) *)
Ltac hs_gsub :=
  unfold hc3_Gsub;
  repeat (apply Forall_cons;
          [eexists; split; [reflexivity | first [apply funspec_sub_refl | apply hc3_nondet_bytes_xcs]] |]);
  apply Forall_nil.

(* hc3_Vsub for a law: the helpers' varspecs are the program's (vm_compute) and are not functions of G *)
Ltac hs_vsub :=
  unfold hc3_Vsub; first [apply Forall_nil | unfold hs_Vh];
  match goal with |- Forall _ ?l => let x := eval vm_compute in l in change l with x end;
  repeat (apply Forall_cons; [split; [reflexivity | vm_compute; reflexivity] |]); apply Forall_nil.
