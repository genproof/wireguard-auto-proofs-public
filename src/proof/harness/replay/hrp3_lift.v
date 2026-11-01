(* law replay: lifting a body proved against a small context (V0 / G0) to the unit. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.

Lemma hrp3l_make_tycontext_g: forall V G i,
  Maps.PTree.get i (make_tycontext_g V G) =
  match initial_world.find_id i G with Some phi => Some (type_of_funspec phi) | None => initial_world.find_id i V end.
Proof.
  intros. induction G as [|[j phi] G IH]; simpl.
  - apply semax_prog.make_tycontext_g_nilG_find_id.
  - rewrite Maps.PTree.gsspec. unfold eq_dec, Memory.EqDec_ident, ident_eq.
    destruct (peq i j); auto.
Qed.

Lemma hrp3l_funspec_sub_type: forall phi psi, funspec_sub phi psi -> type_of_funspec phi = type_of_funspec psi.
Proof.
  intros [? ? ? ? ? ? ?] [? ? ? ? ? ? ?] [[? ?] _]; subst; reflexivity.
Qed.

(* V0 / G0 against the law's context *)
Definition hrp3l_Gsub (G0 G: funspecs) : Prop :=
  Forall (fun ip => exists phi, initial_world.find_id (fst ip) G = Some phi /\ funspec_sub phi (snd ip)) G0.
Definition hrp3l_Vsub (V0 V: varspecs) (G: funspecs) : Prop :=
  Forall (fun it => initial_world.find_id (fst it) G = None /\ initial_world.find_id (fst it) V = Some (snd it)) V0.

Lemma hrp3l_tycontext_sub: forall f V0 G0 V G,
  hrp3l_Gsub G0 G -> hrp3l_Vsub V0 V G ->
  tycontext_sub (func_tycontext f V0 G0 nil) (func_tycontext f V G nil).
Proof.
  intros f V0 G0 V G HG HV.
  apply tycontext_sub_i99. split; intros i.
  - rewrite !hrp3l_make_tycontext_g.
    destruct (initial_world.find_id i G0) as [phi0|] eqn:E0.
    + apply initial_world.find_id_e in E0. unfold hrp3l_Gsub in HG. rewrite Forall_forall in HG.
      destruct (HG _ E0) as [phi [E1 S]]; simpl in E1. rewrite E1. simpl.
      f_equal. apply hrp3l_funspec_sub_type; auto.
    + destruct (initial_world.find_id i V0) as [t|] eqn:E1; simpl; auto.
      apply initial_world.find_id_e in E1. unfold hrp3l_Vsub in HV. rewrite Forall_forall in HV.
      destruct (HV _ E1) as [N1 N2]; simpl in N1, N2. rewrite N1, N2. auto.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i G0) as [phi0|] eqn:E0; simpl; auto.
    apply initial_world.find_id_e in E0. unfold hrp3l_Gsub in HG. rewrite Forall_forall in HG.
    destruct (HG _ E0) as [phi [E1 S]]; simpl in E1. exists phi; split; auto.
    apply funspec_sub_sub_si; auto.
Qed.

Lemma hrp3l_lift: forall (u: unit_ctx) (CS0: compspecs) V0 G0 f ip G,
  @semax_body V0 G0 CS0 f ip ->
  find_internal (u_prog u) (fst ip) = Some f ->
  cspecs_sub CS0 (u_cs u) ->
  Forall (fun it => complete_type (@cenv_cs CS0) (snd it) = true) (fn_vars f) ->
  hrp3l_Gsub G0 G -> hrp3l_Vsub V0 (u_V u) G ->
  verified_in u G ip.
Proof.
  intros u CS0 V0 G0 f ip G B F C T HG HV.
  exists f; split; auto.
  apply (@semax_body_cenv_sub CS0 (u_cs u) C) in B; auto.
  eapply semax_body_subsumption; [exact B |].
  apply hrp3l_tycontext_sub; auto.
Qed.
