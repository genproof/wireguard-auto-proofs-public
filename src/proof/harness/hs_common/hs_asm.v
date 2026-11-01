(* The assembly of an hs_ law: harness_safe of its whole program from the shared pieces and the law's own piece.

   An hs_ program links its harness with noise.c, the primitives, the shim and the libc.  Its functions get their
   specifications from:
   - the libc piece (libc_piece.v: memcpy, memset, memcmp, calloc, the two crypto_memneq), with libc_G;
   - the BLAKE2s piece of the hs_ programs (blake2s_piece5, b2s_piece5.v), with blake2s_G5;
   - the AEAD piece and the Curve25519 piece, as their interfaces aead3b_ok and x25519_ok3c give them;
   - the protocol piece v5 (protocol_piece5, prot_piece5.v: noise.c and the shim), with prot_G5 at the world;
   - the law's own piece: main and the harness's static functions (its copies of the hs_laws.h / hs_unchanged.h
     helpers, whose bodies hs_bodies.v proves once and hc3_lift moves into the law's unit, and its other statics),
     in the unit hs_unit (the world's compspecs, the whole program's varspecs, the harness's Clight).
   Every other function of the program is unreachable from main and gets a vacuous specification
   (asm_assert.asm_harness_safe_gp, which also gives gp_assert / gp_assume their specifications).

   hs_harness_safe is that assembly for any hs_ program; its hypotheses are the law's piece and facts about the
   program checked by computation (hs_lib_found of the eight programs: hs_progs.v). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require WgNoise.proof.blake2s.b2s_piece5 WgNoise.proof.protocol5.prot_piece5.
Require WgNoise.proof.aead.aead_part3b WgNoise.proof.x25519.x25519_part3c.
Require Import WgNoise.proof.harness.consume_response_any.hcr3_xcs.

(* main's postcondition: any (the law is the absence of undefined behaviour, its checks being gp_assert) *)
Definition hs_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

(* the harness unit of a law: the world's compspecs, the whole program's varspecs, the harness's Clight *)
Definition hs_unit (W: compspecs) (p: QP.program function) (prog: Clight.program) : unit_ctx :=
  mk_unit W (QPvarspecs p) prog.

(* main's specification in program p *)
Definition hs_main_spec (p: QP.program function) : ident * funspec := (QP.prog_main p, QPmain_spec_ext' p tt hs_post).

(* the identifiers of the shared pieces' specifications: libc, BLAKE2s, AEAD, Curve25519, protocol *)
Definition hs_lib_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G Noise.CS) ++ map fst blake2s_G5 ++ aead_idents3 ++ x25519_idents3 ++
           map fst (prot_G5 (fun _ _ => nil) (fun _ _ _ _ => nil) (fun _ _ _ _ => None) Noise.CS)) in exact l).

(* the units of the shared pieces with the identifiers each piece proves *)
Definition hs_lib_units : list (unit_ctx * list ident) :=
  [(u_libc, map fst (libc_G Noise.CS)); (u_shim, map fst (libc_G Noise.CS));
   (u_curve25519, map fst (libc_G Noise.CS));
   (u_blake2s, map fst blake2s_G5); (u_noise, map fst blake2s_G5)] ++
  map (fun u => (u, aead_idents3)) aead_units3 ++
  map (fun u => (u, x25519_idents3)) x25519_units3 ++
  [(u_noise, map fst (prot_G5 (fun _ _ => nil) (fun _ _ _ _ => nil) (fun _ _ _ _ => None) Noise.CS));
   (u_shim, map fst (prot_G5 (fun _ _ => nil) (fun _ _ _ _ => nil) (fun _ _ _ _ => None) Noise.CS))].

(* the functions ids of unit u are those of p (same Clight), their local variables complete in u's compspecs *)
Definition hs_unit_found (p: QP.program function) (u: unit_ctx) (ids: list ident) : Prop :=
  forall i f, In i ids -> find_internal (u_prog u) i = Some f ->
    Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) /\
    Forall (fun it => complete_type (@cenv_cs (u_cs u)) (snd it) = true) (fn_vars f).

(* the externals the shared pieces call are p's, and the shared units' functions and global variables are p's
   (checked by computation for each hs_ program: hs_progs.v) *)
Definition hs_lib_found (p: QP.program function) : Prop :=
  forallb (asm_present_ext p) [_quickproof_malloc; _quickproof_free; _nondet_u32; _nondet_bytes] = true /\
  Forall (fun ui => hs_unit_found p (fst ui) (snd ui) /\
                    Forall (fun it => initial_world.find_id (fst it) (QPvarspecs p) = Some (snd it)) (u_V (fst ui)))
    hs_lib_units.

(* the imports a law's piece may use: the externals of the world present in p, the protocol's and the libc's
   specifications *)
Definition hs_import_ok (W: compspecs) (p: QP.program function) (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (ix: ident * funspec) : Prop :=
  (In ix (@env_specs_gp W) /\ asm_present_ext p (fst ix) = true) \/
  In ix (prot_G5 x25519 aead_enc aead_dec W) \/ In ix (libc_G W).

Section Assembly.
Variable p: QP.program function.
Variable OK: QPprogram_OK p.
Variable W: compspecs.
Hypothesis HW: W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK).
Hypothesis CBC: forall H, cenv_built_correctly
                  (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
                  (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Hypothesis EXT: all_unspecified_OK p.
(* the units' compspecs (and CSh) are included in the world: hs_worlds.world_ok_hs_<law> *)
Hypothesis HWS: Forall (fun cs => cspecs_sub cs W) hs_unit_cs.
Hypothesis HLIB: hs_lib_found p.

(* the law: its harness's Clight, the specifications of its static functions other than main (Gl x, with
   identifiers ids_l), its imports Il *)
Variable prog: Clight.program.
Variable Gl: (list byte -> list byte -> list byte) -> funspecs.
Variable ids_l: list ident.
Variable Il: (list byte -> list byte -> list byte) -> (list byte -> Z -> list byte -> list byte -> list byte) ->
             (list byte -> Z -> list byte -> list byte -> option (list byte)) -> compspecs -> funspecs.

Hypothesis HIDS: forall x, map fst (Gl x) = ids_l.
Hypothesis HCC: forall x, cc_default_all (Gl x).
(* the checks of asm_assert on p, the shared identifiers followed by the law's (vm_compute) *)
Hypothesis HCHK: asm_check_gp W p (hs_lib_ids ++ ids_l) = true.
Hypothesis HFUN: hs_unit_found p (hs_unit W p prog) (QP.prog_main p :: ids_l).
Hypothesis HIMP: forall x enc dec, Forall (hs_import_ok W p x enc dec) (Il x enc dec W).
(* the law's piece, for any models of the primitives with the properties the shared pieces prove *)
Hypothesis HPIECE: forall x enc dec,
  x25519_props x -> x25519_clamp_inv x -> x25519_dh_agree x -> aead_props enc dec ->
  piece_ok [hs_unit W p prog] (Il x enc dec) (hs_main_spec p :: Gl x).

Local Notation find_id := initial_world.find_id.

(* the identifiers of the shared pieces, for any models and world *)
Lemma hs_lib_ids_eq x enc dec :
  map fst (libc_G W) ++ map fst blake2s_G5 ++ aead_idents3 ++ x25519_idents3 ++ map fst (prot_G5 x enc dec W) =
  hs_lib_ids.
Proof. vm_compute; reflexivity. Qed.

Lemma hs_present i : In i [_quickproof_malloc; _quickproof_free; _nondet_u32; _nondet_bytes] ->
  asm_present_ext p i = true.
Proof.
  intros H. destruct HLIB as [P _]. rewrite forallb_forall in P. auto.
Qed.

Section Pieces.
Variables (Ga Gx: funspecs) (x: list byte -> list byte -> list byte).
Variables (enc: list byte -> Z -> list byte -> list byte -> list byte)
          (dec: list byte -> Z -> list byte -> list byte -> option (list byte))
          (xenc: list byte -> list byte -> list byte -> list byte -> list byte)
          (xdec: list byte -> list byte -> list byte -> list byte -> option (list byte)).
Hypothesis Hap: aead_props enc dec.
Hypothesis HpA: piece_ok aead_units3 aead_imports3 Ga.
Hypothesis HidA: map fst Ga = aead_idents3.
Hypothesis HcovA: asm_covers Ga (aead_iface3b enc dec xenc xdec).
Hypothesis HccA: cc_default_all Ga.
Hypothesis Hxp: x25519_props x.
Hypothesis HpX: piece_ok x25519_units3 x25519_imports3 Gx.
Hypothesis HidX: map fst Gx = x25519_idents3.
Hypothesis HcovX: asm_covers Gx (x25519_iface3 x).
Hypothesis HccX: cc_default_all Gx.
Hypothesis Hclamp: x25519_clamp_inv x.
Hypothesis Hdh: x25519_dh_agree x.

(* the real specifications, main excepted *)
Definition hs_Gr : funspecs := libc_G W ++ blake2s_G5 ++ Ga ++ Gx ++ prot_G5 x enc dec W ++ Gl x.

Local Notation ids := (hs_lib_ids ++ ids_l).
Local Notation Gw := (@asm_Gall_gp W p hs_post hs_Gr ids).

Lemma hs_IDS : map fst hs_Gr = ids.
Proof.
  unfold hs_Gr. rewrite !map_app, HidA, HidX, HIDS, <- (hs_lib_ids_eq x enc dec), <- !app_assoc. reflexivity.
Qed.

Lemma hs_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_gp_norepet; [apply hs_IDS | apply HCHK]. Qed.

Lemma hs_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_gp_norepet'; [apply hs_IDS | apply HCHK]. Qed.

Lemma hs_find_Gw i s : In (i, s) Gw -> find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [exact H | apply hs_norepet']. Qed.

(* an entry of Gw whose specification is a subtype of the one asked for covers it *)
Lemma hs_cov_entry i s0 s1 : In (i, s0) Gw -> funspec_sub s0 s1 ->
  exists s, find_id i Gw = Some s /\ funspec_sub s s1.
Proof. intros H S. exists s0; split; [apply hs_find_Gw, H | exact S]. Qed.

Lemma hs_in_Gr ix : In ix hs_Gr -> In ix Gw.
Proof. apply asm_Gr_gp_incl. Qed.
Lemma hs_in_libc ix : In ix (libc_G W) -> In ix Gw.
Proof. intros H. apply hs_in_Gr. unfold hs_Gr. apply in_app; auto. Qed.
Lemma hs_in_b2s ix : In ix blake2s_G5 -> In ix Gw.
Proof. intros H. apply hs_in_Gr. unfold hs_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hs_in_aead ix : In ix Ga -> In ix Gw.
Proof. intros H. apply hs_in_Gr. unfold hs_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hs_in_x ix : In ix Gx -> In ix Gw.
Proof. intros H. apply hs_in_Gr. unfold hs_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hs_in_prot ix : In ix (prot_G5 x enc dec W) -> In ix Gw.
Proof. intros H. apply hs_in_Gr. unfold hs_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hs_in_law ix : In ix (Gl x) -> In ix Gw.
Proof. intros H. apply hs_in_Gr. unfold hs_Gr. do 5 (apply in_app; right). auto. Qed.
Lemma hs_in_env i s : In (i, s) (@env_specs_gp W) -> asm_present_ext p i = true -> In (i, s) Gw.
Proof. apply asm_E_gp_incl. Qed.

(* an entry of an abstract piece G (Ga, Gx) covering an interface G0: its specification in Gw *)
Lemma hs_cov_piece (G G0: funspecs) i s0 s1 : incl G hs_Gr -> list_norepet (map fst G) -> asm_covers G G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. unfold asm_covers in COV. rewrite Forall_forall in COV.
  destruct (COV _ Hin) as [s [F S]]; simpl in F.
  exists s; split; [| eapply funspec_sub_trans; eauto].
  apply hs_find_Gw, hs_in_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hs_incl_aead : incl Ga hs_Gr.
Proof. intros a H. unfold hs_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hs_incl_x : incl Gx hs_Gr.
Proof. intros a H. unfold hs_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.

Ltac hs_inl := simpl; repeat first [left; reflexivity | right].

Ltac hs_from_libc sub :=
  eapply hs_cov_entry; [apply hs_in_libc; unfold libc_G; hs_inl | apply sub].
Ltac hs_from_b2s sub :=
  eapply hs_cov_entry; [apply hs_in_b2s; unfold blake2s_G5; hs_inl | apply sub].
Ltac hs_from_aead sub :=
  eapply (hs_cov_piece Ga (aead_iface3b enc dec xenc xdec)); [apply hs_incl_aead | apply HpA | apply HcovA
                                                             | unfold aead_iface3b; hs_inl | apply sub].
Ltac hs_from_x sub :=
  eapply (hs_cov_piece Gx (x25519_iface3 x)); [apply hs_incl_x | apply HpX | apply HcovX
                                              | unfold x25519_iface3; hs_inl | apply sub].
Ltac hs_from_env :=
  eapply hs_cov_entry; [apply hs_in_env; [unfold env_specs_gp, asm_env.env_specs; hs_inl
                                         | apply hs_present; hs_inl] | apply funspec_sub_refl].

(* the imports of the shared pieces *)
Lemma hs_cov_libc_imports cs : asm_covers Gw (libc_imports W cs).
Proof. constructor; [hs_from_env | constructor]. Qed.

Lemma hs_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hs_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
  constructor; [hs_from_libc (@hcr3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hs_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hs_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
  constructor; [hs_from_libc (@hcr3x_memset_sub Libc.CS cs) |].
  constructor; [hs_from_b2s (@hcr3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hs_from_b2s (@hcr3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hs_from_libc (@hcr3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hs_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hs_cov_aead_imports. Qed.

Lemma hs_cov_prot_imports cs : asm_covers Gw (prot_imports5 x enc dec W cs).
Proof.
  unfold prot_imports5, env_specs5. apply asm_covers_app; [| apply asm_covers_app].
  - do 4 (constructor; [hs_from_env |]). constructor.
  - constructor; [hs_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
    constructor; [hs_from_libc (@hcr3x_memset_sub Libc.CS cs) |].
    constructor; [hs_from_libc (@hcr3x_memcmp_sub Libc.CS cs) |].
    constructor; [hs_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
    constructor; [hs_from_b2s (@hcr3x_memzero_explicit_sub Blake2s.CS cs) |].
    constructor; [hs_from_libc (@hcr3x_crypto_memneq_sub Curve25519.CS cs) |].
    constructor; [hs_from_libc (@hcr3x___crypto_memneq_sub Shim.CS cs) |].
    constructor; [hs_from_x (@hcr3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
    constructor; [hs_from_x (@hcr3x_curve25519_sub Curve25519.CS cs x) |].
    constructor; [hs_from_x (@hcr3x_generate_public_sub Curve25519.CS cs x) |].
    constructor; [hs_from_aead (@hcr3x_encrypt_sub Chacha20poly1305.CS cs enc) |].
    constructor; [hs_from_aead (@hcr3x_decrypt3_sub Chacha20poly1305.CS cs dec) | constructor].
  - apply asm_covers_incl; [apply hs_norepet' |]. intros a H. apply hs_in_b2s, H.
Qed.

Lemma hs_cov_law_imports : asm_covers Gw (Il x enc dec W).
Proof.
  unfold asm_covers. specialize (HIMP x enc dec). rewrite Forall_forall in HIMP |- *. intros [i s] Hin.
  destruct (HIMP _ Hin) as [[E P] | [E | E]]; eapply hs_cov_entry; try apply funspec_sub_refl.
  - apply hs_in_env; auto.
  - apply hs_in_prot, E.
  - apply hs_in_libc, E.
Qed.

(* the shared units: their compspecs in the world, their variables and functions p's *)
Lemma hs_lib_unit (Imports: compspecs -> funspecs) u ids ids' :
  In (u, ids) hs_lib_units -> In (u_cs u) hs_unit_cs -> ids' = ids -> asm_covers Gw (Imports (u_cs u)) ->
  asm_unit_ok W p Gw Imports ids' u.
Proof.
  intros Hu Hc -> HI. destruct HLIB as [_ L]. rewrite Forall_forall in L, HWS.
  destruct (L _ Hu) as [F V]. split; [apply HWS, Hc |]. split; [exact V |]. split; [exact HI | exact F].
Qed.

Ltac hs_unit_in := unfold hs_lib_units, aead_units3, x25519_units3; simpl; tauto.
Ltac hs_cs_in := unfold hs_unit_cs; simpl; tauto.

Lemma hs_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hs_norepet.
  - intros a H. apply hs_in_libc, H.
  - repeat apply Forall_cons; try apply Forall_nil;
      (eapply (hs_lib_unit _ _ (map fst (libc_G Noise.CS))); [hs_unit_in | hs_cs_in | reflexivity
                                                             | apply hs_cov_libc_imports]).
Qed.

Lemma hs_bodies_b2s : asm_bodies W p Gw blake2s_G5.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_noise] blake2s_imports3 blake2s_G5 b2s_piece5.blake2s_piece5).
  - apply hs_norepet.
  - intros a H. apply hs_in_b2s, H.
  - repeat apply Forall_cons; try apply Forall_nil;
      (eapply (hs_lib_unit _ _ (map fst blake2s_G5)); [hs_unit_in | hs_cs_in | reflexivity
                                                      | apply hs_cov_b2s_imports]).
Qed.

Lemma hs_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hs_norepet.
  - intros a H. apply hs_in_aead, H.
  - unfold aead_units3. repeat apply Forall_cons; try apply Forall_nil;
      (eapply (hs_lib_unit _ _ aead_idents3); [hs_unit_in | hs_cs_in | exact HidA | apply hs_cov_aead_imports]).
Qed.

Lemma hs_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hs_norepet.
  - intros a H. apply hs_in_x, H.
  - unfold x25519_units3. repeat apply Forall_cons; try apply Forall_nil;
      (eapply (hs_lib_unit _ _ x25519_idents3); [hs_unit_in | hs_cs_in | exact HidX | apply hs_cov_x_imports]).
Qed.

Lemma hs_prot_ids : map fst (prot_G5 x enc dec W) =
  map fst (prot_G5 (fun _ _ => nil) (fun _ _ _ _ => nil) (fun _ _ _ _ => None) Noise.CS).
Proof. vm_compute; reflexivity. Qed.

Lemma hs_bodies_prot : asm_bodies W p Gw (prot_G5 x enc dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_shim] _ _ (prot_piece5.protocol_piece5 x enc dec W Hxp Hap)).
  - apply hs_norepet.
  - intros a H. apply hs_in_prot, H.
  - repeat apply Forall_cons; try apply Forall_nil;
      (eapply (hs_lib_unit _ _ (map fst (prot_G5 (fun _ _ => nil) (fun _ _ _ _ => nil) (fun _ _ _ _ => None) Noise.CS)));
       [hs_unit_in | hs_cs_in | apply hs_prot_ids | apply hs_cov_prot_imports]).
Qed.

(* the varspecs of p, each found in p's varspecs (they are distinct: asm_check_gp) *)
Lemma hs_varspecs_self : Forall (fun it => find_id (fst it) (QPvarspecs p) = Some (snd it)) (QPvarspecs p).
Proof.
  pose proof hs_norepet as LNR. apply list_norepet_append_left in LNR.
  apply Forall_forall. intros [i t] H. apply initial_world.find_id_i; auto.
Qed.

Lemma hs_bodies_law : asm_bodies W p Gw (hs_main_spec p :: Gl x).
Proof.
  apply (asm_piece_lift W p Gw [hs_unit W p prog] (Il x enc dec) _ (HPIECE x enc dec Hxp Hclamp Hdh Hap)).
  - apply hs_norepet.
  - intros a [<-|H]; [left; reflexivity | apply hs_in_law, H].
  - constructor; [| constructor].
    split; [apply cspecs_sub_refl |]. split; [apply hs_varspecs_self |].
    split; [apply hs_cov_law_imports |].
    simpl map. rewrite HIDS. exact HFUN.
Qed.

Lemma hs_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hs_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hs_Gr.
Proof.
  unfold hs_Gr. apply Forall_app; split; [apply hs_cc_dec; vm_compute; reflexivity |].
  apply Forall_app; split; [apply hs_cc_dec; vm_compute; reflexivity |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; [apply hs_cc_dec; vm_compute; reflexivity | apply HCC].
Qed.

Lemma hs_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hs_bodies : asm_bodies W p Gw (hs_main_spec p :: hs_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hs_bodies_law
           (hs_bodies_app _ _ hs_bodies_libc (hs_bodies_app _ _ hs_bodies_b2s
              (hs_bodies_app _ _ hs_bodies_aead (hs_bodies_app _ _ hs_bodies_x hs_bodies_prot))))).
  intros a Ha. unfold hs_Gr in Ha. cbn [app In] in Ha |- *. rewrite !in_app_iff in Ha |- *. tauto.
Qed.

Lemma hs_safe_pieces : harness_safe p.
Proof.
  exact (asm_harness_safe_gp p OK W HW CBC EXT hs_post hs_Gr ids hs_IDS HCHK hs_cc hs_bodies).
Qed.

End Pieces.

Theorem hs_harness_safe : harness_safe p.
Proof.
  destruct aead_part3b.aead_part3b as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HccA).
  destruct x25519_part3c.x25519_part3c as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & Hclamp & Hdh).
  exact (hs_safe_pieces Ga Gx x enc dec xenc xdec Hap HpA HidA HcovA HccA Hxp HpX HidX HcovX HccX Hclamp Hdh).
Qed.

End Assembly.
