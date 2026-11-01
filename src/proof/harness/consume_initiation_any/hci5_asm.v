(* law consume_initiation_any: the assembly, port of
   consume_response_any's hcr5_asm.v: asm_lib's asm_harness_safe in the world W_consume_initiation_any for ANY lower
   pieces satisfying the interfaces, from the libc piece, the shared v4 pieces as their STATEMENTS (hc4_stmt.v:
   prot4_piece_stmt, hc4_piece_stmt_consume_initiation_any) and the law's piece hci5_piece (main and the harness's
   own ts_step, the extra entry of the spec list). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot_piece3.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_ts.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_piece.
Require Import WgNoise.proof.harness.consume_initiation_any.hci3_xcs.
Require WgNoise.contracts.x_consume_initiation_any.

Local Notation p := WgNoise.contracts.x_consume_initiation_any.whole_prog.
Local Notation W := W_consume_initiation_any.

Lemma hci5a_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hci5a_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hci5a_cs_sub cs : In cs (WgNoise.contracts.x_consume_initiation_any.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_consume_initiation_any as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hci5a_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hci5a_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hci5a_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hci5a_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++ protocol_idents3 ++
           hc4_ids_consume_initiation_any ++ [WgNoise.harness.x_consume_initiation_any.code._ts_step]) in exact l).

Lemma hci5a_check : asm_check W p hci5a_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hci5a_hc_ids x enc dec : map fst (hc4_G_consume_initiation_any x enc dec W) = hc4_ids_consume_initiation_any.
Proof. apply hc4_ids_ok_consume_initiation_any. Qed.

(* common4's bodies are proved at CS4, a sub-compspecs of the world *)
Lemma hci5a_cs4 : cspecs_sub CS4 W_consume_initiation_any.
Proof.
  split3; intros ?i; apply sub_option_get; apply Forall_forall; intros ?x ?Hx; vm_compute in Hx;
  repeat destruct Hx as [<-|Hx]; try contradiction; vm_compute; reflexivity.
Qed.

Section Assembly.
Variables (Gb Ga Gx: funspecs).
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis HpB: piece_ok blake2s_units3 blake2s_imports3 Gb.
Hypothesis HidB: map fst Gb = map fst blake2s_G3.
Hypothesis HcovB: asm_covers Gb blake2s_G3.
Hypothesis Hap: aead_props aead_enc aead_dec.
Hypothesis Hxap: xaead_props xaead_enc xaead_dec.
Hypothesis HpA: piece_ok aead_units3 aead_imports3 Ga.
Hypothesis HidA: map fst Ga = aead_idents3.
Hypothesis HcovA: asm_covers Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec).
(* the NULL-tolerant decrypt templates the protocol imports (prot_dec3): NOT in aead_iface3 *)
Hypothesis HcovD: asm_covers Ga [@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS aead_dec;
                                 @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xaead_dec].
Hypothesis Hxp: x25519_props x25519.
Hypothesis HpX: piece_ok x25519_units3 x25519_imports3 Gx.
Hypothesis HidX: map fst Gx = x25519_idents3.
Hypothesis HcovX: asm_covers Gx (x25519_iface3 x25519).
(* the calling conventions of the abstract pieces' internal entries: NOT derivable from aead3_ok / x25519_ok3 *)
Hypothesis HccA: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Ga.
Hypothesis HccX: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Gx.
(* prot_rep_lemmas3's statement *)
Hypothesis Hrep: hci5_rep.
(* the shared v4 pieces, as their statements (hc4_stmt.v): protocol_piece4 and common4's
   hc4_piece_consume_initiation_any *)
Hypothesis Hprot: prot4_piece_stmt.
Hypothesis Hhcs: hc4_piece_stmt_consume_initiation_any.

Definition hci5a_Gr0 : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++ (hc4_G_consume_initiation_any x25519 aead_enc aead_dec W).
(* the harness's own ts_step (the law's piece proves it with main) *)
Definition hci5a_Gr : funspecs := hci5a_Gr0 ++ [hci5_ts_step_spec].

Local Notation Gw := (@asm_Gall W p hci5_post hci5a_Gr hci5a_ids).

Lemma hci5a_IDS : map fst hci5a_Gr = hci5a_ids.
Proof.
  unfold hci5a_Gr, hci5a_Gr0. rewrite !map_app, HidB, HidA, HidX, hci5a_hc_ids.
  rewrite (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)).
  reflexivity.
Qed.

Lemma hci5a_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hci5a_IDS | apply hci5a_check]. Qed.

Lemma hci5a_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hci5a_IDS | apply hci5a_check]. Qed.

Lemma hci5a_find_Gr i s : In (i, s) hci5a_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hci5a_norepet']. apply asm_Gr_incl; auto. Qed.

(* a sub-list Gp of Gr covering G0 makes Gw cover G0 *)
Lemma hci5a_covers_lift Gp G0 : incl Gp hci5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hci5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hci5a_cov1 Gp G0 i s0 s1 : incl Gp hci5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hci5a_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hci5a_incl_libc : incl (libc_G W) hci5a_Gr.
Proof. intros a H. unfold hci5a_Gr. apply in_or_app; left. unfold hci5a_Gr0. apply in_app; auto. Qed.
Lemma hci5a_incl_b2s : incl Gb hci5a_Gr.
Proof. intros a H. unfold hci5a_Gr. apply in_or_app; left. unfold hci5a_Gr0. apply in_app; right; apply in_app; auto. Qed.
Lemma hci5a_incl_aead : incl Ga hci5a_Gr.
Proof. intros a H. unfold hci5a_Gr. apply in_or_app; left. unfold hci5a_Gr0. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hci5a_incl_x : incl Gx hci5a_Gr.
Proof. intros a H. unfold hci5a_Gr. apply in_or_app; left. unfold hci5a_Gr0. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hci5a_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hci5a_Gr.
Proof. intros a H. unfold hci5a_Gr. apply in_or_app; left. unfold hci5a_Gr0. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hci5a_incl_hc : incl (hc4_G_consume_initiation_any x25519 aead_enc aead_dec W) hci5a_Gr.
Proof. intros a H. unfold hci5a_Gr. apply in_or_app; left. unfold hci5a_Gr0. do 5 (apply in_app; right). auto. Qed.

Lemma hci5a_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hci5a_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hci5a_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hci5a_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hci5a_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hci5a_nr_libc | apply incl_refl]. Qed.

Ltac hci5a_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac hci5a_from_libc sub :=
  eapply (hci5a_cov1 (libc_G W) (libc_G W)); [apply hci5a_incl_libc | apply hci5a_nr_libc | apply hci5a_cov_libc
                                            | unfold libc_G; hci5a_inl | apply sub].
Ltac hci5a_from_b2s sub :=
  eapply (hci5a_cov1 Gb blake2s_G3); [apply hci5a_incl_b2s | apply hci5a_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hci5a_inl | apply sub].
Ltac hci5a_from_aead sub :=
  eapply (hci5a_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hci5a_incl_aead | apply hci5a_nr_aead | apply HcovA | unfold aead_iface3; hci5a_inl | apply sub].
Ltac hci5a_from_dec sub :=
  eapply (hci5a_cov1 Ga); [apply hci5a_incl_aead | apply hci5a_nr_aead | apply HcovD | hci5a_inl | apply sub].
Ltac hci5a_from_x sub :=
  eapply (hci5a_cov1 Gx (x25519_iface3 x25519));
    [apply hci5a_incl_x | apply hci5a_nr_x | apply HcovX | unfold x25519_iface3; hci5a_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma hci5a_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hci5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hci5a_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hci5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hci5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hci5a_from_b2s (@hci3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hci5a_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hci5a_cov_aead_imports. Qed.

(* the environment's functions: all present in this program *)
Lemma hci5a_cov_env : asm_covers Gw (@asm_env.env_specs W).
Proof.
  apply asm_covers_incl; [apply hci5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [exact Hx |].
  unfold asm_env.env_specs in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

(* round 3: the protocol / common.h imports take the environment without nondet_size; this law's common.h
   imports (hc_imports3s) add nondet_size back (as rp3_asm) *)
Lemma hci5a_cov_env_ns : asm_covers Gw (env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hci5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold env_specs_ns in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hci5a_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply hci5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma hci5a_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hci5a_covers_lift Gb _ hci5a_incl_b2s hci5a_nr_b2s HcovB). Qed.

Lemma hci5a_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hci5a_norepet' |]. intros a H. apply asm_Gr_incl, hci5a_incl_prot, H. Qed.

Lemma hci5a_cov_hcG : asm_covers Gw (hc4_G_consume_initiation_any x25519 aead_enc aead_dec W).
Proof. apply asm_covers_incl; [apply hci5a_norepet' |]. intros a H. apply asm_Gr_incl, hci5a_incl_hc, H. Qed.

Lemma hci5a_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, prot_imports3. apply asm_covers_app; [apply hci5a_cov_env_ns |].
  apply asm_covers_app; [| apply hci5a_cov_b2sG].
  constructor; [hci5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hci5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hci5a_from_x (@hci3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hci5a_from_x (@hci3x_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hci5a_from_x (@hci3x_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hci5a_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hci5a_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hci5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hci5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hci5a_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply hci5a_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hci5a_cov_b2sG |
                           apply asm_covers_app; [apply hci5a_cov_protG | apply hci5a_cov_nondet_size]]].
  constructor; [hci5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hci5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hci5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hci5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hci5a_from_x (@hci3x_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hci5a_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hci5a_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hci5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hci5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

(* main's imports: entries of prot_G4 / hc4_G_consume_initiation_any found by their identifiers *)
Lemma hci5a_cov_find G G0 : incl G hci5a_Gr -> list_norepet (map fst G) ->
  Forall (fun ix => initial_world.find_id (fst ix) G = Some (snd ix)) G0 -> asm_covers Gw G0.
Proof.
  intros INC LNR F. unfold asm_covers. rewrite Forall_forall in *. intros [i s] H.
  specialize (F _ H). simpl in F. exists s; split; [| apply funspec_sub_refl].
  apply hci5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hci5a_nr_prot : list_norepet (map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)).
Proof. apply (proj2 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.
Lemma hci5a_nr_hc : list_norepet (map fst (hc4_G_consume_initiation_any x25519 aead_enc aead_dec W)).
Proof. apply (Hhcs x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap hci5a_cs4). Qed.

Lemma hci5a_cov_hci5_imports cs : asm_covers Gw (hci5_imports x25519 aead_enc aead_dec cs).
Proof.
  unfold hci5_imports. apply asm_covers_app; [apply hci5a_cov_env_ns |].
  apply asm_covers_app; [apply hci5a_cov_nondet_size |].
  apply asm_covers_app.
  - apply (hci5a_cov_find _ _ hci5a_incl_prot hci5a_nr_prot).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity.
  - apply asm_covers_app; apply (hci5a_cov_find _ _ hci5a_incl_hc hci5a_nr_hc);
      repeat apply Forall_cons; try apply Forall_nil; reflexivity.
Qed.

Ltac hci5a_unit := split; [apply hci5a_cs_sub; hci5a_in_cs |]; split; [hci5a_varspecs |].

(* ---------- libc ---------- *)
Lemma hci5a_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hci5a_norepet.
  - intros a H. apply asm_Gr_incl, hci5a_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hci5a_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hci5a_unit; split; [apply CI | hci5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma hci5a_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hci5a_norepet.
  - intros a H. apply asm_Gr_incl, hci5a_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hci5a_unit; split; [apply hci5a_cov_b2s_imports | hci5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- AEAD ---------- *)
Lemma hci5a_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hci5a_norepet.
  - intros a H. apply asm_Gr_incl, hci5a_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hci5a_unit; split; [apply hci5a_cov_aead_imports | hci5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- x25519 ---------- *)
Lemma hci5a_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hci5a_norepet.
  - intros a H. apply asm_Gr_incl, hci5a_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hci5a_unit; split; [apply hci5a_cov_x_imports | hci5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- the protocol piece ---------- *)
Lemma hci5a_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  destruct (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap) as [IDS PK].
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ PK).
  - apply hci5a_norepet.
  - intros a H. apply asm_Gr_incl, hci5a_incl_prot, H.
  - rewrite IDS.
    repeat (apply Forall_cons; [hci5a_unit; split; [apply hci5a_cov_prot_imports | hci5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- the common.h piece ---------- *)
Lemma hci5a_bodies_hc : asm_bodies W p Gw (hc4_G_consume_initiation_any x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_consume_initiation_any] _ _
           (Hhcs x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap hci5a_cs4)).
  - apply hci5a_norepet.
  - intros a H. apply asm_Gr_incl, hci5a_incl_hc, H.
  - rewrite hci5a_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hci5a_cs_sub; left; reflexivity |]. split; [hci5a_varspecs |].
    split; [apply hci5a_cov_hc_imports | hci5a_funs].
Qed.

(* ---------- the law's piece (main) ---------- *)
Lemma hci5a_bodies_main : asm_bodies W p Gw hci5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hci5] (hci5_imports x25519 aead_enc aead_dec) hci5_G
           (hci5_piece x25519 aead_enc aead_dec xaead_enc xaead_dec
              (conj Hxp (conj Hap (conj Hxap Hrep))))).
  - apply hci5a_norepet.
  - intros a H. destruct H as [<-|[<-|[]]].
    + apply asm_Gr_incl. unfold hci5a_Gr. apply in_or_app; right; left; reflexivity.
    + left; reflexivity.
  - repeat (apply Forall_cons; [split; [apply cspecs_sub_refl |]; split; [hci5a_varspecs |];
                                split; [apply hci5a_cov_hci5_imports | hci5a_funs] |]); apply Forall_nil.
Qed.

Lemma hci5a_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hci5a_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hci5a_Gr.
Proof.
  unfold hci5a_Gr. apply Forall_app; split; [| apply hci5a_cc_dec; vm_compute; reflexivity].
  unfold hci5a_Gr0. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (hci3x_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; apply hci5a_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hci5a_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hci5a_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hci5_post) :: hci5a_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hci5a_bodies_main
           (hci5a_bodies_app _ _ hci5a_bodies_libc (hci5a_bodies_app _ _ hci5a_bodies_b2s
              (hci5a_bodies_app _ _ hci5a_bodies_aead (hci5a_bodies_app _ _ hci5a_bodies_x
                 (hci5a_bodies_app _ _ hci5a_bodies_prot hci5a_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; right; left; reflexivity |].
  unfold hci5a_Gr in H. apply in_app_or in H. destruct H as [H|[<-|[]]]; [right; exact H | left; left; reflexivity].
Qed.

Lemma hci5a_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_consume_initiation_any W W_consume_initiation_any_eq hci5a_cbc hci5a_ext_ok hci5_post
           hci5a_Gr hci5a_ids hci5a_IDS hci5a_check hci5a_cc hci5a_bodies).
Qed.

End Assembly.
