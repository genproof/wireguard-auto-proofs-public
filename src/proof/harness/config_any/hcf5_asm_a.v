(* law config_any: the assembly helpers of hcf5_asm.v, a port of handshake_clear's hcl5_asm_a.v: asm_lib's asm_harness_safe in the world
   W_config_any for ANY lower pieces (Gb, Ga, Gx with their models) satisfying the interfaces, from the libc piece,
   the protocol piece v4 (prot4_piece_stmt), the common.h piece v4 (hc4_piece_stmt_config_any) and the law's piece
   (main).  Cross-compspecs funspec_sub lemmas: the base's hci3_xcs.v. *)
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
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci3_xcs.
Require WgNoise.contracts.x_config_any.

Local Notation p := WgNoise.contracts.x_config_any.whole_prog.
Local Notation W := W_config_any.

Lemma hcf5_asm_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hcf5_asm_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hcf5_asm_cs_sub cs : In cs (WgNoise.contracts.x_config_any.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_config_any as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hcf5_asm_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hcf5_asm_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hcf5_asm_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hcf5_asm_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++
           WgNoise.proof.protocol.prot_piece3.protocol_idents3 ++ hc4_ids_config_any) in exact l).

Lemma hcf5_asm_check : asm_check W p hcf5_asm_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hcf5_asm_hc_ids x enc dec : map fst (hc4_G_config_any x enc dec W) = hc4_ids_config_any.
Proof. apply hc4_ids_ok_config_any. Qed.

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
Hypothesis HcovD: asm_covers Ga [@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS aead_dec;
                                 @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xaead_dec].
Hypothesis Hxp: x25519_props x25519.
Hypothesis HpX: piece_ok x25519_units3 x25519_imports3 Gx.
Hypothesis HidX: map fst Gx = x25519_idents3.
Hypothesis HcovX: asm_covers Gx (x25519_iface3 x25519).
Hypothesis HccA: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Ga.
Hypothesis HccX: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Gx.
(* the shared v4 pieces and the law's piece *)
Hypothesis Hprot: prot4_piece_stmt.
Hypothesis Hhc: hc4_piece_stmt_config_any.
Hypothesis HM: piece_ok [u_hcf5] (hcf5_imports x25519) hcf5_G.

Definition hcf5_asm_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++
  (hc4_G_config_any x25519 aead_enc aead_dec W).

Local Notation Gw := (@asm_Gall W p hcf5_post hcf5_asm_Gr hcf5_asm_ids).

Lemma hcf5_asm_protI : map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) =
  WgNoise.proof.protocol.prot_piece3.protocol_idents3.
Proof. exact (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma hcf5_asm_protP : piece_ok [u_noise; u_cookie; u_shim] (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. exact (proj2 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma hcf5_asm_hcP : piece_ok [u_h4_config_any] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (hc4_G_config_any x25519 aead_enc aead_dec W).
Proof. exact (Hhc x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap hcf5_cs4_sub). Qed.

Lemma hcf5_asm_IDS : map fst hcf5_asm_Gr = hcf5_asm_ids.
Proof.
  unfold hcf5_asm_Gr. rewrite !map_app, HidB, HidA, HidX, hcf5_asm_hc_ids, hcf5_asm_protI.
  reflexivity.
Qed.

Lemma hcf5_asm_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hcf5_asm_IDS | apply hcf5_asm_check]. Qed.

Lemma hcf5_asm_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hcf5_asm_IDS | apply hcf5_asm_check]. Qed.

Lemma hcf5_asm_find_Gr i s : In (i, s) hcf5_asm_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hcf5_asm_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma hcf5_asm_covers_lift Gp G0 : incl Gp hcf5_asm_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hcf5_asm_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hcf5_asm_cov1 Gp G0 i s0 s1 : incl Gp hcf5_asm_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hcf5_asm_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hcf5_asm_incl_libc : incl (libc_G W) hcf5_asm_Gr.
Proof. intros a H. unfold hcf5_asm_Gr. apply in_app; auto. Qed.
Lemma hcf5_asm_incl_b2s : incl Gb hcf5_asm_Gr.
Proof. intros a H. unfold hcf5_asm_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hcf5_asm_incl_aead : incl Ga hcf5_asm_Gr.
Proof. intros a H. unfold hcf5_asm_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcf5_asm_incl_x : incl Gx hcf5_asm_Gr.
Proof. intros a H. unfold hcf5_asm_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcf5_asm_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hcf5_asm_Gr.
Proof. intros a H. unfold hcf5_asm_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcf5_asm_incl_hc : incl (hc4_G_config_any x25519 aead_enc aead_dec W) hcf5_asm_Gr.
Proof. intros a H. unfold hcf5_asm_Gr. do 5 (apply in_app; right). auto. Qed.

Lemma hcf5_asm_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hcf5_asm_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hcf5_asm_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hcf5_asm_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hcf5_asm_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hcf5_asm_nr_libc | apply incl_refl]. Qed.

Ltac hcf5_asm_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac hcf5_asm_from_libc sub :=
  eapply (hcf5_asm_cov1 (libc_G W) (libc_G W)); [apply hcf5_asm_incl_libc | apply hcf5_asm_nr_libc | apply hcf5_asm_cov_libc
                                            | unfold libc_G; hcf5_asm_inl | apply sub].
Ltac hcf5_asm_from_b2s sub :=
  eapply (hcf5_asm_cov1 Gb blake2s_G3); [apply hcf5_asm_incl_b2s | apply hcf5_asm_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hcf5_asm_inl | apply sub].
Ltac hcf5_asm_from_aead sub :=
  eapply (hcf5_asm_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hcf5_asm_incl_aead | apply hcf5_asm_nr_aead | apply HcovA | unfold aead_iface3; hcf5_asm_inl | apply sub].
Ltac hcf5_asm_from_dec sub :=
  eapply (hcf5_asm_cov1 Ga); [apply hcf5_asm_incl_aead | apply hcf5_asm_nr_aead | apply HcovD | hcf5_asm_inl | apply sub].
Ltac hcf5_asm_from_x sub :=
  eapply (hcf5_asm_cov1 Gx (x25519_iface3 x25519));
    [apply hcf5_asm_incl_x | apply hcf5_asm_nr_x | apply HcovX | unfold x25519_iface3; hcf5_asm_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma hcf5_asm_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hcf5_asm_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hcf5_asm_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hcf5_asm_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcf5_asm_from_b2s (@hci3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hcf5_asm_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hcf5_asm_cov_aead_imports. Qed.

Lemma hcf5_asm_cov_env_ns : asm_covers Gw (WgNoise.proof.protocol.prot_prog3.env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hcf5_asm_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx;
    repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hcf5_asm_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply hcf5_asm_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma hcf5_asm_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hcf5_asm_covers_lift Gb _ hcf5_asm_incl_b2s hcf5_asm_nr_b2s HcovB). Qed.

Lemma hcf5_asm_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hcf5_asm_norepet' |]. intros a H. apply asm_Gr_incl, hcf5_asm_incl_prot, H. Qed.

Lemma hcf5_asm_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, WgNoise.proof.protocol.prot_prog3.prot_imports3.
  apply asm_covers_app; [apply hcf5_asm_cov_env_ns |].
  apply asm_covers_app; [| apply hcf5_asm_cov_b2sG].
  constructor; [hcf5_asm_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hcf5_asm_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hcf5_asm_from_x (@hci3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hcf5_asm_from_x (@hci3x_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hcf5_asm_from_x (@hci3x_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hcf5_asm_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hcf5_asm_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hcf5_asm_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hcf5_asm_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hcf5_asm_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply hcf5_asm_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hcf5_asm_cov_b2sG |
                           apply asm_covers_app; [apply hcf5_asm_cov_protG | apply hcf5_asm_cov_nondet_size]]].
  constructor; [hcf5_asm_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hcf5_asm_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hcf5_asm_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcf5_asm_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hcf5_asm_from_x (@hci3x_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hcf5_asm_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hcf5_asm_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hcf5_asm_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hcf5_asm_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

(* main's imports: entries of prot_G4 / hc4_G_config_any found by their identifiers *)
Lemma hcf5_asm_cov_find G G0 : incl G hcf5_asm_Gr -> list_norepet (map fst G) ->
  Forall (fun ix => initial_world.find_id (fst ix) G = Some (snd ix)) G0 -> asm_covers Gw G0.
Proof.
  intros INC LNR F. unfold asm_covers. rewrite Forall_forall in *. intros [i s] H.
  specialize (F _ H). simpl in F. exists s; split; [| apply funspec_sub_refl].
  apply hcf5_asm_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hcf5_asm_nr_prot : list_norepet (map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)).
Proof. apply hcf5_asm_protP. Qed.
Lemma hcf5_asm_nr_hc : list_norepet (map fst (hc4_G_config_any x25519 aead_enc aead_dec W)).
Proof. apply hcf5_asm_hcP. Qed.

Lemma hcf5_asm_cov_hcf5_imports : asm_covers Gw (hcf5_imports x25519 W).
Proof.
  unfold hcf5_imports. apply asm_covers_app; [apply hcf5_asm_cov_env_ns |].
  apply asm_covers_app.
  - apply (hcf5_asm_cov_find _ _ hcf5_asm_incl_prot hcf5_asm_nr_prot).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity.
  - cbn [app].
    apply (hcf5_asm_cov_find _ _ hcf5_asm_incl_hc hcf5_asm_nr_hc).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity.
Qed.

Ltac hcf5_asm_unit := split; [apply hcf5_asm_cs_sub; hcf5_asm_in_cs |]; split; [hcf5_asm_varspecs |].

Lemma hcf5_asm_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hcf5_asm_norepet.
  - intros a H. apply asm_Gr_incl, hcf5_asm_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hcf5_asm_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hcf5_asm_unit; split; [apply CI | hcf5_asm_funs] |]); apply Forall_nil.
Qed.

Lemma hcf5_asm_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hcf5_asm_norepet.
  - intros a H. apply asm_Gr_incl, hcf5_asm_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hcf5_asm_unit; split; [apply hcf5_asm_cov_b2s_imports | hcf5_asm_funs] |]); apply Forall_nil.
Qed.

Lemma hcf5_asm_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hcf5_asm_norepet.
  - intros a H. apply asm_Gr_incl, hcf5_asm_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hcf5_asm_unit; split; [apply hcf5_asm_cov_aead_imports | hcf5_asm_funs] |]); apply Forall_nil.
Qed.

Lemma hcf5_asm_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hcf5_asm_norepet.
  - intros a H. apply asm_Gr_incl, hcf5_asm_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hcf5_asm_unit; split; [apply hcf5_asm_cov_x_imports | hcf5_asm_funs] |]); apply Forall_nil.
Qed.

Lemma hcf5_asm_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ hcf5_asm_protP).
  - apply hcf5_asm_norepet.
  - intros a H. apply asm_Gr_incl, hcf5_asm_incl_prot, H.
  - rewrite hcf5_asm_protI.
    repeat (apply Forall_cons; [hcf5_asm_unit; split; [apply hcf5_asm_cov_prot_imports | hcf5_asm_funs] |]); apply Forall_nil.
Qed.

Lemma hcf5_asm_bodies_hc : asm_bodies W p Gw (hc4_G_config_any x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_config_any] _ _ hcf5_asm_hcP).
  - apply hcf5_asm_norepet.
  - intros a H. apply asm_Gr_incl, hcf5_asm_incl_hc, H.
  - rewrite hcf5_asm_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hcf5_asm_cs_sub; left; reflexivity |]. split; [hcf5_asm_varspecs |].
    split; [apply hcf5_asm_cov_hc_imports | hcf5_asm_funs].
Qed.

(* the law's piece (main) *)
Lemma hcf5_asm_bodies_main : asm_bodies W p Gw hcf5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hcf5] (hcf5_imports x25519) hcf5_G HM).
  - apply hcf5_asm_norepet.
  - intros a H. destruct H as [<-|[]]. left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [hcf5_asm_varspecs |].
    split; [apply hcf5_asm_cov_hcf5_imports | hcf5_asm_funs].
Qed.

Lemma hcf5_asm_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hcf5_asm_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hcf5_asm_Gr.
Proof.
  unfold hcf5_asm_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (hci3x_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; apply hcf5_asm_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hcf5_asm_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hcf5_asm_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hcf5_post) :: hcf5_asm_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hcf5_asm_bodies_main
           (hcf5_asm_bodies_app _ _ hcf5_asm_bodies_libc (hcf5_asm_bodies_app _ _ hcf5_asm_bodies_b2s
              (hcf5_asm_bodies_app _ _ hcf5_asm_bodies_aead (hcf5_asm_bodies_app _ _ hcf5_asm_bodies_x
                 (hcf5_asm_bodies_app _ _ hcf5_asm_bodies_prot hcf5_asm_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; left; reflexivity | right; exact H].
Qed.

Lemma hcf5_asm_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_config_any W W_config_any_eq hcf5_asm_cbc hcf5_asm_ext_ok hcf5_post
           hcf5_asm_Gr hcf5_asm_ids hcf5_asm_IDS hcf5_asm_check hcf5_asm_cc hcf5_asm_bodies).
Qed.

End Assembly.
