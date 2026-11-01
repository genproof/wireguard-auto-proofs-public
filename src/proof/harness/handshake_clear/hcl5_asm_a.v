(* law handshake_clear: the assembly helpers of hcl5_asm.v, a port of create_any's ca5_asm.v / cookie_reply's hcy5_asm.v:
   asm_lib's asm_harness_safe in the world W_handshake_clear for ANY lower pieces (Gb, Ga, Gx with their models)
   satisfying the interfaces, from the libc piece, the protocol piece v4 (prot4_piece_stmt), the common.h piece v4
   (hc4_piece_stmt_handshake_clear) and the law's piece (main).  Cross-compspecs funspec_sub lemmas: the base's
   hci3_xcs.v.  hcl5a_rep_ok: hcl5_rep from prot_rep_lemmas3 (as v1's hci3_rep_ok). *)
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci3_xcs.
Require WgNoise.proof.libc.libc_bytes.
Require WgNoise.contracts.x_handshake_clear.

Local Notation p := WgNoise.contracts.x_handshake_clear.whole_prog.
Local Notation W := W_handshake_clear.

(* prot_rep_lemmas3 gives hcl5_rep (its last conjunct states the keypair's bytes at the world compspecs) *)
Lemma hcl5a_rep_ok : hcl5_rep.
Proof.
  destruct prot_rep_lemmas3 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  repeat (split; [assumption |]).
  intros CSw k K E n h. rewrite (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs Noise.CS CSw).
  apply A8.
Qed.

Lemma hcl5a_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hcl5a_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hcl5a_cs_sub cs : In cs (WgNoise.contracts.x_handshake_clear.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_handshake_clear as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hcl5a_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hcl5a_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hcl5a_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hcl5a_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++
           WgNoise.proof.protocol.prot_piece3.protocol_idents3 ++ hc4_ids_handshake_clear) in exact l).

Lemma hcl5a_check : asm_check W p hcl5a_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hcl5a_hc_ids x enc dec : map fst (hc4_G_handshake_clear x enc dec W) = hc4_ids_handshake_clear.
Proof. apply hc4_ids_ok_handshake_clear. Qed.

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
Hypothesis Hhc: hc4_piece_stmt_handshake_clear.
Hypothesis HM: piece_ok [u_hcl5] (hcl5_imports x25519) hcl5_G.

Definition hcl5a_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++
  (hc4_G_handshake_clear x25519 aead_enc aead_dec W).

Local Notation Gw := (@asm_Gall W p hcl5_post hcl5a_Gr hcl5a_ids).

Lemma hcl5a_protI : map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) =
  WgNoise.proof.protocol.prot_piece3.protocol_idents3.
Proof. exact (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma hcl5a_protP : piece_ok [u_noise; u_cookie; u_shim] (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. exact (proj2 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma hcl5a_hcP : piece_ok [u_h4_handshake_clear] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (hc4_G_handshake_clear x25519 aead_enc aead_dec W).
Proof. exact (Hhc x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap hcl5_cs4_sub). Qed.

Lemma hcl5a_IDS : map fst hcl5a_Gr = hcl5a_ids.
Proof.
  unfold hcl5a_Gr. rewrite !map_app, HidB, HidA, HidX, hcl5a_hc_ids, hcl5a_protI.
  reflexivity.
Qed.

Lemma hcl5a_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hcl5a_IDS | apply hcl5a_check]. Qed.

Lemma hcl5a_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hcl5a_IDS | apply hcl5a_check]. Qed.

Lemma hcl5a_find_Gr i s : In (i, s) hcl5a_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hcl5a_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma hcl5a_covers_lift Gp G0 : incl Gp hcl5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hcl5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hcl5a_cov1 Gp G0 i s0 s1 : incl Gp hcl5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hcl5a_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hcl5a_incl_libc : incl (libc_G W) hcl5a_Gr.
Proof. intros a H. unfold hcl5a_Gr. apply in_app; auto. Qed.
Lemma hcl5a_incl_b2s : incl Gb hcl5a_Gr.
Proof. intros a H. unfold hcl5a_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hcl5a_incl_aead : incl Ga hcl5a_Gr.
Proof. intros a H. unfold hcl5a_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcl5a_incl_x : incl Gx hcl5a_Gr.
Proof. intros a H. unfold hcl5a_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcl5a_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hcl5a_Gr.
Proof. intros a H. unfold hcl5a_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcl5a_incl_hc : incl (hc4_G_handshake_clear x25519 aead_enc aead_dec W) hcl5a_Gr.
Proof. intros a H. unfold hcl5a_Gr. do 5 (apply in_app; right). auto. Qed.

Lemma hcl5a_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hcl5a_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hcl5a_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hcl5a_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hcl5a_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hcl5a_nr_libc | apply incl_refl]. Qed.

Ltac hcl5a_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac hcl5a_from_libc sub :=
  eapply (hcl5a_cov1 (libc_G W) (libc_G W)); [apply hcl5a_incl_libc | apply hcl5a_nr_libc | apply hcl5a_cov_libc
                                            | unfold libc_G; hcl5a_inl | apply sub].
Ltac hcl5a_from_b2s sub :=
  eapply (hcl5a_cov1 Gb blake2s_G3); [apply hcl5a_incl_b2s | apply hcl5a_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hcl5a_inl | apply sub].
Ltac hcl5a_from_aead sub :=
  eapply (hcl5a_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hcl5a_incl_aead | apply hcl5a_nr_aead | apply HcovA | unfold aead_iface3; hcl5a_inl | apply sub].
Ltac hcl5a_from_dec sub :=
  eapply (hcl5a_cov1 Ga); [apply hcl5a_incl_aead | apply hcl5a_nr_aead | apply HcovD | hcl5a_inl | apply sub].
Ltac hcl5a_from_x sub :=
  eapply (hcl5a_cov1 Gx (x25519_iface3 x25519));
    [apply hcl5a_incl_x | apply hcl5a_nr_x | apply HcovX | unfold x25519_iface3; hcl5a_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma hcl5a_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hcl5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hcl5a_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hcl5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hcl5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcl5a_from_b2s (@hci3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hcl5a_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hcl5a_cov_aead_imports. Qed.

Lemma hcl5a_cov_env_ns : asm_covers Gw (WgNoise.proof.protocol.prot_prog3.env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hcl5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx;
    repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hcl5a_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply hcl5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma hcl5a_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hcl5a_covers_lift Gb _ hcl5a_incl_b2s hcl5a_nr_b2s HcovB). Qed.

Lemma hcl5a_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hcl5a_norepet' |]. intros a H. apply asm_Gr_incl, hcl5a_incl_prot, H. Qed.

Lemma hcl5a_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, WgNoise.proof.protocol.prot_prog3.prot_imports3.
  apply asm_covers_app; [apply hcl5a_cov_env_ns |].
  apply asm_covers_app; [| apply hcl5a_cov_b2sG].
  constructor; [hcl5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hcl5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hcl5a_from_x (@hci3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hcl5a_from_x (@hci3x_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hcl5a_from_x (@hci3x_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hcl5a_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hcl5a_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hcl5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hcl5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hcl5a_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply hcl5a_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hcl5a_cov_b2sG |
                           apply asm_covers_app; [apply hcl5a_cov_protG | apply hcl5a_cov_nondet_size]]].
  constructor; [hcl5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hcl5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hcl5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcl5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hcl5a_from_x (@hci3x_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hcl5a_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hcl5a_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hcl5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hcl5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

(* main's imports: entries of prot_G4 / hc4_G_handshake_clear found by their identifiers *)
Lemma hcl5a_cov_find G G0 : incl G hcl5a_Gr -> list_norepet (map fst G) ->
  Forall (fun ix => initial_world.find_id (fst ix) G = Some (snd ix)) G0 -> asm_covers Gw G0.
Proof.
  intros INC LNR F. unfold asm_covers. rewrite Forall_forall in *. intros [i s] H.
  specialize (F _ H). simpl in F. exists s; split; [| apply funspec_sub_refl].
  apply hcl5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hcl5a_nr_prot : list_norepet (map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)).
Proof. apply hcl5a_protP. Qed.
Lemma hcl5a_nr_hc : list_norepet (map fst (hc4_G_handshake_clear x25519 aead_enc aead_dec W)).
Proof. apply hcl5a_hcP. Qed.

Lemma hcl5a_cov_hcl5_imports : asm_covers Gw (hcl5_imports x25519 W).
Proof.
  unfold hcl5_imports. apply asm_covers_app; [apply hcl5a_cov_env_ns |].
  apply asm_covers_app.
  - apply (hcl5a_cov_find _ _ hcl5a_incl_prot hcl5a_nr_prot).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity.
  - apply (hcl5a_cov_find _ _ hcl5a_incl_hc hcl5a_nr_hc).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity.
Qed.

Ltac hcl5a_unit := split; [apply hcl5a_cs_sub; hcl5a_in_cs |]; split; [hcl5a_varspecs |].

Lemma hcl5a_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hcl5a_norepet.
  - intros a H. apply asm_Gr_incl, hcl5a_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hcl5a_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hcl5a_unit; split; [apply CI | hcl5a_funs] |]); apply Forall_nil.
Qed.

Lemma hcl5a_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hcl5a_norepet.
  - intros a H. apply asm_Gr_incl, hcl5a_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hcl5a_unit; split; [apply hcl5a_cov_b2s_imports | hcl5a_funs] |]); apply Forall_nil.
Qed.

Lemma hcl5a_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hcl5a_norepet.
  - intros a H. apply asm_Gr_incl, hcl5a_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hcl5a_unit; split; [apply hcl5a_cov_aead_imports | hcl5a_funs] |]); apply Forall_nil.
Qed.

Lemma hcl5a_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hcl5a_norepet.
  - intros a H. apply asm_Gr_incl, hcl5a_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hcl5a_unit; split; [apply hcl5a_cov_x_imports | hcl5a_funs] |]); apply Forall_nil.
Qed.

Lemma hcl5a_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ hcl5a_protP).
  - apply hcl5a_norepet.
  - intros a H. apply asm_Gr_incl, hcl5a_incl_prot, H.
  - rewrite hcl5a_protI.
    repeat (apply Forall_cons; [hcl5a_unit; split; [apply hcl5a_cov_prot_imports | hcl5a_funs] |]); apply Forall_nil.
Qed.

Lemma hcl5a_bodies_hc : asm_bodies W p Gw (hc4_G_handshake_clear x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_handshake_clear] _ _ hcl5a_hcP).
  - apply hcl5a_norepet.
  - intros a H. apply asm_Gr_incl, hcl5a_incl_hc, H.
  - rewrite hcl5a_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hcl5a_cs_sub; left; reflexivity |]. split; [hcl5a_varspecs |].
    split; [apply hcl5a_cov_hc_imports | hcl5a_funs].
Qed.

(* the law's piece (main) *)
Lemma hcl5a_bodies_main : asm_bodies W p Gw hcl5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hcl5] (hcl5_imports x25519) hcl5_G HM).
  - apply hcl5a_norepet.
  - intros a H. destruct H as [<-|[]]. left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [hcl5a_varspecs |].
    split; [apply hcl5a_cov_hcl5_imports | hcl5a_funs].
Qed.

Lemma hcl5a_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hcl5a_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hcl5a_Gr.
Proof.
  unfold hcl5a_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (hci3x_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; apply hcl5a_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hcl5a_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hcl5a_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hcl5_post) :: hcl5a_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hcl5a_bodies_main
           (hcl5a_bodies_app _ _ hcl5a_bodies_libc (hcl5a_bodies_app _ _ hcl5a_bodies_b2s
              (hcl5a_bodies_app _ _ hcl5a_bodies_aead (hcl5a_bodies_app _ _ hcl5a_bodies_x
                 (hcl5a_bodies_app _ _ hcl5a_bodies_prot hcl5a_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; left; reflexivity | right; exact H].
Qed.

Lemma hcl5a_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_handshake_clear W W_handshake_clear_eq hcl5a_cbc hcl5a_ext_ok hcl5_post
           hcl5a_Gr hcl5a_ids hcl5a_IDS hcl5a_check hcl5a_cc hcl5a_bodies).
Qed.

End Assembly.
