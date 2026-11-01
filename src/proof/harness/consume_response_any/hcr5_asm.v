(* law consume_response_any: the assembly, for ANY lower pieces (Gb, Ga, Gx with their models)
   satisfying the interfaces, from the libc piece, the protocol piece v4 (protocol_piece4), the common.h piece v4 of
   this unit (statements prot4_piece_stmt / hc4_piece_stmt_consume_response_any of hc4_stmt.v: HYPOTHESES here,
   discharged in the target file by hc4_pieces_final) and
   the law's piece (hcr5_piece). *)
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
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_piece.
Require Import WgNoise.proof.harness.consume_response_any.hcr3_xcs.
Require WgNoise.contracts.x_consume_response_any.

Local Notation p := WgNoise.contracts.x_consume_response_any.whole_prog.
Local Notation W := W_consume_response_any.

Lemma hcr5a_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hcr5a_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hcr5a_cs_sub cs : In cs (WgNoise.contracts.x_consume_response_any.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_consume_response_any as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hcr5a_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hcr5a_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hcr5a_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hcr5a_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++ protocol_idents3 ++
           hc4_ids_consume_response_any) in exact l).

Lemma hcr5a_check : asm_check W p hcr5a_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hcr5a_hc_ids x enc dec : map fst (hc4_G_consume_response_any x enc dec W) = hc4_ids_consume_response_any.
Proof. apply hc4_ids_ok_consume_response_any. Qed.

(* common4's bodies are proved at CS4, a sub-compspecs of the world *)
Lemma hcr5a_cs4 : cspecs_sub CS4 W_consume_response_any.
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
Hypothesis Hrep: hcr5_rep.
(* the shared v4 pieces, as their statements (hc4_stmt.v): protocol_piece4 and common4's
   hc4_piece_consume_response_any *)
Hypothesis Hprot: prot4_piece_stmt.
Hypothesis Hhcs: hc4_piece_stmt_consume_response_any.

Definition hcr5a_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++ (hc4_G_consume_response_any x25519 aead_enc aead_dec W).

Local Notation Gw := (@asm_Gall W p hcr5_post hcr5a_Gr hcr5a_ids).

Lemma hcr5a_IDS : map fst hcr5a_Gr = hcr5a_ids.
Proof.
  unfold hcr5a_Gr. rewrite !map_app, HidB, HidA, HidX, hcr5a_hc_ids.
  rewrite (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)).
  reflexivity.
Qed.

Lemma hcr5a_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hcr5a_IDS | apply hcr5a_check]. Qed.

Lemma hcr5a_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hcr5a_IDS | apply hcr5a_check]. Qed.

Lemma hcr5a_find_Gr i s : In (i, s) hcr5a_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hcr5a_norepet']. apply asm_Gr_incl; auto. Qed.

(* a sub-list Gp of Gr covering G0 makes Gw cover G0 *)
Lemma hcr5a_covers_lift Gp G0 : incl Gp hcr5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hcr5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hcr5a_cov1 Gp G0 i s0 s1 : incl Gp hcr5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hcr5a_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hcr5a_incl_libc : incl (libc_G W) hcr5a_Gr.
Proof. intros a H. unfold hcr5a_Gr. apply in_app; auto. Qed.
Lemma hcr5a_incl_b2s : incl Gb hcr5a_Gr.
Proof. intros a H. unfold hcr5a_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hcr5a_incl_aead : incl Ga hcr5a_Gr.
Proof. intros a H. unfold hcr5a_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcr5a_incl_x : incl Gx hcr5a_Gr.
Proof. intros a H. unfold hcr5a_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcr5a_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hcr5a_Gr.
Proof. intros a H. unfold hcr5a_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hcr5a_incl_hc : incl (hc4_G_consume_response_any x25519 aead_enc aead_dec W) hcr5a_Gr.
Proof. intros a H. unfold hcr5a_Gr. do 5 (apply in_app; right). auto. Qed.

Lemma hcr5a_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hcr5a_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hcr5a_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hcr5a_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hcr5a_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hcr5a_nr_libc | apply incl_refl]. Qed.

Ltac hcr5a_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac hcr5a_from_libc sub :=
  eapply (hcr5a_cov1 (libc_G W) (libc_G W)); [apply hcr5a_incl_libc | apply hcr5a_nr_libc | apply hcr5a_cov_libc
                                            | unfold libc_G; hcr5a_inl | apply sub].
Ltac hcr5a_from_b2s sub :=
  eapply (hcr5a_cov1 Gb blake2s_G3); [apply hcr5a_incl_b2s | apply hcr5a_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hcr5a_inl | apply sub].
Ltac hcr5a_from_aead sub :=
  eapply (hcr5a_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hcr5a_incl_aead | apply hcr5a_nr_aead | apply HcovA | unfold aead_iface3; hcr5a_inl | apply sub].
Ltac hcr5a_from_dec sub :=
  eapply (hcr5a_cov1 Ga); [apply hcr5a_incl_aead | apply hcr5a_nr_aead | apply HcovD | hcr5a_inl | apply sub].
Ltac hcr5a_from_x sub :=
  eapply (hcr5a_cov1 Gx (x25519_iface3 x25519));
    [apply hcr5a_incl_x | apply hcr5a_nr_x | apply HcovX | unfold x25519_iface3; hcr5a_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma hcr5a_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hcr5a_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hcr5a_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hcr5a_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_memset_sub Libc.CS cs) |].
  constructor; [hcr5a_from_b2s (@hcr3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcr5a_from_b2s (@hcr3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hcr5a_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hcr5a_cov_aead_imports. Qed.

(* the environment's functions: all present in this program *)
Lemma hcr5a_cov_env : asm_covers Gw (@asm_env.env_specs W).
Proof.
  apply asm_covers_incl; [apply hcr5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [exact Hx |].
  unfold asm_env.env_specs in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

(* round 3: the protocol / common.h imports take the environment without nondet_size; this law's common.h
   imports (hc_imports3s) add nondet_size back (as rp3_asm) *)
Lemma hcr5a_cov_env_ns : asm_covers Gw (env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hcr5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold env_specs_ns in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hcr5a_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply hcr5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma hcr5a_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hcr5a_covers_lift Gb _ hcr5a_incl_b2s hcr5a_nr_b2s HcovB). Qed.

Lemma hcr5a_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hcr5a_norepet' |]. intros a H. apply asm_Gr_incl, hcr5a_incl_prot, H. Qed.

Lemma hcr5a_cov_hcG : asm_covers Gw (hc4_G_consume_response_any x25519 aead_enc aead_dec W).
Proof. apply asm_covers_incl; [apply hcr5a_norepet' |]. intros a H. apply asm_Gr_incl, hcr5a_incl_hc, H. Qed.

Lemma hcr5a_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, prot_imports3. apply asm_covers_app; [apply hcr5a_cov_env_ns |].
  apply asm_covers_app; [| apply hcr5a_cov_b2sG].
  constructor; [hcr5a_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_memset_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_memcmp_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hcr5a_from_b2s (@hcr3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hcr5a_from_x (@hcr3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hcr5a_from_x (@hcr3x_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hcr5a_from_x (@hcr3x_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hcr5a_from_aead (@hcr3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hcr5a_from_dec (@hcr3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hcr5a_from_aead (@hcr3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hcr5a_from_dec (@hcr3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hcr5a_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply hcr5a_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hcr5a_cov_b2sG |
                           apply asm_covers_app; [apply hcr5a_cov_protG | apply hcr5a_cov_nondet_size]]].
  constructor; [hcr5a_from_libc (@hcr3x_memcpy_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_memset_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_memcmp_sub Libc.CS cs) |].
  constructor; [hcr5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hcr5a_from_b2s (@hcr3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hcr5a_from_libc (@hcr3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hcr5a_from_x (@hcr3x_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hcr5a_from_aead (@hcr3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hcr5a_from_dec (@hcr3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hcr5a_from_aead (@hcr3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hcr5a_from_dec (@hcr3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hcr5a_cov_hcr5_imports cs : asm_covers Gw (hcr5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec cs).
Proof.
  unfold hcr5_imports. apply asm_covers_app; [exact (hcr5a_cov_hc_imports cs) | apply hcr5a_cov_hcG].
Qed.

Ltac hcr5a_unit := split; [apply hcr5a_cs_sub; hcr5a_in_cs |]; split; [hcr5a_varspecs |].

(* ---------- libc ---------- *)
Lemma hcr5a_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hcr5a_norepet.
  - intros a H. apply asm_Gr_incl, hcr5a_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hcr5a_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hcr5a_unit; split; [apply CI | hcr5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma hcr5a_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hcr5a_norepet.
  - intros a H. apply asm_Gr_incl, hcr5a_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hcr5a_unit; split; [apply hcr5a_cov_b2s_imports | hcr5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- AEAD ---------- *)
Lemma hcr5a_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hcr5a_norepet.
  - intros a H. apply asm_Gr_incl, hcr5a_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hcr5a_unit; split; [apply hcr5a_cov_aead_imports | hcr5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- x25519 ---------- *)
Lemma hcr5a_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hcr5a_norepet.
  - intros a H. apply asm_Gr_incl, hcr5a_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hcr5a_unit; split; [apply hcr5a_cov_x_imports | hcr5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- the protocol piece ---------- *)
Lemma hcr5a_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  destruct (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap) as [IDS PK].
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ PK).
  - apply hcr5a_norepet.
  - intros a H. apply asm_Gr_incl, hcr5a_incl_prot, H.
  - rewrite IDS.
    repeat (apply Forall_cons; [hcr5a_unit; split; [apply hcr5a_cov_prot_imports | hcr5a_funs] |]); apply Forall_nil.
Qed.

(* ---------- the common.h piece ---------- *)
Lemma hcr5a_bodies_hc : asm_bodies W p Gw (hc4_G_consume_response_any x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_consume_response_any] _ _
           (Hhcs x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap hcr5a_cs4)).
  - apply hcr5a_norepet.
  - intros a H. apply asm_Gr_incl, hcr5a_incl_hc, H.
  - rewrite hcr5a_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hcr5a_cs_sub; left; reflexivity |]. split; [hcr5a_varspecs |].
    split; [apply hcr5a_cov_hc_imports | hcr5a_funs].
Qed.

(* ---------- the law's piece (main) ---------- *)
Lemma hcr5a_bodies_main : asm_bodies W p Gw hcr5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hcr5] (hcr5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hcr5_G
           (hcr5_piece x25519 aead_enc aead_dec xaead_enc xaead_dec
              (conj Hxp (conj Hap (conj Hxap Hrep))))).
  - apply hcr5a_norepet.
  - intros a H. destruct H as [<-|[]]. left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [hcr5a_varspecs |].
    split; [apply hcr5a_cov_hcr5_imports | hcr5a_funs].
Qed.

Lemma hcr5a_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hcr5a_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hcr5a_Gr.
Proof.
  unfold hcr5a_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (hcr3x_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; apply hcr5a_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hcr5a_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hcr5a_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hcr5_post) :: hcr5a_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hcr5a_bodies_main
           (hcr5a_bodies_app _ _ hcr5a_bodies_libc (hcr5a_bodies_app _ _ hcr5a_bodies_b2s
              (hcr5a_bodies_app _ _ hcr5a_bodies_aead (hcr5a_bodies_app _ _ hcr5a_bodies_x
                 (hcr5a_bodies_app _ _ hcr5a_bodies_prot hcr5a_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; left; reflexivity | right; exact H].
Qed.

Lemma hcr5a_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_consume_response_any W W_consume_response_any_eq hcr5a_cbc hcr5a_ext_ok hcr5_post
           hcr5a_Gr hcr5a_ids hcr5a_IDS hcr5a_check hcr5a_cc hcr5a_bodies).
Qed.

End Assembly.
