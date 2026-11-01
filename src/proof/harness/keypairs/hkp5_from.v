(* law keypairs: the assembly, for ANY lower
   pieces satisfying the interfaces, from the libc piece, the protocol piece v4 (prot4_piece_stmt), the common.h
   piece v4 of the keypairs unit (hc4_piece_stmt_keypairs) and the law's own piece (hkp5_piece_stmt: mk_unlink, m_get,
   m_put, rest_same, warn_same, check_all, pick_live, pick_held, main). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.keypairs.hkp5_stmts.
Require WgNoise.contracts.x_keypairs.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
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
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.create_any.ca3_xcs.
Require Import WgNoise.proof.protocol.prot3c_bridge.

(* ---------------------------------------------------------------------- *)
(* The assembly (a port of create_any's ca5_asm.v; the law's piece covers  *)
(* main and the eight harness functions kpf_Gh)                             *)
(* ---------------------------------------------------------------------- *)

Local Notation p := WgNoise.contracts.x_keypairs.whole_prog.
Local Notation W := W_keypairs.

Lemma kpf_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma kpf_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma kpf_cs_sub cs : In cs (WgNoise.contracts.x_keypairs.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_keypairs as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

(* common4's body compspecs are included in the world (hc4_piece_stmt's hypothesis) *)
Lemma kpf_cs4_sub : cspecs_sub WgNoise.proof.harness.common4.hc4_cs.CS4 W.
Proof. rewrite W_keypairs_eq; apply world_cspecs_sub; vm_refl. Qed.

Ltac kpf_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac kpf_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac kpf_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition kpf_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++
           WgNoise.proof.protocol.prot_piece3.protocol_idents3 ++ hc4_ids_keypairs ++
           [KC._mk_unlink; KC._m_get; KC._m_put; KC._rest_same; KC._warn_same; KC._check_all; KC._pick_live;
            KC._pick_held]) in exact l).

Lemma kpf_check : asm_check W p kpf_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma kpf_hc_ids x enc dec : map fst (hc4_G_keypairs x enc dec W) = hc4_ids_keypairs.
Proof. apply hc4_ids_ok_keypairs. Qed.

(* the law's own entries, main excepted *)
Definition kpf_Gh (x25519: list byte -> list byte -> list byte) : funspecs :=
  [hk5_mk_unlink_spec; hk5_m_get_spec; hk5_m_put_spec; hk5_rest_same_spec; hk5_warn_same_spec;
   hk5_check_all_spec x25519; hk5_pick_live_spec; hk5_pick_held_spec].

Section Assembly.
Context (Gb Ga Gx: funspecs).
Context (x25519: list byte -> list byte -> list byte).
Context (aead_enc: list byte -> Z -> list byte -> list byte -> list byte).
Context (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)).
Context (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte).
Context (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte)).
Context (HpB: piece_ok blake2s_units3 blake2s_imports3 Gb).
Context (HidB: map fst Gb = map fst blake2s_G3).
Context (HcovB: asm_covers Gb blake2s_G3).
Context (Hap: aead_props aead_enc aead_dec).
Context (Hxap: xaead_props xaead_enc xaead_dec).
Context (HpA: piece_ok aead_units3 aead_imports3 Ga).
Context (HidA: map fst Ga = aead_idents3).
Context (HcovA: asm_covers Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec)).
Context (HcovD: asm_covers Ga [@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS aead_dec;
                                 @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xaead_dec]).
Context (Hxp: x25519_props x25519).
Context (HpX: piece_ok x25519_units3 x25519_imports3 Gx).
Context (HidX: map fst Gx = x25519_idents3).
Context (HcovX: asm_covers Gx (x25519_iface3 x25519)).
Context (HccA: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Ga).
Context (HccX: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Gx).
(* the shared v4 pieces and the law's piece *)
Context (Hprot: prot4_piece_stmt).
Context (Hhc: hc4_piece_stmt_keypairs).
Context (HM: piece_ok [u_hkp5] (hkp5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) (hkp5_G x25519)).

Definition kpf_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++
  (hc4_G_keypairs x25519 aead_enc aead_dec W) ++ kpf_Gh x25519.

Local Notation Gw := (@asm_Gall W p hkp5_post kpf_Gr kpf_ids).

Lemma kpf_protI : map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) =
  WgNoise.proof.protocol.prot_piece3.protocol_idents3.
Proof. exact (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma kpf_protP : piece_ok [u_noise; u_cookie; u_shim] (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. exact (proj2 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma kpf_hcP : piece_ok [u_h4_keypairs] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (hc4_G_keypairs x25519 aead_enc aead_dec W).
Proof. exact (Hhc x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap kpf_cs4_sub). Qed.

Lemma kpf_IDS : map fst kpf_Gr = kpf_ids.
Proof.
  unfold kpf_Gr. rewrite !map_app, HidB, HidA, HidX, kpf_hc_ids, kpf_protI.
  reflexivity.
Qed.

Lemma kpf_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply kpf_IDS | apply kpf_check]. Qed.

Lemma kpf_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply kpf_IDS | apply kpf_check]. Qed.

Lemma kpf_find_Gr i s : In (i, s) kpf_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply kpf_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma kpf_covers_lift Gp G0 : incl Gp kpf_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply kpf_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma kpf_cov1 Gp G0 i s0 s1 : incl Gp kpf_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := kpf_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma kpf_incl_libc : incl (libc_G W) kpf_Gr.
Proof. intros a H. unfold kpf_Gr. apply in_app; auto. Qed.
Lemma kpf_incl_b2s : incl Gb kpf_Gr.
Proof. intros a H. unfold kpf_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma kpf_incl_aead : incl Ga kpf_Gr.
Proof. intros a H. unfold kpf_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma kpf_incl_x : incl Gx kpf_Gr.
Proof. intros a H. unfold kpf_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma kpf_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) kpf_Gr.
Proof. intros a H. unfold kpf_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma kpf_incl_hc : incl (hc4_G_keypairs x25519 aead_enc aead_dec W) kpf_Gr.
Proof. intros a H. unfold kpf_Gr. do 5 (apply in_app; right). apply in_app; auto. Qed.
Lemma kpf_incl_law : incl (kpf_Gh x25519) kpf_Gr.
Proof. intros a H. unfold kpf_Gr. do 6 (apply in_app; right). exact H. Qed.

Lemma kpf_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma kpf_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma kpf_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma kpf_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma kpf_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply kpf_nr_libc | apply incl_refl]. Qed.

Ltac kpf_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac kpf_from_libc sub :=
  eapply (kpf_cov1 (libc_G W) (libc_G W)); [apply kpf_incl_libc | apply kpf_nr_libc | apply kpf_cov_libc
                                            | unfold libc_G; kpf_inl | apply sub].
Ltac kpf_from_b2s sub :=
  eapply (kpf_cov1 Gb blake2s_G3); [apply kpf_incl_b2s | apply kpf_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; kpf_inl | apply sub].
Ltac kpf_from_aead sub :=
  eapply (kpf_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply kpf_incl_aead | apply kpf_nr_aead | apply HcovA | unfold aead_iface3; kpf_inl | apply sub].
Ltac kpf_from_dec sub :=
  eapply (kpf_cov1 Ga); [apply kpf_incl_aead | apply kpf_nr_aead | apply HcovD | kpf_inl | apply sub].
Ltac kpf_from_x sub :=
  eapply (kpf_cov1 Gx (x25519_iface3 x25519));
    [apply kpf_incl_x | apply kpf_nr_x | apply HcovX | unfold x25519_iface3; kpf_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma kpf_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [kpf_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (@ca3_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma kpf_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [kpf_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (@ca3_memset_sub Libc.CS cs) |].
  constructor; [kpf_from_b2s (@ca3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [kpf_from_b2s (@ca3_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [kpf_from_libc (@ca3_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma kpf_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply kpf_cov_aead_imports. Qed.

Lemma kpf_cov_env_ns : asm_covers Gw (WgNoise.proof.protocol.prot_prog3.env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply kpf_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx;
    repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma kpf_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply kpf_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma kpf_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (kpf_covers_lift Gb _ kpf_incl_b2s kpf_nr_b2s HcovB). Qed.

Lemma kpf_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply kpf_norepet' |]. intros a H. apply asm_Gr_incl, kpf_incl_prot, H. Qed.

Lemma kpf_cov_hcG : asm_covers Gw (hc4_G_keypairs x25519 aead_enc aead_dec W).
Proof. apply asm_covers_incl; [apply kpf_norepet' |]. intros a H. apply asm_Gr_incl, kpf_incl_hc, H. Qed.

Lemma kpf_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, WgNoise.proof.protocol.prot_prog3.prot_imports3.
  apply asm_covers_app; [apply kpf_cov_env_ns |].
  apply asm_covers_app; [| apply kpf_cov_b2sG].
  constructor; [kpf_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (@ca3_memset_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (@ca3_memcmp_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [kpf_from_b2s (@ca3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [kpf_from_libc (@ca3_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [kpf_from_libc (@ca3___crypto_memneq_sub Shim.CS cs) |].
  constructor; [kpf_from_x (@ca3_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [kpf_from_x (@ca3_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [kpf_from_x (@ca3_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [kpf_from_aead (@ca3_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [kpf_from_dec (@ca3_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [kpf_from_aead (@ca3_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [kpf_from_dec (@ca3_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma kpf_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply kpf_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply kpf_cov_b2sG |
                           apply asm_covers_app; [apply kpf_cov_protG | apply kpf_cov_nondet_size]]].
  constructor; [kpf_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (@ca3_memset_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (@ca3_memcmp_sub Libc.CS cs) |].
  constructor; [kpf_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [kpf_from_b2s (@ca3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [kpf_from_libc (@ca3_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [kpf_from_x (@ca3_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [kpf_from_aead (@ca3_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [kpf_from_dec (@ca3_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [kpf_from_aead (@ca3_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [kpf_from_dec (@ca3_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma kpf_cov_hkp5_imports cs : asm_covers Gw (hkp5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec cs).
Proof.
  unfold hkp5_imports. apply asm_covers_app; [exact (kpf_cov_hc_imports cs) | apply kpf_cov_hcG].
Qed.

Ltac kpf_unit := split; [apply kpf_cs_sub; kpf_in_cs |]; split; [kpf_varspecs |].

(* ---------- libc ---------- *)
Lemma kpf_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply kpf_norepet.
  - intros a H. apply asm_Gr_incl, kpf_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply kpf_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [kpf_unit; split; [apply CI | kpf_funs] |]); apply Forall_nil.
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma kpf_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply kpf_norepet.
  - intros a H. apply asm_Gr_incl, kpf_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [kpf_unit; split; [apply kpf_cov_b2s_imports | kpf_funs] |]); apply Forall_nil.
Qed.

(* ---------- AEAD ---------- *)
Lemma kpf_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply kpf_norepet.
  - intros a H. apply asm_Gr_incl, kpf_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [kpf_unit; split; [apply kpf_cov_aead_imports | kpf_funs] |]); apply Forall_nil.
Qed.

(* ---------- x25519 ---------- *)
Lemma kpf_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply kpf_norepet.
  - intros a H. apply asm_Gr_incl, kpf_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [kpf_unit; split; [apply kpf_cov_x_imports | kpf_funs] |]); apply Forall_nil.
Qed.

(* ---------- the protocol piece v4 ---------- *)
Lemma kpf_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ kpf_protP).
  - apply kpf_norepet.
  - intros a H. apply asm_Gr_incl, kpf_incl_prot, H.
  - rewrite kpf_protI.
    repeat (apply Forall_cons; [kpf_unit; split; [apply kpf_cov_prot_imports | kpf_funs] |]); apply Forall_nil.
Qed.

(* ---------- the common.h piece v4 ---------- *)
Lemma kpf_bodies_hc : asm_bodies W p Gw (hc4_G_keypairs x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_keypairs] _ _ kpf_hcP).
  - apply kpf_norepet.
  - intros a H. apply asm_Gr_incl, kpf_incl_hc, H.
  - rewrite kpf_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply kpf_cs_sub; left; reflexivity |]. split; [kpf_varspecs |].
    split; [apply kpf_cov_hc_imports | kpf_funs].
Qed.

(* ---------- the law's piece (main) ---------- *)
Lemma kpf_bodies_main : asm_bodies W p Gw (hkp5_G x25519).
Proof.
  apply (asm_piece_lift W p Gw [u_hkp5] (hkp5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) (hkp5_G x25519) HM).
  - apply kpf_norepet.
  - intros a H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
      [apply asm_Gr_incl, kpf_incl_law; simpl; tauto .. | left; reflexivity].
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [kpf_varspecs |].
    split; [apply kpf_cov_hkp5_imports | kpf_funs].
Qed.

Lemma kpf_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma kpf_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) kpf_Gr.
Proof.
  unfold kpf_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (ca3_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; [apply kpf_cc_dec; vm_compute; reflexivity |].
  apply Forall_app; split; apply kpf_cc_dec; vm_compute; reflexivity.
Qed.

Lemma kpf_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma kpf_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hkp5_post) :: kpf_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ kpf_bodies_main
           (kpf_bodies_app _ _ kpf_bodies_libc (kpf_bodies_app _ _ kpf_bodies_b2s
              (kpf_bodies_app _ _ kpf_bodies_aead (kpf_bodies_app _ _ kpf_bodies_x
                 (kpf_bodies_app _ _ kpf_bodies_prot kpf_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H].
  - left. unfold hkp5_G. do 8 right. left. unfold hkp5_main_spec. reflexivity.
  - unfold kpf_Gr in H. apply in_app_or in H. destruct H as [H|H]; [right; apply in_app; left; exact H|].
    apply in_app_or in H. destruct H as [H|H]; [right; apply in_app; right; apply in_app; left; exact H|].
    apply in_app_or in H. destruct H as [H|H]; [right; do 2 (apply in_app; right); apply in_app; left; exact H|].
    apply in_app_or in H. destruct H as [H|H]; [right; do 3 (apply in_app; right); apply in_app; left; exact H|].
    apply in_app_or in H. destruct H as [H|H]; [right; do 4 (apply in_app; right); apply in_app; left; exact H|].
    apply in_app_or in H. destruct H as [H|H]; [right; do 5 (apply in_app; right); exact H|].
    left. unfold kpf_Gh in H. unfold hkp5_G.
    destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      [left; reflexivity | do 1 right; left; reflexivity | do 2 right; left; reflexivity
      | do 3 right; left; reflexivity | do 4 right; left; reflexivity | do 5 right; left; reflexivity
      | do 6 right; left; reflexivity | do 7 right; left; reflexivity].
Qed.

Lemma kpf_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_keypairs W W_keypairs_eq kpf_cbc kpf_ext_ok hkp5_post
           kpf_Gr kpf_ids kpf_IDS kpf_check kpf_cc kpf_bodies).
Qed.

End Assembly.

Lemma keypairs_from5 :
  prot4_piece_stmt -> hc4_piece_stmt_keypairs -> hkp5_piece_stmt ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_keypairs.whole_prog.
Proof.
  intros Hprot Hhc HM B A X.
  destruct B as (Gb & HpB & HidB & HcovB).
  destruct (prot3c_aead A) as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA).
  destruct (prot3c_x25519 X) as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & _ & _).
  exact (kpf_safe Gb Ga Gx x enc dec xenc xdec HpB HidB HcovB Hap Hxap HpA HidA HcovA HcovD Hxp HpX HidX HcovX
           HccA HccX Hprot Hhc (HM x enc dec xenc xdec Hxp Hap Hxap)).
Qed.
