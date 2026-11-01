(* law cookie_mac: the assembly, for ANY lower
   pieces (Gb, Ga, Gx with their models) satisfying the interfaces, from the libc piece, the protocol piece v4
   (protocol_piece4's statement, a hypothesis), the common.h piece of this unit (common4's hc4 piece, a hypothesis)
   and the law's piece (a hypothesis: hck5_piece.v proves it). (+ the base's ck3_xcs.v,
   reusable); law cookie_reply's hcy5_asm.v has the same statement. *)
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
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require WgNoise.proof.protocol.prot_piece3.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require WgNoise.contracts.x_cookie_mac.

Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot_piece3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.cookie_mac.ck3_xcs.

Local Notation p := WgNoise.contracts.x_cookie_mac.whole_prog.
Local Notation W := W_cookie_mac.

Lemma hck5a_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hck5a_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hck5a_cs_sub cs : In cs (WgNoise.contracts.x_cookie_mac.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_cookie_mac as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hck5a_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hck5a_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hck5a_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hck5a_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++ protocol_idents3 ++
           hc4_ids_cookie_mac ++ [WgNoise.harness.x_cookie_mac.code._m_cookie;
                                    WgNoise.harness.x_cookie_mac.code._m_expired]) in exact l).

Lemma hck5a_check : asm_check W p hck5a_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hck5a_hc_ids x enc dec : map fst (hc4_G_cookie_mac x enc dec W) = hc4_ids_cookie_mac.
Proof. apply hc4_ids_ok_cookie_mac. Qed.

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
(* the protocol piece v4 at the world compspecs *)
Context (HprotI: map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) = protocol_idents3).
Context (HprotP: piece_ok [u_noise; u_cookie; u_shim] (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)
                   (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)).
(* the common.h piece v4 of this unit *)
Context (Hhc: piece_ok [u_h4_cookie_mac] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
                (hc4_G_cookie_mac x25519 aead_enc aead_dec W)).
(* the law's piece *)
Context (HPIECE: piece_ok [u_hck5] (hck5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hck5_G).

Definition hck5a_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++
  (hc4_G_cookie_mac x25519 aead_enc aead_dec W) ++ [hck5_m_cookie_spec; hck5_m_expired_spec].

Local Notation Gw := (@asm_Gall W p hck5_post hck5a_Gr hck5a_ids).

Lemma hck5a_IDS : map fst hck5a_Gr = hck5a_ids.
Proof.
  unfold hck5a_Gr. rewrite !map_app, HidB, HidA, HidX, hck5a_hc_ids, HprotI.
  reflexivity.
Qed.

Lemma hck5a_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hck5a_IDS | apply hck5a_check]. Qed.

Lemma hck5a_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hck5a_IDS | apply hck5a_check]. Qed.

Lemma hck5a_find_Gr i s : In (i, s) hck5a_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hck5a_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma hck5a_covers_lift Gp G0 : incl Gp hck5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hck5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hck5a_cov1 Gp G0 i s0 s1 : incl Gp hck5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hck5a_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hck5a_incl_libc : incl (libc_G W) hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. apply in_app; auto. Qed.
Lemma hck5a_incl_b2s : incl Gb hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hck5a_incl_aead : incl Ga hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hck5a_incl_x : incl Gx hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hck5a_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hck5a_incl_hc : incl (hc4_G_cookie_mac x25519 aead_enc aead_dec W) hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. do 5 (apply in_app; right). apply in_app; auto. Qed.
Lemma hck5a_incl_loc : incl [hck5_m_cookie_spec; hck5_m_expired_spec] hck5a_Gr.
Proof. intros a H. unfold hck5a_Gr. do 6 (apply in_app; right). auto. Qed.

Lemma hck5a_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hck5a_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hck5a_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hck5a_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hck5a_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hck5a_nr_libc | apply incl_refl]. Qed.

Ltac hck5a_inl := simpl; repeat first [left; reflexivity | right].

Ltac hck5a_from_libc sub :=
  eapply (hck5a_cov1 (libc_G W) (libc_G W)); [apply hck5a_incl_libc | apply hck5a_nr_libc | apply hck5a_cov_libc
                                            | unfold libc_G; hck5a_inl | apply sub].
Ltac hck5a_from_b2s sub :=
  eapply (hck5a_cov1 Gb blake2s_G3); [apply hck5a_incl_b2s | apply hck5a_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hck5a_inl | apply sub].
Ltac hck5a_from_aead sub :=
  eapply (hck5a_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hck5a_incl_aead | apply hck5a_nr_aead | apply HcovA | unfold aead_iface3; hck5a_inl | apply sub].
Ltac hck5a_from_dec sub :=
  eapply (hck5a_cov1 Ga); [apply hck5a_incl_aead | apply hck5a_nr_aead | apply HcovD | hck5a_inl | apply sub].
Ltac hck5a_from_x sub :=
  eapply (hck5a_cov1 Gx (x25519_iface3 x25519));
    [apply hck5a_incl_x | apply hck5a_nr_x | apply HcovX | unfold x25519_iface3; hck5a_inl | apply sub].

Lemma hck5a_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hck5a_from_libc (@ck3_memcpy_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hck5a_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hck5a_from_libc (@ck3_memcpy_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_memset_sub Libc.CS cs) |].
  constructor; [hck5a_from_b2s (@ck3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hck5a_from_b2s (@ck3_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hck5a_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hck5a_cov_aead_imports. Qed.

Lemma hck5a_cov_env_ns : asm_covers Gw (env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hck5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold env_specs_ns in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hck5a_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply hck5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma hck5a_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hck5a_covers_lift Gb _ hck5a_incl_b2s hck5a_nr_b2s HcovB). Qed.

Lemma hck5a_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hck5a_norepet' |]. intros a H. apply asm_Gr_incl, hck5a_incl_prot, H. Qed.

Lemma hck5a_cov_hcG : asm_covers Gw (hc4_G_cookie_mac x25519 aead_enc aead_dec W).
Proof. apply asm_covers_incl; [apply hck5a_norepet' |]. intros a H. apply asm_Gr_incl, hck5a_incl_hc, H. Qed.

Lemma hck5a_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, prot_imports3. apply asm_covers_app; [apply hck5a_cov_env_ns |].
  apply asm_covers_app; [| apply hck5a_cov_b2sG].
  constructor; [hck5a_from_libc (@ck3_memcpy_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_memset_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_memcmp_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hck5a_from_b2s (@ck3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hck5a_from_libc (@ck3___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hck5a_from_x (@ck3_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hck5a_from_x (@ck3_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hck5a_from_x (@ck3_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hck5a_from_aead (@ck3_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hck5a_from_dec (@ck3_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hck5a_from_aead (@ck3_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hck5a_from_dec (@ck3_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hck5a_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply hck5a_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hck5a_cov_b2sG |
                           apply asm_covers_app; [apply hck5a_cov_protG | apply hck5a_cov_nondet_size]]].
  constructor; [hck5a_from_libc (@ck3_memcpy_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_memset_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_memcmp_sub Libc.CS cs) |].
  constructor; [hck5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hck5a_from_b2s (@ck3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hck5a_from_libc (@ck3_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hck5a_from_x (@ck3_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hck5a_from_aead (@ck3_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hck5a_from_dec (@ck3_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hck5a_from_aead (@ck3_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hck5a_from_dec (@ck3_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hck5a_cov_hck5_imports cs : asm_covers Gw (hck5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec cs).
Proof.
  unfold hck5_imports. apply asm_covers_app; [exact (hck5a_cov_hc_imports cs) | apply hck5a_cov_hcG].
Qed.

Ltac hck5a_unit := split; [apply hck5a_cs_sub; hck5a_in_cs |]; split; [hck5a_varspecs |].

Lemma hck5a_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hck5a_norepet.
  - intros a H. apply asm_Gr_incl, hck5a_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hck5a_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hck5a_unit; split; [apply CI | hck5a_funs] |]); apply Forall_nil.
Qed.

Lemma hck5a_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hck5a_norepet.
  - intros a H. apply asm_Gr_incl, hck5a_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hck5a_unit; split; [apply hck5a_cov_b2s_imports | hck5a_funs] |]); apply Forall_nil.
Qed.

Lemma hck5a_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hck5a_norepet.
  - intros a H. apply asm_Gr_incl, hck5a_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hck5a_unit; split; [apply hck5a_cov_aead_imports | hck5a_funs] |]); apply Forall_nil.
Qed.

Lemma hck5a_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hck5a_norepet.
  - intros a H. apply asm_Gr_incl, hck5a_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hck5a_unit; split; [apply hck5a_cov_x_imports | hck5a_funs] |]); apply Forall_nil.
Qed.

Lemma hck5a_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ HprotP).
  - apply hck5a_norepet.
  - intros a H. apply asm_Gr_incl, hck5a_incl_prot, H.
  - rewrite HprotI.
    repeat (apply Forall_cons; [hck5a_unit; split; [apply hck5a_cov_prot_imports | hck5a_funs] |]); apply Forall_nil.
Qed.

Lemma hck5a_bodies_hc : asm_bodies W p Gw (hc4_G_cookie_mac x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_cookie_mac] _ _ Hhc).
  - apply hck5a_norepet.
  - intros a H. apply asm_Gr_incl, hck5a_incl_hc, H.
  - rewrite hck5a_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hck5a_cs_sub; left; reflexivity |]. split; [hck5a_varspecs |].
    split; [apply hck5a_cov_hc_imports | hck5a_funs].
Qed.

Lemma hck5a_bodies_main : asm_bodies W p Gw hck5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hck5] (hck5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hck5_G HPIECE).
  - apply hck5a_norepet.
  - intros a H. destruct H as [<-|[<-|[<-|[]]]].
    + apply asm_Gr_incl, hck5a_incl_loc. left; reflexivity.
    + apply asm_Gr_incl, hck5a_incl_loc. right; left; reflexivity.
    + left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [hck5a_varspecs |].
    split; [apply hck5a_cov_hck5_imports | hck5a_funs].
Qed.

Lemma hck5a_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hck5a_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hck5a_Gr.
Proof.
  unfold hck5a_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (ck3_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; [apply hck5a_cc_dec; vm_compute; reflexivity |].
  apply Forall_app; split; apply hck5a_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hck5a_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hck5a_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hck5_post) :: hck5a_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hck5a_bodies_main
           (hck5a_bodies_app _ _ hck5a_bodies_libc (hck5a_bodies_app _ _ hck5a_bodies_b2s
              (hck5a_bodies_app _ _ hck5a_bodies_aead (hck5a_bodies_app _ _ hck5a_bodies_x
                 (hck5a_bodies_app _ _ hck5a_bodies_prot hck5a_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H].
  - left. right; right; left; reflexivity.
  - unfold hck5a_Gr in H. rewrite !in_app_iff in H.
    destruct H as [H|[H|[H|[H|[H|[H|H]]]]]].
    + right. apply in_app; left; exact H.
    + right. apply in_app; right; apply in_app; left; exact H.
    + right. do 2 (apply in_app; right); apply in_app; left; exact H.
    + right. do 3 (apply in_app; right); apply in_app; left; exact H.
    + right. do 4 (apply in_app; right); apply in_app; left; exact H.
    + right. do 5 (apply in_app; right); exact H.
    + left. destruct H as [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity].
Qed.

Lemma hck5a_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_cookie_mac W W_cookie_mac_eq hck5a_cbc hck5a_ext_ok hck5_post
           hck5a_Gr hck5a_ids hck5a_IDS hck5a_check hck5a_cc hck5a_bodies).
Qed.

End Assembly.

Lemma hck5_safe_from :
  (forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
     hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
     piece_ok [u_hck5] (hck5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hck5_G) ->
  (forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
     x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
     map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw) =
       WgNoise.proof.protocol.prot_piece3.protocol_idents3 /\
     piece_ok [u_noise; u_cookie; u_shim]
       (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
       (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)) ->
  (forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
     x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
     piece_ok [u_h4_cookie_mac] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_cookie_mac)
       (hc4_G_cookie_mac x25519 aead_enc aead_dec W_cookie_mac)) ->
  blake2s3_ok ->
  (exists (G: funspecs) enc dec xenc xdec,
     aead_props enc dec /\ xaead_props xenc xdec /\
     piece_ok aead_units3 aead_imports3 G /\ map fst G = aead_idents3 /\
     asm_covers G (aead_iface3 enc dec xenc xdec) /\
     asm_covers G [@chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS dec;
                   @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xdec] /\
     Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G) ->
  (exists (G: funspecs) x,
     x25519_props x /\ piece_ok x25519_units3 x25519_imports3 G /\ map fst G = x25519_idents3 /\
     asm_covers G (x25519_iface3 x) /\
     Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G) ->
  harness_safe WgNoise.contracts.x_cookie_mac.whole_prog.
Proof.
  intros HPIECE HPROT HHC (Gb & HpB & HidB & HcovB)
         (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA)
         (Gx & x & Hxp & HpX & HidX & HcovX & HccX).
  destruct (HPROT x enc dec xenc xdec W_cookie_mac Hxp Hap Hxap) as [HprotI HprotP].
  exact (hck5a_safe Gb Ga Gx x enc dec xenc xdec HpB HidB HcovB HpA HidA HcovA HcovD HpX HidX HcovX
           HccA HccX HprotI HprotP (HHC x enc dec xenc xdec Hxp Hap Hxap)
           (HPIECE x enc dec xenc xdec (conj Hxp (conj Hap Hxap)))).
Qed.
