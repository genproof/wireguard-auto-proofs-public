(* law create_any: the assembly, for
   ANY lower pieces (Gb, Ga, Gx with their models) satisfying the interfaces, from the libc piece, the protocol
   piece v4 (prot4_piece_stmt: the statement of protocol_piece4, hc4_stmt.v), the common.h piece v4
   (hc4_piece_stmt_create_any) and the law's piece (main: HM, = hca5_piece).  v1:
   (the same assembly over prot_G3 / hc_G3_create_any / hca3_imports; port it). *)
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
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.ca3_xcs.
Require WgNoise.contracts.x_create_any.

Local Notation p := WgNoise.contracts.x_create_any.whole_prog.
Local Notation W := W_create_any.

Lemma ca5_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma ca5_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma ca5_cs_sub cs : In cs (WgNoise.contracts.x_create_any.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_create_any as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

(* common4's body compspecs are included in the world (hc4_piece_stmt's hypothesis) *)
Lemma ca5_cs4_sub : cspecs_sub WgNoise.proof.harness.common4.hc4_cs.CS4 W.
Proof. rewrite W_create_any_eq; apply world_cspecs_sub; vm_refl. Qed.

Ltac ca5_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac ca5_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac ca5_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition ca5_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++
           WgNoise.proof.protocol.prot_piece3.protocol_idents3 ++ hc4_ids_create_any) in exact l).

Lemma ca5_check : asm_check W p ca5_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma ca5_hc_ids x enc dec : map fst (hc4_G_create_any x enc dec W) = hc4_ids_create_any.
Proof. apply hc4_ids_ok_create_any. Qed.

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
Hypothesis Hhc: hc4_piece_stmt_create_any.
Hypothesis HM: piece_ok [u_hca3] (hca5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hca3_G.

Definition ca5_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++
  (hc4_G_create_any x25519 aead_enc aead_dec W).

Local Notation Gw := (@asm_Gall W p hca3_post ca5_Gr ca5_ids).

Lemma ca5_protI : map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) =
  WgNoise.proof.protocol.prot_piece3.protocol_idents3.
Proof. exact (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma ca5_protP : piece_ok [u_noise; u_cookie; u_shim] (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. exact (proj2 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma ca5_hcP : piece_ok [u_h4_create_any] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (hc4_G_create_any x25519 aead_enc aead_dec W).
Proof. exact (Hhc x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap ca5_cs4_sub). Qed.

Lemma ca5_IDS : map fst ca5_Gr = ca5_ids.
Proof.
  unfold ca5_Gr. rewrite !map_app, HidB, HidA, HidX, ca5_hc_ids, ca5_protI.
  reflexivity.
Qed.

Lemma ca5_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply ca5_IDS | apply ca5_check]. Qed.

Lemma ca5_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply ca5_IDS | apply ca5_check]. Qed.

Lemma ca5_find_Gr i s : In (i, s) ca5_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply ca5_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma ca5_covers_lift Gp G0 : incl Gp ca5_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply ca5_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma ca5_cov1 Gp G0 i s0 s1 : incl Gp ca5_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := ca5_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma ca5_incl_libc : incl (libc_G W) ca5_Gr.
Proof. intros a H. unfold ca5_Gr. apply in_app; auto. Qed.
Lemma ca5_incl_b2s : incl Gb ca5_Gr.
Proof. intros a H. unfold ca5_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma ca5_incl_aead : incl Ga ca5_Gr.
Proof. intros a H. unfold ca5_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma ca5_incl_x : incl Gx ca5_Gr.
Proof. intros a H. unfold ca5_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma ca5_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ca5_Gr.
Proof. intros a H. unfold ca5_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma ca5_incl_hc : incl (hc4_G_create_any x25519 aead_enc aead_dec W) ca5_Gr.
Proof. intros a H. unfold ca5_Gr. do 5 (apply in_app; right). auto. Qed.

Lemma ca5_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma ca5_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma ca5_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma ca5_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma ca5_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply ca5_nr_libc | apply incl_refl]. Qed.

Ltac ca5_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac ca5_from_libc sub :=
  eapply (ca5_cov1 (libc_G W) (libc_G W)); [apply ca5_incl_libc | apply ca5_nr_libc | apply ca5_cov_libc
                                            | unfold libc_G; ca5_inl | apply sub].
Ltac ca5_from_b2s sub :=
  eapply (ca5_cov1 Gb blake2s_G3); [apply ca5_incl_b2s | apply ca5_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; ca5_inl | apply sub].
Ltac ca5_from_aead sub :=
  eapply (ca5_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply ca5_incl_aead | apply ca5_nr_aead | apply HcovA | unfold aead_iface3; ca5_inl | apply sub].
Ltac ca5_from_dec sub :=
  eapply (ca5_cov1 Ga); [apply ca5_incl_aead | apply ca5_nr_aead | apply HcovD | ca5_inl | apply sub].
Ltac ca5_from_x sub :=
  eapply (ca5_cov1 Gx (x25519_iface3 x25519));
    [apply ca5_incl_x | apply ca5_nr_x | apply HcovX | unfold x25519_iface3; ca5_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma ca5_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [ca5_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (@ca3_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma ca5_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [ca5_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (@ca3_memset_sub Libc.CS cs) |].
  constructor; [ca5_from_b2s (@ca3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [ca5_from_b2s (@ca3_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [ca5_from_libc (@ca3_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma ca5_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply ca5_cov_aead_imports. Qed.

Lemma ca5_cov_env_ns : asm_covers Gw (WgNoise.proof.protocol.prot_prog3.env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply ca5_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx;
    repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma ca5_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply ca5_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma ca5_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (ca5_covers_lift Gb _ ca5_incl_b2s ca5_nr_b2s HcovB). Qed.

Lemma ca5_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply ca5_norepet' |]. intros a H. apply asm_Gr_incl, ca5_incl_prot, H. Qed.

Lemma ca5_cov_hcG : asm_covers Gw (hc4_G_create_any x25519 aead_enc aead_dec W).
Proof. apply asm_covers_incl; [apply ca5_norepet' |]. intros a H. apply asm_Gr_incl, ca5_incl_hc, H. Qed.

Lemma ca5_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, WgNoise.proof.protocol.prot_prog3.prot_imports3.
  apply asm_covers_app; [apply ca5_cov_env_ns |].
  apply asm_covers_app; [| apply ca5_cov_b2sG].
  constructor; [ca5_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (@ca3_memset_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (@ca3_memcmp_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [ca5_from_b2s (@ca3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [ca5_from_libc (@ca3_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [ca5_from_libc (@ca3___crypto_memneq_sub Shim.CS cs) |].
  constructor; [ca5_from_x (@ca3_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [ca5_from_x (@ca3_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [ca5_from_x (@ca3_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [ca5_from_aead (@ca3_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [ca5_from_dec (@ca3_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [ca5_from_aead (@ca3_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [ca5_from_dec (@ca3_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma ca5_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply ca5_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply ca5_cov_b2sG |
                           apply asm_covers_app; [apply ca5_cov_protG | apply ca5_cov_nondet_size]]].
  constructor; [ca5_from_libc (@ca3_memcpy_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (@ca3_memset_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (@ca3_memcmp_sub Libc.CS cs) |].
  constructor; [ca5_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [ca5_from_b2s (@ca3_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [ca5_from_libc (@ca3_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [ca5_from_x (@ca3_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [ca5_from_aead (@ca3_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [ca5_from_dec (@ca3_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [ca5_from_aead (@ca3_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [ca5_from_dec (@ca3_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma ca5_cov_hca5_imports cs : asm_covers Gw (hca5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec cs).
Proof.
  unfold hca5_imports. apply asm_covers_app; [exact (ca5_cov_hc_imports cs) | apply ca5_cov_hcG].
Qed.

Ltac ca5_unit := split; [apply ca5_cs_sub; ca5_in_cs |]; split; [ca5_varspecs |].

(* ---------- libc ---------- *)
Lemma ca5_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply ca5_norepet.
  - intros a H. apply asm_Gr_incl, ca5_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply ca5_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [ca5_unit; split; [apply CI | ca5_funs] |]); apply Forall_nil.
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma ca5_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply ca5_norepet.
  - intros a H. apply asm_Gr_incl, ca5_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [ca5_unit; split; [apply ca5_cov_b2s_imports | ca5_funs] |]); apply Forall_nil.
Qed.

(* ---------- AEAD ---------- *)
Lemma ca5_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply ca5_norepet.
  - intros a H. apply asm_Gr_incl, ca5_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [ca5_unit; split; [apply ca5_cov_aead_imports | ca5_funs] |]); apply Forall_nil.
Qed.

(* ---------- x25519 ---------- *)
Lemma ca5_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply ca5_norepet.
  - intros a H. apply asm_Gr_incl, ca5_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [ca5_unit; split; [apply ca5_cov_x_imports | ca5_funs] |]); apply Forall_nil.
Qed.

(* ---------- the protocol piece v4 ---------- *)
Lemma ca5_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ ca5_protP).
  - apply ca5_norepet.
  - intros a H. apply asm_Gr_incl, ca5_incl_prot, H.
  - rewrite ca5_protI.
    repeat (apply Forall_cons; [ca5_unit; split; [apply ca5_cov_prot_imports | ca5_funs] |]); apply Forall_nil.
Qed.

(* ---------- the common.h piece v4 ---------- *)
Lemma ca5_bodies_hc : asm_bodies W p Gw (hc4_G_create_any x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_create_any] _ _ ca5_hcP).
  - apply ca5_norepet.
  - intros a H. apply asm_Gr_incl, ca5_incl_hc, H.
  - rewrite ca5_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply ca5_cs_sub; left; reflexivity |]. split; [ca5_varspecs |].
    split; [apply ca5_cov_hc_imports | ca5_funs].
Qed.

(* ---------- the law's piece (main) ---------- *)
Lemma ca5_bodies_main : asm_bodies W p Gw hca3_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hca3] (hca5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hca3_G HM).
  - apply ca5_norepet.
  - intros a H. destruct H as [<-|[]]. left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [ca5_varspecs |].
    split; [apply ca5_cov_hca5_imports | ca5_funs].
Qed.

Lemma ca5_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma ca5_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) ca5_Gr.
Proof.
  unfold ca5_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (ca3_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; apply ca5_cc_dec; vm_compute; reflexivity.
Qed.

Lemma ca5_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma ca5_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hca3_post) :: ca5_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ ca5_bodies_main
           (ca5_bodies_app _ _ ca5_bodies_libc (ca5_bodies_app _ _ ca5_bodies_b2s
              (ca5_bodies_app _ _ ca5_bodies_aead (ca5_bodies_app _ _ ca5_bodies_x
                 (ca5_bodies_app _ _ ca5_bodies_prot ca5_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; left; reflexivity | right; exact H].
Qed.

Lemma ca5_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_create_any W W_create_any_eq ca5_cbc ca5_ext_ok hca3_post
           ca5_Gr ca5_ids ca5_IDS ca5_check ca5_cc ca5_bodies).
Qed.

End Assembly.
