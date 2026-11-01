(* law handshake: the assembly, for ANY lower pieces
   (Gb, Ga, Gx with their models) satisfying the interfaces, from the libc piece, the protocol piece, the
   common.h piece (hc_pieces3) and the law's piece (hhs3_piece). *)
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
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.common.hc_bodies3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_piece.
Require Import WgNoise.proof.harness.handshake.hhs3_xcs.
Require WgNoise.contracts.x_handshake.

Local Notation p := WgNoise.contracts.x_handshake.whole_prog.
Local Notation W := W_handshake.

Lemma hhs3a_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hhs3a_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hhs3a_cs_sub cs : In cs (WgNoise.contracts.x_handshake.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_handshake as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hhs3a_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hhs3a_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hhs3a_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hhs3a_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++ protocol_idents3 ++
           hc_ids_handshake) in exact l).

Lemma hhs3a_check : asm_check W p hhs3a_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3a_hc_ids x enc dec : map fst (hc_G3_handshake x enc dec) = hc_ids_handshake.
Proof. reflexivity. Qed.

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
(* law handshake: X25519 commutativity on the base point and clamp invariance *)
Hypothesis Hcomm: hhs3_comm x25519.
(* prot_rep_lemmas3's statement *)
Hypothesis Hrep: hhs3_rep.

Definition hhs3a_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++ (hc_G3_handshake x25519 aead_enc aead_dec).

Local Notation Gw := (@asm_Gall W p hhs3_post hhs3a_Gr hhs3a_ids).

Lemma hhs3a_IDS : map fst hhs3a_Gr = hhs3a_ids.
Proof.
  unfold hhs3a_Gr. rewrite !map_app, HidB, HidA, HidX, hhs3a_hc_ids.
  rewrite (proj1 (protocol_piece3 x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)).
  reflexivity.
Qed.

Lemma hhs3a_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hhs3a_IDS | apply hhs3a_check]. Qed.

Lemma hhs3a_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hhs3a_IDS | apply hhs3a_check]. Qed.

Lemma hhs3a_find_Gr i s : In (i, s) hhs3a_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hhs3a_norepet']. apply asm_Gr_incl; auto. Qed.

(* a sub-list Gp of Gr covering G0 makes Gw cover G0 *)
Lemma hhs3a_covers_lift Gp G0 : incl Gp hhs3a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hhs3a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hhs3a_cov1 Gp G0 i s0 s1 : incl Gp hhs3a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hhs3a_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hhs3a_incl_libc : incl (libc_G W) hhs3a_Gr.
Proof. intros a H. unfold hhs3a_Gr. apply in_app; auto. Qed.
Lemma hhs3a_incl_b2s : incl Gb hhs3a_Gr.
Proof. intros a H. unfold hhs3a_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hhs3a_incl_aead : incl Ga hhs3a_Gr.
Proof. intros a H. unfold hhs3a_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hhs3a_incl_x : incl Gx hhs3a_Gr.
Proof. intros a H. unfold hhs3a_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hhs3a_incl_prot : incl (prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hhs3a_Gr.
Proof. intros a H. unfold hhs3a_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hhs3a_incl_hc : incl (hc_G3_handshake x25519 aead_enc aead_dec) hhs3a_Gr.
Proof. intros a H. unfold hhs3a_Gr. do 5 (apply in_app; right). auto. Qed.

Lemma hhs3a_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hhs3a_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hhs3a_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hhs3a_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hhs3a_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hhs3a_nr_libc | apply incl_refl]. Qed.

Ltac hhs3a_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac hhs3a_from_libc sub :=
  eapply (hhs3a_cov1 (libc_G W) (libc_G W)); [apply hhs3a_incl_libc | apply hhs3a_nr_libc | apply hhs3a_cov_libc
                                            | unfold libc_G; hhs3a_inl | apply sub].
Ltac hhs3a_from_b2s sub :=
  eapply (hhs3a_cov1 Gb blake2s_G3); [apply hhs3a_incl_b2s | apply hhs3a_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hhs3a_inl | apply sub].
Ltac hhs3a_from_aead sub :=
  eapply (hhs3a_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hhs3a_incl_aead | apply hhs3a_nr_aead | apply HcovA | unfold aead_iface3; hhs3a_inl | apply sub].
Ltac hhs3a_from_dec sub :=
  eapply (hhs3a_cov1 Ga); [apply hhs3a_incl_aead | apply hhs3a_nr_aead | apply HcovD | hhs3a_inl | apply sub].
Ltac hhs3a_from_x sub :=
  eapply (hhs3a_cov1 Gx (x25519_iface3 x25519));
    [apply hhs3a_incl_x | apply hhs3a_nr_x | apply HcovX | unfold x25519_iface3; hhs3a_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma hhs3a_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hhs3a_from_libc (@hhs3x_memcpy_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hhs3a_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hhs3a_from_libc (@hhs3x_memcpy_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_memset_sub Libc.CS cs) |].
  constructor; [hhs3a_from_b2s (@hhs3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hhs3a_from_b2s (@hhs3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hhs3a_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hhs3a_cov_aead_imports. Qed.

(* the environment's functions the protocol / common.h imports name: all but nondet_size (env_specs_ns), all
   present in this program *)
Lemma hhs3a_cov_env : asm_covers Gw (env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hhs3a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold env_specs_ns in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hhs3a_covers_filter (G l: funspecs) f : asm_covers G l -> asm_covers G (filter f l).
Proof. unfold asm_covers. intros H. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  rewrite Forall_forall in H. auto. Qed.

Lemma hhs3a_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hhs3a_covers_lift Gb _ hhs3a_incl_b2s hhs3a_nr_b2s HcovB). Qed.

Lemma hhs3a_cov_protG : asm_covers Gw (prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hhs3a_norepet' |]. intros a H. apply asm_Gr_incl, hhs3a_incl_prot, H. Qed.

Lemma hhs3a_cov_hcG : asm_covers Gw (hc_G3_handshake x25519 aead_enc aead_dec).
Proof. apply asm_covers_incl; [apply hhs3a_norepet' |]. intros a H. apply asm_Gr_incl, hhs3a_incl_hc, H. Qed.

Lemma hhs3a_cov_prot_imports cs : asm_covers Gw (prot_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports3. apply asm_covers_app; [apply hhs3a_cov_env |].
  apply asm_covers_app; [| apply hhs3a_cov_b2sG].
  constructor; [hhs3a_from_libc (@hhs3x_memcpy_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_memset_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_memcmp_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hhs3a_from_b2s (@hhs3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hhs3a_from_x (@hhs3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hhs3a_from_x (@hhs3x_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hhs3a_from_x (@hhs3x_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hhs3a_from_aead (@hhs3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hhs3a_from_dec (@hhs3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hhs3a_from_aead (@hhs3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hhs3a_from_dec (@hhs3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hhs3a_cov_hc_rest cs : exists R, hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs = env_specs_ns W ++ R /\
  asm_covers Gw R.
Proof.
  eexists; split; [unfold hc_imports3; reflexivity |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hhs3a_cov_b2sG | apply hhs3a_cov_protG]].
  constructor; [hhs3a_from_libc (@hhs3x_memcpy_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_memset_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_memcmp_sub Libc.CS cs) |].
  constructor; [hhs3a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hhs3a_from_b2s (@hhs3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hhs3a_from_libc (@hhs3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hhs3a_from_x (@hhs3x_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hhs3a_from_aead (@hhs3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hhs3a_from_dec (@hhs3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hhs3a_from_aead (@hhs3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hhs3a_from_dec (@hhs3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hhs3a_cov_hc_imports cs : asm_covers Gw (hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  destruct (hhs3a_cov_hc_rest cs) as [R [E C]]. rewrite E. apply asm_covers_app; [apply hhs3a_cov_env | exact C].
Qed.

Lemma hhs3a_cov_hhs3_imports cs : asm_covers Gw (hhs3_imports x25519 aead_enc aead_dec xaead_enc xaead_dec cs).
Proof.
  unfold hhs3_imports. apply asm_covers_app; [exact (hhs3a_cov_hc_imports cs) |].
  apply hhs3a_cov_hcG.
Qed.

Ltac hhs3a_unit := split; [apply hhs3a_cs_sub; hhs3a_in_cs |]; split; [hhs3a_varspecs |].

(* ---------- libc ---------- *)
Lemma hhs3a_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hhs3a_norepet.
  - intros a H. apply asm_Gr_incl, hhs3a_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hhs3a_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hhs3a_unit; split; [apply CI | hhs3a_funs] |]); apply Forall_nil.
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma hhs3a_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hhs3a_norepet.
  - intros a H. apply asm_Gr_incl, hhs3a_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hhs3a_unit; split; [apply hhs3a_cov_b2s_imports | hhs3a_funs] |]); apply Forall_nil.
Qed.

(* ---------- AEAD ---------- *)
Lemma hhs3a_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hhs3a_norepet.
  - intros a H. apply asm_Gr_incl, hhs3a_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hhs3a_unit; split; [apply hhs3a_cov_aead_imports | hhs3a_funs] |]); apply Forall_nil.
Qed.

(* ---------- x25519 ---------- *)
Lemma hhs3a_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hhs3a_norepet.
  - intros a H. apply asm_Gr_incl, hhs3a_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hhs3a_unit; split; [apply hhs3a_cov_x_imports | hhs3a_funs] |]); apply Forall_nil.
Qed.

(* ---------- the protocol piece ---------- *)
Lemma hhs3a_bodies_prot : asm_bodies W p Gw (prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  destruct (protocol_piece3 x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap) as [IDS PK].
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ PK).
  - apply hhs3a_norepet.
  - intros a H. apply asm_Gr_incl, hhs3a_incl_prot, H.
  - rewrite IDS.
    repeat (apply Forall_cons; [hhs3a_unit; split; [apply hhs3a_cov_prot_imports | hhs3a_funs] |]); apply Forall_nil.
Qed.

(* ---------- the common.h piece ---------- *)
Lemma hhs3a_bodies_hc : asm_bodies W p Gw (hc_G3_handshake x25519 aead_enc aead_dec).
Proof.
  destruct (hc_pieces3 x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap) as [_ [_ [PK _]]].
  apply (asm_piece_lift W p Gw [u_h_handshake] _ _ PK).
  - apply hhs3a_norepet.
  - intros a H. apply asm_Gr_incl, hhs3a_incl_hc, H.
  - rewrite hhs3a_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hhs3a_cs_sub; left; reflexivity |]. split; [hhs3a_varspecs |].
    split; [apply hhs3a_cov_hc_imports | hhs3a_funs].
Qed.

(* ---------- the law's piece (main) ---------- *)
Lemma hhs3a_bodies_main : asm_bodies W p Gw hhs3_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hhs3] (hhs3_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hhs3_G
           (hhs3_piece x25519 aead_enc aead_dec xaead_enc xaead_dec
              (conj Hxp (conj Hap (conj Hxap (conj Hcomm Hrep)))))).
  - apply hhs3a_norepet.
  - intros a H. destruct H as [<-|[]]. left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [hhs3a_varspecs |].
    split; [apply hhs3a_cov_hhs3_imports | hhs3a_funs].
Qed.

Lemma hhs3a_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hhs3a_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hhs3a_Gr.
Proof.
  unfold hhs3a_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (hhs3x_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; apply hhs3a_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hhs3a_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hhs3a_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hhs3_post) :: hhs3a_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hhs3a_bodies_main
           (hhs3a_bodies_app _ _ hhs3a_bodies_libc (hhs3a_bodies_app _ _ hhs3a_bodies_b2s
              (hhs3a_bodies_app _ _ hhs3a_bodies_aead (hhs3a_bodies_app _ _ hhs3a_bodies_x
                 (hhs3a_bodies_app _ _ hhs3a_bodies_prot hhs3a_bodies_hc)))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; left; reflexivity | right; exact H].
Qed.

Lemma hhs3a_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_handshake W W_handshake_eq hhs3a_cbc hhs3a_ext_ok hhs3_post
           hhs3a_Gr hhs3a_ids hhs3a_IDS hhs3a_check hhs3a_cc hhs3a_bodies).
Qed.

End Assembly.
