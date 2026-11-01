(* law handshake_receive: the assembly helpers of hrx5_asm.v, a port of handshake_clear's hcl5_asm_a.v: asm_lib's asm_harness_safe in the
   world W_handshake_receive for ANY lower pieces (Gb, Ga, Gx with their models) satisfying the interfaces, from the
   libc piece, the protocol piece v4 (prot4_piece_stmt), the common.h piece v4 (hc4_piece_stmt_handshake_receive)
   and the law's two pieces: main at W (hrx5_mpiece_stmt) and the harness unit's other functions at HRX
   (hrx5_lpiece_stmt, instantiated at CSw := W so that its specifications are main's imports).  Cross-compspecs
   funspec_sub lemmas: the base's hci3_xcs.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci3_xcs.
Require WgNoise.proof.libc.libc_bytes.
Require WgNoise.contracts.x_handshake_receive.

Local Notation p := WgNoise.contracts.x_handshake_receive.whole_prog.
Local Notation W := W_handshake_receive.

Lemma hrx5a_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hrx5a_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hrx5a_cs_sub cs : In cs (WgNoise.contracts.x_handshake_receive.Harness.CS :: all_unit_cs) -> cspecs_sub cs W.
Proof.
  destruct world_ok_handshake_receive as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hrx5a_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hrx5a_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hrx5a_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the harness unit's functions but main *)
Definition hrx5_loc_ids : list ident :=
  [HRC._wg_shim_rx_peer; HRC._wg_packet_send_handshake_cookie; HRC._wg_socket_set_peer_endpoint_from_skb;
   HRC._wg_packet_send_handshake_response; HRC._wg_timers_session_derived; HRC._wg_timers_handshake_complete;
   HRC._wg_packet_send_keepalive; HRC._wg_timers_any_authenticated_packet_received;
   HRC._wg_timers_any_authenticated_packet_traversal; HRC._update_rx_stats; HRC._validate_header_len;
   HRC._wg_receive_handshake_packet; HRC._m_expired; HRC._m_cookie; HRC._rx_reset; HRC._rx_only_cookie;
   HRC._rx_authenticated; HRC._dispatch; HRC._draw_type; HRC._k_initiation; HRC._k_response; HRC._draw_macs].

Lemma hrx5a_loc_ids_ok x ad xe xd cs : map fst (hrx5_G_local x ad xe xd cs) = hrx5_loc_ids.
Proof. reflexivity. Qed.

(* the identifiers of the real specifications, main excepted *)
Definition hrx5a_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ aead_idents3 ++ x25519_idents3 ++
           WgNoise.proof.protocol.prot_piece3.protocol_idents3 ++ hc4_ids_handshake_receive ++ hrx5_loc_ids)
        in exact l).

Lemma hrx5a_check : asm_check W p hrx5a_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hrx5a_hc_ids x enc dec : map fst (hc4_G_handshake_receive x enc dec W) = hc4_ids_handshake_receive.
Proof. apply hc4_ids_ok_handshake_receive. Qed.

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
Hypothesis Hhc: hc4_piece_stmt_handshake_receive.
Hypothesis HM: piece_ok [u_hrx5] (hrx5_mimports x25519 aead_dec xaead_enc xaead_dec) hrx5_G.
Hypothesis HL: piece_ok [u_hrx5l] (hrx5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (hrx5_G_local x25519 aead_dec xaead_enc xaead_dec W).

Definition hrx5a_Gr : funspecs := libc_G W ++ Gb ++ Ga ++ Gx ++ (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) ++
  (hc4_G_handshake_receive x25519 aead_enc aead_dec W) ++ (hrx5_G_local x25519 aead_dec xaead_enc xaead_dec W).

Local Notation Gw := (@asm_Gall W p hrx5_post hrx5a_Gr hrx5a_ids).

Lemma hrx5a_protI : map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) =
  WgNoise.proof.protocol.prot_piece3.protocol_idents3.
Proof. exact (proj1 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma hrx5a_protP : piece_ok [u_noise; u_cookie; u_shim] (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. exact (proj2 (Hprot x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap)). Qed.

Lemma hrx5a_hcP : piece_ok [u_h4_handshake_receive] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W)
  (hc4_G_handshake_receive x25519 aead_enc aead_dec W).
Proof. exact (Hhc x25519 aead_enc aead_dec xaead_enc xaead_dec W Hxp Hap Hxap hrx5_cs4_sub). Qed.

Lemma hrx5a_IDS : map fst hrx5a_Gr = hrx5a_ids.
Proof.
  unfold hrx5a_Gr. rewrite !map_app, HidB, HidA, HidX, hrx5a_hc_ids, hrx5a_protI, hrx5a_loc_ids_ok.
  reflexivity.
Qed.

Lemma hrx5a_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hrx5a_IDS | apply hrx5a_check]. Qed.

Lemma hrx5a_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hrx5a_IDS | apply hrx5a_check]. Qed.

Lemma hrx5a_find_Gr i s : In (i, s) hrx5a_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hrx5a_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma hrx5a_covers_lift Gp G0 : incl Gp hrx5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  asm_covers Gw G0.
Proof.
  intros INC LNR COV. unfold asm_covers in *. rewrite Forall_forall in *. intros ix H.
  destruct (COV ix H) as [s [F S]]. exists s; split; auto.
  apply hrx5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hrx5a_cov1 Gp G0 i s0 s1 : incl Gp hrx5a_Gr -> list_norepet (map fst Gp) -> asm_covers Gp G0 ->
  In (i, s0) G0 -> funspec_sub s0 s1 -> exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof.
  intros INC LNR COV Hin S01. assert (C := hrx5a_covers_lift Gp G0 INC LNR COV).
  unfold asm_covers in C. rewrite Forall_forall in C. destruct (C _ Hin) as [s [F S]].
  exists s; split; auto. eapply funspec_sub_trans; eauto.
Qed.

Lemma hrx5a_incl_libc : incl (libc_G W) hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. apply in_app; auto. Qed.
Lemma hrx5a_incl_b2s : incl Gb hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. apply in_app; right; apply in_app; auto. Qed.
Lemma hrx5a_incl_aead : incl Ga hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. do 2 (apply in_app; right). apply in_app; auto. Qed.
Lemma hrx5a_incl_x : incl Gx hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. do 3 (apply in_app; right). apply in_app; auto. Qed.
Lemma hrx5a_incl_prot : incl (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W) hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. do 4 (apply in_app; right). apply in_app; auto. Qed.
Lemma hrx5a_incl_hc : incl (hc4_G_handshake_receive x25519 aead_enc aead_dec W) hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. do 5 (apply in_app; right). apply in_app; auto. Qed.
Lemma hrx5a_incl_loc : incl (hrx5_G_local x25519 aead_dec xaead_enc xaead_dec W) hrx5a_Gr.
Proof. intros a H. unfold hrx5a_Gr. do 6 (apply in_app; right). auto. Qed.

Lemma hrx5a_nr_libc : list_norepet (map fst (libc_G W)).
Proof. apply compute_list_norepet_e; reflexivity. Qed.
Lemma hrx5a_nr_b2s : list_norepet (map fst Gb).
Proof. apply HpB. Qed.
Lemma hrx5a_nr_aead : list_norepet (map fst Ga).
Proof. apply HpA. Qed.
Lemma hrx5a_nr_x : list_norepet (map fst Gx).
Proof. apply HpX. Qed.

Lemma hrx5a_cov_libc : asm_covers (libc_G W) (libc_G W).
Proof. apply asm_covers_incl; [apply hrx5a_nr_libc | apply incl_refl]. Qed.

Ltac hrx5a_inl := simpl; repeat first [left; reflexivity | right].

(* the entries owned by the libc piece, the BLAKE2s piece, the AEAD piece, the x25519 piece *)
Ltac hrx5a_from_libc sub :=
  eapply (hrx5a_cov1 (libc_G W) (libc_G W)); [apply hrx5a_incl_libc | apply hrx5a_nr_libc | apply hrx5a_cov_libc
                                            | unfold libc_G; hrx5a_inl | apply sub].
Ltac hrx5a_from_b2s sub :=
  eapply (hrx5a_cov1 Gb blake2s_G3); [apply hrx5a_incl_b2s | apply hrx5a_nr_b2s | apply HcovB
                                   | unfold blake2s_G3; hrx5a_inl | apply sub].
Ltac hrx5a_from_aead sub :=
  eapply (hrx5a_cov1 Ga (aead_iface3 aead_enc aead_dec xaead_enc xaead_dec));
    [apply hrx5a_incl_aead | apply hrx5a_nr_aead | apply HcovA | unfold aead_iface3; hrx5a_inl | apply sub].
Ltac hrx5a_from_dec sub :=
  eapply (hrx5a_cov1 Ga); [apply hrx5a_incl_aead | apply hrx5a_nr_aead | apply HcovD | hrx5a_inl | apply sub].
Ltac hrx5a_from_x sub :=
  eapply (hrx5a_cov1 Gx (x25519_iface3 x25519));
    [apply hrx5a_incl_x | apply hrx5a_nr_x | apply HcovX | unfold x25519_iface3; hrx5a_inl | apply sub].

(* the imports common to the lower pieces *)
Lemma hrx5a_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [hrx5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_memset_sub Libc.CS cs) | constructor].
Qed.

Lemma hrx5a_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [hrx5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hrx5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hrx5a_from_b2s (@hci3x_get_unaligned_le32_sub Blake2s.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) | constructor].
Qed.

Lemma hrx5a_cov_x_imports cs : asm_covers Gw (x25519_imports3 cs).
Proof. apply hrx5a_cov_aead_imports. Qed.

Lemma hrx5a_cov_env_ns : asm_covers Gw (WgNoise.proof.protocol.prot_prog3.env_specs_ns W).
Proof.
  apply asm_covers_incl; [apply hrx5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx; unfold asm_env.env_specs; simpl in *; tauto |].
  unfold WgNoise.proof.protocol.prot_prog3.env_specs_ns in Hx;
    repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

Lemma hrx5a_cov_nondet_size : asm_covers Gw [nondet_size_spec].
Proof.
  apply asm_covers_incl; [apply hrx5a_norepet' |]. intros [i s] Hx.
  apply asm_E_incl; [destruct Hx as [Hx|[]]; rewrite <- Hx; unfold asm_env.env_specs; simpl; tauto |].
  destruct Hx as [Hx|[]]; inv Hx; reflexivity.
Qed.

Lemma hrx5a_cov_b2sG : asm_covers Gw blake2s_G3.
Proof. exact (hrx5a_covers_lift Gb _ hrx5a_incl_b2s hrx5a_nr_b2s HcovB). Qed.

Lemma hrx5a_cov_protG : asm_covers Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof. apply asm_covers_incl; [apply hrx5a_norepet' |]. intros a H. apply asm_Gr_incl, hrx5a_incl_prot, H. Qed.

Lemma hrx5a_cov_prot_imports cs : asm_covers Gw (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold prot_imports4, WgNoise.proof.protocol.prot_prog3.prot_imports3.
  apply asm_covers_app; [apply hrx5a_cov_env_ns |].
  apply asm_covers_app; [| apply hrx5a_cov_b2sG].
  constructor; [hrx5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hrx5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x___crypto_memneq_sub Shim.CS cs) |].
  constructor; [hrx5a_from_x (@hci3x_clamp_secret_sub Curve25519Fiat32.CS cs) |].
  constructor; [hrx5a_from_x (@hci3x_curve25519_sub Curve25519.CS cs x25519) |].
  constructor; [hrx5a_from_x (@hci3x_generate_public_sub Curve25519.CS cs x25519) |].
  constructor; [hrx5a_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hrx5a_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hrx5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hrx5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

Lemma hrx5a_cov_hc_imports cs : asm_covers Gw (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof.
  unfold hc4_imports. apply asm_covers_app; [apply hrx5a_cov_env_ns |].
  apply asm_covers_app; [| apply asm_covers_app; [apply hrx5a_cov_b2sG |
                           apply asm_covers_app; [apply hrx5a_cov_protG | apply hrx5a_cov_nondet_size]]].
  constructor; [hrx5a_from_libc (@hci3x_memcpy_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_memset_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_memcmp_sub Libc.CS cs) |].
  constructor; [hrx5a_from_libc (funspec_sub_refl (snd (@calloc_spec W))) |].
  constructor; [hrx5a_from_b2s (@hci3x_memzero_explicit_sub Blake2s.CS cs) |].
  constructor; [hrx5a_from_libc (@hci3x_crypto_memneq_sub Curve25519.CS cs) |].
  constructor; [hrx5a_from_x (@hci3x_curve25519_generic_sub Curve25519Fiat32.CS cs x25519) |].
  constructor; [hrx5a_from_aead (@hci3x_encrypt_sub Chacha20poly1305.CS cs aead_enc) |].
  constructor; [hrx5a_from_dec (@hci3x_decrypt3_sub Chacha20poly1305.CS cs aead_dec) |].
  constructor; [hrx5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS cs xaead_enc) |].
  constructor; [hrx5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS cs xaead_dec) | constructor].
Qed.

(* main's imports: entries of prot_G4 / hc4_G_handshake_receive found by their identifiers *)
Lemma hrx5a_cov_find G G0 : incl G hrx5a_Gr -> list_norepet (map fst G) ->
  Forall (fun ix => initial_world.find_id (fst ix) G = Some (snd ix)) G0 -> asm_covers Gw G0.
Proof.
  intros INC LNR F. unfold asm_covers. rewrite Forall_forall in *. intros [i s] H.
  specialize (F _ H). simpl in F. exists s; split; [| apply funspec_sub_refl].
  apply hrx5a_find_Gr, INC. apply initial_world.find_id_e; auto.
Qed.

Lemma hrx5a_nr_prot : list_norepet (map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W)).
Proof. apply hrx5a_protP. Qed.
Lemma hrx5a_nr_hc : list_norepet (map fst (hc4_G_handshake_receive x25519 aead_enc aead_dec W)).
Proof. apply hrx5a_hcP. Qed.

Lemma hrx5a_nr_loc : list_norepet (map fst (hrx5_G_local x25519 aead_dec xaead_enc xaead_dec W)).
Proof. apply HL. Qed.

Lemma hrx5a_cov_hcG : asm_covers Gw (hc4_G_handshake_receive x25519 aead_enc aead_dec W).
Proof. apply asm_covers_incl; [apply hrx5a_norepet' |]. intros a H. apply asm_Gr_incl, hrx5a_incl_hc, H. Qed.

Lemma hrx5a_cov_loc_imports cs : asm_covers Gw (hrx5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W cs).
Proof. unfold hrx5_imports. apply asm_covers_app; [apply hrx5a_cov_hc_imports | apply hrx5a_cov_hcG]. Qed.

Lemma hrx5a_cov_mimports : asm_covers Gw (hrx5_mimports x25519 aead_dec xaead_enc xaead_dec W).
Proof.
  unfold hrx5_mimports. apply asm_covers_app; [apply hrx5a_cov_env_ns |].
  apply asm_covers_app; [apply hrx5a_cov_nondet_size |].
  apply asm_covers_app.
  { constructor; [hrx5a_from_aead (@hci3x_xencrypt_sub Chacha20poly1305.CS W xaead_enc) |].
    constructor; [hrx5a_from_dec (@hci3x_xdecrypt3_sub Chacha20poly1305.CS W xaead_dec) | constructor]. }
  apply asm_covers_app.
  { apply (hrx5a_cov_find _ _ hrx5a_incl_prot hrx5a_nr_prot).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity. }
  apply asm_covers_app.
  { apply (hrx5a_cov_find _ _ hrx5a_incl_hc hrx5a_nr_hc).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity. }
  apply asm_covers_app.
  { apply (hrx5a_cov_find _ _ hrx5a_incl_hc hrx5a_nr_hc).
    repeat apply Forall_cons; try apply Forall_nil; reflexivity. }
  apply (hrx5a_cov_find _ _ hrx5a_incl_loc hrx5a_nr_loc).
  repeat apply Forall_cons; try apply Forall_nil; reflexivity.
Qed.

Ltac hrx5a_unit := split; [apply hrx5a_cs_sub; hrx5a_in_cs |]; split; [hrx5a_varspecs |].

Lemma hrx5a_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hrx5a_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [hrx5a_unit; split; [apply CI | hrx5a_funs] |]); apply Forall_nil.
Qed.

Lemma hrx5a_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [hrx5a_unit; split; [apply hrx5a_cov_b2s_imports | hrx5a_funs] |]); apply Forall_nil.
Qed.

Lemma hrx5a_bodies_aead : asm_bodies W p Gw Ga.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 Ga HpA).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_aead, H.
  - rewrite HidA. unfold aead_units3.
    repeat (apply Forall_cons; [hrx5a_unit; split; [apply hrx5a_cov_aead_imports | hrx5a_funs] |]); apply Forall_nil.
Qed.

Lemma hrx5a_bodies_x : asm_bodies W p Gw Gx.
Proof.
  apply (asm_piece_lift W p Gw x25519_units3 x25519_imports3 Gx HpX).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_x, H.
  - rewrite HidX. unfold x25519_units3.
    repeat (apply Forall_cons; [hrx5a_unit; split; [apply hrx5a_cov_x_imports | hrx5a_funs] |]); apply Forall_nil.
Qed.

Lemma hrx5a_bodies_prot : asm_bodies W p Gw (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_noise; u_cookie; u_shim] _ _ hrx5a_protP).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_prot, H.
  - rewrite hrx5a_protI.
    repeat (apply Forall_cons; [hrx5a_unit; split; [apply hrx5a_cov_prot_imports | hrx5a_funs] |]); apply Forall_nil.
Qed.

Lemma hrx5a_bodies_hc : asm_bodies W p Gw (hc4_G_handshake_receive x25519 aead_enc aead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_h4_handshake_receive] _ _ hrx5a_hcP).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_hc, H.
  - rewrite hrx5a_hc_ids.
    apply Forall_cons; [| apply Forall_nil].
    split; [apply hrx5a_cs_sub; left; reflexivity |]. split; [hrx5a_varspecs |].
    split; [apply hrx5a_cov_hc_imports | hrx5a_funs].
Qed.

(* the law's local piece (the harness unit's functions but main, at HRX) *)
Lemma hrx5a_bodies_loc : asm_bodies W p Gw (hrx5_G_local x25519 aead_dec xaead_enc xaead_dec W).
Proof.
  apply (asm_piece_lift W p Gw [u_hrx5l] _ _ HL).
  - apply hrx5a_norepet.
  - intros a H. apply asm_Gr_incl, hrx5a_incl_loc, H.
  - rewrite hrx5a_loc_ids_ok. unfold hrx5_loc_ids.
    repeat (apply Forall_cons; [split; [apply hrx5a_cs_sub; left; reflexivity |]; split; [hrx5a_varspecs |];
                                split; [apply hrx5a_cov_loc_imports | hrx5a_funs] |]); apply Forall_nil.
Qed.

(* the law's main piece *)
Lemma hrx5a_bodies_main : asm_bodies W p Gw hrx5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hrx5] _ hrx5_G HM).
  - apply hrx5a_norepet.
  - intros a H. destruct H as [<-|[]]. left; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    split; [apply cspecs_sub_refl |]. split; [hrx5a_varspecs |].
    split; [apply hrx5a_cov_mimports | hrx5a_funs].
Qed.

Lemma hrx5a_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Lemma hrx5a_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hrx5a_Gr.
Proof.
  unfold hrx5a_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (hci3x_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply Forall_app; split; [exact HccA |].
  apply Forall_app; split; [exact HccX |].
  apply Forall_app; split; [| apply Forall_app; split]; apply hrx5a_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hrx5a_bodies_app L1 L2 : asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> asm_bodies W p Gw (L1 ++ L2).
Proof. intros H1 H2. exact (asm_bodies_incl _ _ _ _ _ _ H1 H2 (incl_refl _)). Qed.

Lemma hrx5a_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hrx5_post) :: hrx5a_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hrx5a_bodies_main
           (hrx5a_bodies_app _ _ hrx5a_bodies_libc (hrx5a_bodies_app _ _ hrx5a_bodies_b2s
              (hrx5a_bodies_app _ _ hrx5a_bodies_aead (hrx5a_bodies_app _ _ hrx5a_bodies_x
                 (hrx5a_bodies_app _ _ hrx5a_bodies_prot
                    (hrx5a_bodies_app _ _ hrx5a_bodies_hc hrx5a_bodies_loc))))))).
  intros a H. apply in_app. destruct H as [<-|H]; [left; left; reflexivity | right; exact H].
Qed.

Lemma hrx5a_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_handshake_receive W W_handshake_receive_eq hrx5a_cbc hrx5a_ext_ok hrx5_post
           hrx5a_Gr hrx5a_ids hrx5a_IDS hrx5a_check hrx5a_cc hrx5a_bodies).
Qed.

End Assembly.
