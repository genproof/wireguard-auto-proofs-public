(* the assembly.
   Pieces: libc (libc_piece), BLAKE2s (ANY piece Gb of the interface blake2s3_ok: memzero_explicit and
   get_unaligned_le32 for the AEAD), the CONCRETE AEAD piece (aead_piece3b: the harness compares the kernel's
   verdict with the reference's, so the model aead_dec must be the concrete one), the counter piece (cnt_piece3),
   the shared common.h functions, the NULL-tolerant
   reference AEAD (ht4r_piece), the transport.h shadow model, main (hka5_piece).
   Every other function of the program (noise.c, cookie.c, the shim, data_header.c, Curve25519, ...) is never
   called: asm_lib gives it a vacuous specification. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3b.
Require WgNoise.proof.aead.aead_piece3b WgNoise.proof.aead.aead_models_props3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_piece3.
Require Import WgNoise.proof.harness.replay.rp3_xcs.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_spec.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_piece.
Require Import WgNoise.proof.harness.common4t.ht4r_piece.
Require Import WgNoise.proof.harness.common4t.ht4r_sub.
Require Import WgNoise.proof.harness.common4t.ht4c_sub.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.harness.transport_keepalive.ht4k_cnt.
Require WgNoise.proof.harness.prim_aead.haead_piece3.
Require WgNoise.proof.harness.transport_keepalive.ht4k_wm_body_a WgNoise.proof.harness.transport_keepalive.ht4k_wm_body_c
        WgNoise.proof.harness.transport_keepalive.ht4k_rc_body.
Require WgNoise.contracts.x_transport_keepalive.

Local Notation p := WgNoise.contracts.x_transport_keepalive.whole_prog.
Local Notation W := W_transport_keepalive.

Lemma hka5_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hka5_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma hka5_cs_sub cs : In cs (WgNoise.contracts.x_transport_keepalive.Harness.CS :: DataHeader.CS :: all_unit_cs) ->
  cspecs_sub cs W.
Proof.
  destruct world_ok_transport_keepalive as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac hka5_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac hka5_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hka5_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

(* the identifiers of the real specifications, main excepted *)
Definition hka5_ids : list ident :=
  ltac:(let l := eval compute in
          (map fst (libc_G W) ++ map fst blake2s_G3 ++ map fst aead_G3b ++ map fst cnt_G ++ map fst ht4c_G1 ++
           [fst (rp_final_spec_of hka5_mp)] ++ map fst (ht4r_G hka5_mp) ++ map fst ht4k_wm_G) in exact l).

Lemma hka5_check : asm_check W p hka5_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hka5_cc_dec (l: funspecs) :
  forallb (fun ix => if calling_convention_eq (callingconvention_of_funspec (snd ix)) cc_default then true else false) l = true ->
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) l.
Proof.
  intros H. rewrite forallb_forall in H. apply Forall_forall. intros ix Hx. specialize (H ix Hx).
  destruct (calling_convention_eq _ _); [auto | discriminate].
Qed.

Section Assembly.
Variable Gb: funspecs.
Hypothesis HpB: piece_ok blake2s_units3 blake2s_imports3 Gb.
Hypothesis HidB: map fst Gb = map fst blake2s_G3.
Hypothesis HcovB: asm_covers Gb blake2s_G3.

(* the real specifications, main excepted *)
Definition hka5_Gr : funspecs :=
  libc_G W ++ Gb ++ aead_G3b ++ cnt_G ++ ht4c_G1 ++ [rp_final_spec_of hka5_mp] ++ ht4r_G hka5_mp ++ ht4k_wm_G.

Local Notation Gw := (@asm_Gall W p hka5_post hka5_Gr hka5_ids).

Lemma hka5_IDS : map fst hka5_Gr = hka5_ids.
Proof. unfold hka5_Gr. rewrite !map_app, HidB. reflexivity. Qed.

Lemma hka5_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hka5_IDS | apply hka5_check]. Qed.

Lemma hka5_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hka5_IDS | apply hka5_check]. Qed.

Lemma hka5_find_Gr i s : In (i, s) hka5_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hka5_norepet']. apply asm_Gr_incl; auto. Qed.

(* the eight blocks of Gr *)
Lemma hka5_in_libc ix : In ix (libc_G W) -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.
Lemma hka5_in_b2s ix : In ix Gb -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.
Lemma hka5_in_aead ix : In ix aead_G3b -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.
Lemma hka5_in_cnt ix : In ix cnt_G -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.
Lemma hka5_in_c1 ix : In ix ht4c_G1 -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.
Lemma hka5_in_rpf : In (rp_final_spec_of hka5_mp) hka5_Gr.
Proof. unfold hka5_Gr. rewrite !in_app_iff. simpl. tauto. Qed.
Lemma hka5_in_r ix : In ix (ht4r_G hka5_mp) -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.
Lemma hka5_in_wm ix : In ix ht4k_wm_G -> In ix hka5_Gr.
Proof. intros H. unfold hka5_Gr. rewrite !in_app_iff. tauto. Qed.

(* an entry of Gr covering s0 *)
Lemma hka5_cov1 i s s0 : In (i, s) hka5_Gr -> funspec_sub s s0 ->
  exists s', initial_world.find_id i Gw = Some s' /\ funspec_sub s' s0.
Proof. intros H S. exists s; split; auto. apply hka5_find_Gr; auto. Qed.

(* an entry of the BLAKE2s interface: Gb's entry is in Gw and covers it *)
Lemma hka5_b2s_entry i s0 : In (i, s0) blake2s_G3 ->
  exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s0.
Proof.
  intros H. unfold asm_covers in HcovB. rewrite Forall_forall in HcovB.
  destruct (HcovB _ H) as [s [Fs Sub]]; simpl in Fs.
  exists s; split; auto. apply hka5_find_Gr, hka5_in_b2s. apply initial_world.find_id_e; auto.
Qed.

Ltac hka5_inl := simpl; repeat first [left; reflexivity | right].

Lemma hka5_cov_env : asm_covers Gw (@asm_env.env_specs W).
Proof.
  apply asm_covers_incl; [apply hka5_norepet' |]. intros [i s] Hx. apply asm_E_incl; [exact Hx |].
  unfold asm_env.env_specs in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity.
Qed.

(* ---------- libc ---------- *)
Lemma hka5_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hka5_norepet.
  - intros a H. apply asm_Gr_incl, hka5_in_libc, H.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hka5_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    repeat (apply Forall_cons; [split; [apply hka5_cs_sub; hka5_in_cs |]; split; [hka5_varspecs |];
                                split; [apply CI | hka5_funs] |]); apply Forall_nil.
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma hka5_cov_b2s_imports cs : asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor]].
  - apply (hka5_cov1 _ (snd (@memcpy_spec Libc.CS))); [apply hka5_in_libc; hka5_inl | apply rp3_memcpy_sub].
  - apply (hka5_cov1 _ (snd (@memset_spec Libc.CS))); [apply hka5_in_libc; hka5_inl | apply rp3_memset_sub].
Qed.

Lemma hka5_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw blake2s_units3 blake2s_imports3 Gb HpB).
  - apply hka5_norepet.
  - intros a H. apply asm_Gr_incl, hka5_in_b2s, H.
  - rewrite HidB. unfold blake2s_units3.
    repeat (apply Forall_cons; [split; [apply hka5_cs_sub; hka5_in_cs |]; split; [hka5_varspecs |];
                                split; [apply hka5_cov_b2s_imports | hka5_funs] |]); apply Forall_nil.
Qed.

(* ---------- AEAD (the concrete piece) ---------- *)
Lemma hka5_cov_aead_imports cs : asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - apply (hka5_cov1 _ (snd (@memcpy_spec Libc.CS))); [apply hka5_in_libc; hka5_inl | apply rp3_memcpy_sub].
  - apply (hka5_cov1 _ (snd (@memset_spec Libc.CS))); [apply hka5_in_libc; hka5_inl | apply rp3_memset_sub].
  - destruct (hka5_b2s_entry _ _ (ltac:(unfold blake2s_G3; hka5_inl)
        : In (@memzero_explicit_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub | apply rp3_memzero_explicit_sub].
  - destruct (hka5_b2s_entry _ _ (ltac:(unfold blake2s_G3; hka5_inl)
        : In (@get_unaligned_le32_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub | apply rp3_get_unaligned_le32_sub].
  - apply (hka5_cov1 _ (snd (@crypto_memneq_spec Curve25519.CS)));
      [apply hka5_in_libc; unfold libc_G; hka5_inl | apply rp3_crypto_memneq_sub].
Qed.

Lemma hka5_bodies_aead : asm_bodies W p Gw aead_G3b.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3b (proj1 aead_piece3b.aead_piece3b)).
  - apply hka5_norepet.
  - intros a H. apply asm_Gr_incl, hka5_in_aead, H.
  - unfold aead_units3.
    repeat (apply Forall_cons; [split; [apply hka5_cs_sub; hka5_in_cs |]; split; [hka5_varspecs |];
                                split; [apply hka5_cov_aead_imports | hka5_funs] |]); apply Forall_nil.
Qed.

(* ---------- the counter ---------- *)
Lemma hka5_bodies_cnt : asm_bodies W p Gw cnt_G.
Proof.
  apply (asm_piece_lift W p Gw [u_counter] cnt_imports cnt_G cnt_piece3).
  - apply hka5_norepet.
  - intros a H. apply asm_Gr_incl, hka5_in_cnt, H.
  - constructor; [| constructor]. split; [apply hka5_cs_sub; hka5_in_cs |]. split; [hka5_varspecs |].
    split; [constructor | hka5_funs].
Qed.

(* ---------- the NULL-tolerant reference AEAD (ht4r) ---------- *)
Lemma hka5_bodies_ht4r : asm_bodies W p Gw (ht4r_G hka5_mp).
Proof.
  apply (asm_piece_lift W p Gw [u_ht4r] (fun _ => ht4c_G0 hka5_mp) (ht4r_G hka5_mp)
           (ht4r_piece hka5_mp WgNoise.proof.harness.prim_aead.haead_piece3.haead_hyps_ok)).
  - apply hka5_norepet.
  - intros a H. apply asm_Gr_incl, hka5_in_r, H.
  - constructor; [| constructor]. split; [apply ht4_prim_aead_sub_transport_keepalive |]. split; [constructor |].
    split; [| hka5_funs].
    apply asm_covers_incl; [apply hka5_norepet' |]. intros a H. apply asm_Gr_incl.
    unfold ht4c_G0 in H. apply in_app in H as [H|[<-|[]]]; [apply hka5_in_c1, H | apply hka5_in_rpf].
Qed.

(* ---------- the shared common.h functions ---------- *)
Lemma hka5_bodies_c1 : asm_bodies W p Gw ht4c_G1.
Proof.
  apply (asm_piece_lift W p Gw [u_ht4c] (fun _ => []) ht4c_G1 ht4c_piece1).
  - apply hka5_norepet.
  - intros a H. apply asm_Gr_incl, hka5_in_c1, H.
  - constructor; [| constructor]. split; [apply ht4_prim_aead_sub_transport_keepalive |]. split; [constructor |].
    split; [constructor | hka5_funs].
Qed.

Lemma hka5_bodies_rpf : asm_bodies W p Gw [rp_final_spec_of hka5_mp].
Proof.
  apply (asm_piece_lift W p Gw _ (fun _ => ht4c_G1) [rp_final_spec_of hka5_mp] ht4c_piece_rpf_keepalive).
  - apply hka5_norepet.
  - intros a [<-|[]]. apply asm_Gr_incl, hka5_in_rpf.
  - constructor; [| constructor]. split; [apply ht4_prim_aead_sub_transport_keepalive |]. split; [hka5_varspecs |].
    split; [| hka5_funs].
    apply asm_covers_incl; [apply hka5_norepet' |]. intros a H. apply asm_Gr_incl, hka5_in_c1, H.
Qed.

(* ---------- the transport.h shadow model ---------- *)
(* one body, proved at compspecs csu with varspecs Vu and context Gu, lifted into the whole program *)
Lemma hka5_lift (csu: compspecs) (Vu: varspecs) (Gu: funspecs) f ip :
  cspecs_sub csu W ->
  Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  Forall (fun it => complete_type (@cenv_cs csu) (snd it) = true) (fn_vars f) ->
  Forall (fun it => initial_world.find_id (fst it) (QPvarspecs p) = Some (snd it)) Vu ->
  asm_covers Gw Gu ->
  @semax_body Vu Gu csu f ip ->
  exists f', Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f')) /\
             @semax_body (QPvarspecs p) Gw W f' ip.
Proof.
  intros CS D C HV HG SB. exists f. split; auto.
  exact (asm_body_lift Vu (QPvarspecs p) Gu Gw f ip CS C hka5_norepet HV HG SB).
Qed.

(* an environment entry *)
Lemma hka5_cov_env1 i s : In (i, s) (@asm_env.env_specs W) -> asm_present_ext p i = true ->
  exists s', initial_world.find_id i Gw = Some s' /\ funspec_sub s' s.
Proof.
  intros H1 H2. exists s. split; [| apply funspec_sub_refl].
  apply initial_world.find_id_i; [apply asm_E_incl; auto | apply hka5_norepet'].
Qed.

Lemma hka5_cov_mem : asm_covers Gw ht4k_G_mem.
Proof.
  constructor; [| constructor; [| constructor]].
  - apply hka5_cov_env1; [hka5_inl | reflexivity].
  - apply hka5_cov_env1; [hka5_inl | reflexivity].
Qed.

Lemma hka5_cov_size : asm_covers Gw [nondet_size_spec].
Proof. constructor; [| constructor]. apply hka5_cov_env1; [hka5_inl | reflexivity]. Qed.

Lemma hka5_cov_nil : asm_covers Gw [].
Proof. constructor. Qed.

Ltac hka5_one_w B G :=
  refine (hka5_lift W ht4k_V0 _ _ _ (@cspecs_sub_refl W) _ _ _ _ B);
  [vm_compute; reflexivity | vm_compute; repeat constructor | constructor | exact G].

Lemma hka5_bodies_wm : asm_bodies W p Gw ht4k_wm_G.
Proof.
  pose proof WgNoise.proof.harness.transport_keepalive.ht4k_wm_body_a.ht4k_body_wm_init as A0.
  destruct WgNoise.proof.harness.transport_keepalive.ht4k_wm_body_a.ht4k_wm_bodies_a as (A1 & A2).
  pose proof WgNoise.proof.harness.transport_keepalive.ht4k_wm_body_c.ht4k_body_wm_commit as C1.
  destruct WgNoise.proof.harness.transport_keepalive.ht4k_rc_body.ht4k_rc_bodies as (R1 & R2 & R3 & D0).
  unfold asm_bodies, ht4k_wm_G.
  repeat apply Forall_cons; try apply Forall_nil.
  - hka5_one_w D0 hka5_cov_size.
  - hka5_one_w A0 hka5_cov_nil.
  - hka5_one_w A1 hka5_cov_nil.
  - hka5_one_w C1 hka5_cov_mem.
  - hka5_one_w A2 hka5_cov_mem.
  - hka5_one_w R1 hka5_cov_nil.
  - hka5_one_w R2 hka5_cov_nil.
  - hka5_one_w R3 hka5_cov_nil.
Qed.

(* ---------- main ---------- *)
Lemma hka5_cov_main_imports cs : asm_covers Gw (hka5_imports cs).
Proof.
  unfold hka5_imports. apply asm_covers_app; [apply hka5_cov_env |].
  apply asm_covers_app.
  2: { apply asm_covers_incl; [apply hka5_norepet' |]. intros a H. apply asm_Gr_incl, hka5_in_wm, H. }
  constructor; [apply (hka5_cov1 _ (snd chacha20poly1305_encrypt_spec3));
                [apply hka5_in_aead; unfold aead_G3b; hka5_inl | apply ht4_encrypt_sub] |].
  constructor; [apply (hka5_cov1 _ (snd chacha20poly1305_decrypt_spec3b));
                [apply hka5_in_aead; unfold aead_G3b; hka5_inl | apply ht4_decrypt_sub] |].
  constructor; [apply (hka5_cov1 _ (snd wg_counter_validate_spec));
                [apply hka5_in_cnt; unfold cnt_G; hka5_inl | apply ht4k_cnt_validate_sub] |].
  constructor; [apply (hka5_cov1 _ (snd ht4_check_failed_spec));
                [apply hka5_in_c1; unfold ht4c_G1; hka5_inl | apply funspec_sub_refl] |].
  constructor; [apply (hka5_cov1 _ (snd (@ht4_le32_store_spec W_prim_aead)));
                [apply hka5_in_c1; unfold ht4c_G1; hka5_inl | apply ht4c_le32_store_sub] |].
  constructor; [apply (hka5_cov1 _ (snd (@ht4_le64_store_spec W_prim_aead)));
                [apply hka5_in_c1; unfold ht4c_G1; hka5_inl | apply ht4c_le64_store_sub] |].
  constructor; [apply (hka5_cov1 _ (snd (ref_aead_decrypt_spec_n W_prim_aead hka5_mp)));
                [apply hka5_in_r; unfold ht4r_G; hka5_inl | apply ht4r_dec_sub] | constructor].
Qed.

Lemma hka5_bodies_main : asm_bodies W p Gw hka5_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hka5] hka5_imports hka5_G hka5_piece).
  - apply hka5_norepet.
  - intros a [<-|[]]. left; reflexivity.
  - constructor; [| constructor]. split; [apply cspecs_sub_refl |]. split; [hka5_varspecs |].
    split; [apply hka5_cov_main_imports | hka5_funs].
Qed.

Lemma hka5_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hka5_Gr.
Proof.
  unfold hka5_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [apply (rp3_cc_of_covers Gb blake2s_G3); auto; [apply HpB | repeat constructor] |].
  apply hka5_cc_dec; vm_compute; reflexivity.
Qed.

Lemma hka5_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hka5_post) :: hka5_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_main
          (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_libc
           (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_b2s
            (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_aead
             (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_cnt
              (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_c1
               (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_rpf
                (asm_bodies_incl _ _ _ _ _ _ hka5_bodies_ht4r hka5_bodies_wm (incl_refl _))
                (incl_refl _)) (incl_refl _)) (incl_refl _)) (incl_refl _)) (incl_refl _)) (incl_refl _))).
  intros a H. destruct H as [<-|H]; [left; reflexivity |]. right. exact H.
Qed.

Lemma hka5_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_transport_keepalive W W_transport_keepalive_eq hka5_cbc hka5_ext_ok
           hka5_post hka5_Gr hka5_ids hka5_IDS hka5_check hka5_cc hka5_bodies).
Qed.

End Assembly.

Theorem hka5_harness_safe : blake2s3_ok -> harness_safe WgNoise.contracts.x_transport_keepalive.whole_prog.
Proof.
  intros [Gb [Hp [Hi Hc]]]. exact (hka5_safe Gb Hp Hi Hc).
Qed.
