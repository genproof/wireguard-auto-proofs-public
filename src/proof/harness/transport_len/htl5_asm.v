(* the assembly,
   haead_safe3.v's (law prim_aead) with the transport layer:
   - libc piece, BLAKE2s piece (any Gb of blake2s3_ok: memzero_explicit / get_unaligned_le32 for the AEAD),
   - the CONCRETE AEAD piece aead_piece3b (any length; aead_model's aead_enc / aead_dec, which the reference
     ref_aead_decrypt computes) - the hypothesis aead3b_ok is not used,
   - the DataHeader piece dh4_piece (wg_validate_header_len),
   - the shared common.h bodies (ht4c_sub.v: ht4c_piece1, ht4c_piece_d, ht4c_piece_rpf_len) and the NULL-tolerant
     reference AEAD of (a hypothesis of the section: the piece of ht4r_G),
   - main (htl5_main.v), at W_transport_len, its imports covered by cs-change funspec_subs. *)
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
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3b.
Require WgNoise.proof.aead.aead_piece3b.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4c_sub.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.data_header.dh4_spec.
Require Import WgNoise.proof.data_header.dh4_body.
Require Import WgNoise.proof.harness.transport_len.htl5_defs.
Require Import WgNoise.proof.harness.transport_len.htl5_main.
Require WgNoise.contracts.x_transport_len.

Local Notation p := WgNoise.contracts.x_transport_len.whole_prog.
Local Notation W := W_transport_len.

#[local] Instance htl5_cce_libc_b2s : change_composite_env Libc.CS Blake2s.CS.
Proof. make_cs_preserve Libc.CS Blake2s.CS. Defined.
#[local] Instance htl5_cce_libc_cookie : change_composite_env Libc.CS Cookie.CS.
Proof. make_cs_preserve Libc.CS Cookie.CS. Defined.

Ltac htl5_cce a b := make_cs_preserve a b.
#[local] Instance htl5_cce_l1 : change_composite_env Libc.CS Chacha.CS. Proof. htl5_cce Libc.CS Chacha.CS. Defined.
#[local] Instance htl5_cce_l2 : change_composite_env Libc.CS ChachaBlock.CS. Proof. htl5_cce Libc.CS ChachaBlock.CS. Defined.
#[local] Instance htl5_cce_l3 : change_composite_env Libc.CS Poly1305.CS. Proof. htl5_cce Libc.CS Poly1305.CS. Defined.
#[local] Instance htl5_cce_l4 : change_composite_env Libc.CS Poly1305Donna32.CS. Proof. htl5_cce Libc.CS Poly1305Donna32.CS. Defined.
#[local] Instance htl5_cce_l5 : change_composite_env Libc.CS Chacha20poly1305.CS. Proof. htl5_cce Libc.CS Chacha20poly1305.CS. Defined.
#[local] Instance htl5_cce_l6 : change_composite_env Libc.CS Shim.CS. Proof. htl5_cce Libc.CS Shim.CS. Defined.
#[local] Instance htl5_cce_b1 : change_composite_env Blake2s.CS Chacha.CS. Proof. htl5_cce Blake2s.CS Chacha.CS. Defined.
#[local] Instance htl5_cce_b2 : change_composite_env Blake2s.CS ChachaBlock.CS. Proof. htl5_cce Blake2s.CS ChachaBlock.CS. Defined.
#[local] Instance htl5_cce_b3 : change_composite_env Blake2s.CS Poly1305.CS. Proof. htl5_cce Blake2s.CS Poly1305.CS. Defined.
#[local] Instance htl5_cce_b4 : change_composite_env Blake2s.CS Poly1305Donna32.CS. Proof. htl5_cce Blake2s.CS Poly1305Donna32.CS. Defined.
#[local] Instance htl5_cce_b5 : change_composite_env Blake2s.CS Chacha20poly1305.CS. Proof. htl5_cce Blake2s.CS Chacha20poly1305.CS. Defined.
#[local] Instance htl5_cce_b6 : change_composite_env Blake2s.CS Shim.CS. Proof. htl5_cce Blake2s.CS Shim.CS. Defined.
#[local] Instance htl5_cce_c1 : change_composite_env Curve25519.CS Chacha.CS. Proof. htl5_cce Curve25519.CS Chacha.CS. Defined.
#[local] Instance htl5_cce_c2 : change_composite_env Curve25519.CS ChachaBlock.CS. Proof. htl5_cce Curve25519.CS ChachaBlock.CS. Defined.
#[local] Instance htl5_cce_c3 : change_composite_env Curve25519.CS Poly1305.CS. Proof. htl5_cce Curve25519.CS Poly1305.CS. Defined.
#[local] Instance htl5_cce_c4 : change_composite_env Curve25519.CS Poly1305Donna32.CS. Proof. htl5_cce Curve25519.CS Poly1305Donna32.CS. Defined.
#[local] Instance htl5_cce_c5 : change_composite_env Curve25519.CS Chacha20poly1305.CS. Proof. htl5_cce Curve25519.CS Chacha20poly1305.CS. Defined.
#[local] Instance htl5_cce_c6 : change_composite_env Curve25519.CS Shim.CS. Proof. htl5_cce Curve25519.CS Shim.CS. Defined.

(* the harness's real specifications (main excepted) *)
Definition htl5_Gh : funspecs :=
  ht4c_G1 ++ [rp_final_spec_of htl5_mp] ++ ht4r_G htl5_mp ++ ht4c_Gdraw.

(* the identifiers of the real specifications (Gb has blake2s_G3's) *)
Definition htl5_ids : list ident :=
  ltac:(let l := eval compute in (map fst (libc_G W ++ blake2s_G3 ++ aead_G3b ++ dh4_G ++ htl5_Gh)) in exact l).

Lemma htl5_check : asm_check W p htl5_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma htl5_cs_sub cs : In cs (WgNoise.contracts.x_transport_len.Harness.CS :: DataHeader.CS :: all_unit_cs) ->
  cspecs_sub cs W.
Proof.
  destruct world_ok_transport_len as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply HF.
Qed.

Ltac htl5_in_cs := simpl; repeat first [left; reflexivity | right].

Ltac htl5_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac htl5_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

Lemma htl5_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma htl5_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma htl5_cc_h : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) (dh4_G ++ htl5_Gh).
Proof. repeat constructor. Qed.

Section Assembly.
Variable Gb: funspecs.
Variable Hpiece: piece_ok blake2s_units3 blake2s_imports3 Gb.
Variable Hids: map fst Gb = map fst blake2s_G3.
Variable Hcov: asm_covers Gb blake2s_G3.
(* NULL-tolerant reference AEAD *)
Variable Hr4: piece_ok [u_ht4r] (fun _ => ht4c_G0 htl5_mp) (ht4r_G htl5_mp).
(* the cs-change of ref_aead_decrypt's specification *)
Variable Hdec: funspec_sub (snd (ref_aead_decrypt_spec_n W_prim_aead htl5_mp)) (snd (ref_aead_decrypt_spec_n W htl5_mp)).

Definition htl5_Gr : funspecs := libc_G W ++ Gb ++ aead_G3b ++ dh4_G ++ htl5_Gh.

Local Notation Gw := (@asm_Gall W p htl5_post htl5_Gr htl5_ids).

Lemma htl5_IDS : map fst htl5_Gr = htl5_ids.
Proof. unfold htl5_Gr. rewrite !map_app, Hids. reflexivity. Qed.

Lemma htl5_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply htl5_IDS | apply htl5_check]. Qed.

Lemma htl5_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply htl5_IDS | apply htl5_check]. Qed.

Lemma htl5_find_Gr i s : In (i, s) htl5_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply htl5_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma htl5_in_libc ix : In ix (libc_G W) -> In ix htl5_Gr.
Proof. intros H. unfold htl5_Gr. apply in_app; left; auto. Qed.
Lemma htl5_in_b2s ix : In ix Gb -> In ix htl5_Gr.
Proof. intros H. unfold htl5_Gr. apply in_app; right; apply in_app; left; auto. Qed.
Lemma htl5_in_aead ix : In ix aead_G3b -> In ix htl5_Gr.
Proof. intros H. unfold htl5_Gr. apply in_app; right; apply in_app; right; apply in_app; left; auto. Qed.
Lemma htl5_in_dh ix : In ix dh4_G -> In ix htl5_Gr.
Proof.
  intros H. unfold htl5_Gr. apply in_app; right; apply in_app; right; apply in_app; right; apply in_app; left; auto.
Qed.
Lemma htl5_in_h ix : In ix htl5_Gh -> In ix htl5_Gr.
Proof.
  intros H. unfold htl5_Gr. apply in_app; right; apply in_app; right; apply in_app; right; apply in_app; right; auto.
Qed.

(* an entry of the BLAKE2s interface: Gb's entry is in Gw and covers it *)
Lemma htl5_b2s_entry i s0 : In (i, s0) blake2s_G3 ->
  exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s0.
Proof.
  intros H. unfold asm_covers in Hcov. rewrite Forall_forall in Hcov.
  destruct (Hcov _ H) as [s [Fs Sub]]; simpl in Fs.
  exists s; split; auto. apply htl5_find_Gr, htl5_in_b2s. apply initial_world.find_id_e; auto.
Qed.

(* ---------- libc ---------- *)
Lemma htl5_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_libc; auto.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply htl5_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply htl5_cs_sub; htl5_in_cs |]; split; [htl5_varspecs |]; split; [apply CI | htl5_funs].
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma htl5_covers_b2s_imports cs (CCE: change_composite_env Libc.CS cs) :
  asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply htl5_find_Gr, htl5_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs CCE).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply htl5_find_Gr, htl5_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs CCE).
Qed.

Lemma htl5_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_cookie] blake2s_imports3 Gb Hpiece).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_b2s; auto.
  - rewrite Hids.
    constructor; [| constructor; [| constructor]].
    + split; [apply htl5_cs_sub; htl5_in_cs |]. split; [htl5_varspecs |].
      split; [apply (htl5_covers_b2s_imports Blake2s.CS htl5_cce_libc_b2s) | htl5_funs].
    + split; [apply htl5_cs_sub; htl5_in_cs |]. split; [htl5_varspecs |].
      split; [apply (htl5_covers_b2s_imports Cookie.CS htl5_cce_libc_cookie) | htl5_funs].
Qed.

(* ---------- AEAD (the concrete piece) ---------- *)
Lemma htl5_covers_aead_imports cs (C1: change_composite_env Libc.CS cs) (C2: change_composite_env Blake2s.CS cs)
    (C3: change_composite_env Curve25519.CS cs) :
  asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply htl5_find_Gr, htl5_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs C1).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply htl5_find_Gr, htl5_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs C1).
  - destruct (htl5_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@memzero_explicit_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_memzero_explicit_sub Blake2s.CS cs C2).
  - destruct (htl5_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@get_unaligned_le32_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_get_unaligned_le32_sub Blake2s.CS cs C2).
  - exists (snd (@crypto_memneq_spec Curve25519.CS)). split.
    + apply htl5_find_Gr, htl5_in_libc. unfold libc_G; simpl; repeat (first [left; reflexivity | right]).
    + apply (@xa3_crypto_memneq_sub Curve25519.CS cs C3).
Qed.

Lemma htl5_bodies_aead : asm_bodies W p Gw aead_G3b.
Proof.
  destruct WgNoise.proof.aead.aead_piece3b.aead_piece3b as [Ha _].
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3b Ha).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_aead; auto.
  - unfold aead_units3.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    all: split; [apply htl5_cs_sub; htl5_in_cs |]; split; [htl5_varspecs |].
    all: split; [apply htl5_covers_aead_imports; typeclasses eauto | htl5_funs].
Qed.

(* ---------- DataHeader ---------- *)
Lemma htl5_bodies_dh : asm_bodies W p Gw dh4_G.
Proof.
  apply (asm_piece_lift W p Gw [u_data_header] dh4_imports dh4_G dh4_piece).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_dh; auto.
  - constructor; [| constructor].
    split; [apply htl5_cs_sub; htl5_in_cs |]. split; [htl5_varspecs |].
    split; [constructor | htl5_funs].
Qed.

(* ---------- the shared common.h bodies ---------- *)
Lemma htl5_prim_sub : cspecs_sub W_prim_aead W.
Proof. exact ht4_prim_aead_sub_transport_len. Qed.

Lemma htl5_covers_G1 : asm_covers Gw ht4c_G1.
Proof.
  apply asm_covers_incl; [apply htl5_norepet' |].
  intros x Hx. apply asm_Gr_incl, htl5_in_h. unfold htl5_Gh. apply in_app; left; auto.
Qed.

Lemma htl5_bodies_c1 : asm_bodies W p Gw ht4c_G1.
Proof.
  apply (asm_piece_lift W p Gw [u_ht4c] (fun _ => []) ht4c_G1 ht4c_piece1).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_h. unfold htl5_Gh. apply in_app; left; auto.
  - constructor; [| constructor].
    split; [apply htl5_prim_sub |]. split; [constructor |].
    split; [constructor | htl5_funs].
Qed.

Lemma htl5_bodies_cd : asm_bodies W p Gw ht4c_Gdraw.
Proof.
  apply (asm_piece_lift W p Gw [u_ht4c] (fun _ => ht4c_Gd) ht4c_Gdraw ht4c_piece_d).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_h. unfold htl5_Gh.
    apply in_app; right; apply in_app; right; apply in_app; right; auto.
  - constructor; [| constructor].
    split; [apply htl5_prim_sub |]. split; [constructor |].
    split; [| htl5_funs].
    apply asm_covers_incl; [apply htl5_norepet' |].
    intros [i s] Hx. apply asm_E_incl; [| repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity].
    unfold asm_env.env_specs. repeat destruct Hx as [<-|Hx]; try contradiction; simpl; auto 7.
Qed.

Lemma htl5_bodies_rpf : asm_bodies W p Gw [rp_final_spec_of htl5_mp].
Proof.
  apply (asm_piece_lift W p Gw _ (fun _ => ht4c_G1) [rp_final_spec_of htl5_mp] ht4c_piece_rpf_len).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_h. unfold htl5_Gh. apply in_app; right; apply in_app; left; auto.
  - constructor; [| constructor].
    split; [apply htl5_prim_sub |]. split; [htl5_varspecs |].
    split; [apply htl5_covers_G1 | htl5_funs].
Qed.

Lemma htl5_bodies_r4 : asm_bodies W p Gw (ht4r_G htl5_mp).
Proof.
  apply (asm_piece_lift W p Gw [u_ht4r] (fun _ => ht4c_G0 htl5_mp) (ht4r_G htl5_mp) Hr4).
  - apply htl5_norepet.
  - intros x Hx. apply asm_Gr_incl, htl5_in_h. unfold htl5_Gh.
    apply in_app; right; apply in_app; right; apply in_app; left; auto.
  - constructor; [| constructor].
    split; [apply htl5_prim_sub |]. split; [constructor |].
    split; [| htl5_funs].
    apply asm_covers_incl; [apply htl5_norepet' |].
    intros x Hx. apply asm_Gr_incl, htl5_in_h. unfold htl5_Gh, ht4c_G0 in *.
    apply in_app in Hx as [Hx|Hx]; [apply in_app; left; auto | apply in_app; right; apply in_app; left; auto].
Qed.

(* ---------- main ---------- *)
Definition u_htl5 : unit_ctx := mk_unit W htl5_V WgNoise.harness.x_transport_len.code.prog.

Lemma htl5_main_piece : piece_ok [u_htl5] (fun _ => htl5_imports) [htl5_main_spec].
Proof.
  split; [repeat constructor; simpl; intuition |].
  repeat constructor. exists u_htl5; split; [left; reflexivity |].
  exists WgNoise.harness.x_transport_len.code.f_main; split; [reflexivity |].
  exact htl5_main_body.
Qed.

Lemma htl5_covers_imports : asm_covers Gw htl5_imports.
Proof.
  unfold htl5_imports. apply asm_covers_app.
  - apply asm_covers_incl; [apply htl5_norepet' |].
    intros [i s] Hx. apply asm_E_incl; [| repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity].
    unfold asm_env.env_specs. repeat destruct Hx as [<-|Hx]; try contradiction; simpl; auto 7.
  - assert (IH: forall ix, In ix htl5_Gh -> In ix htl5_Gr) by exact htl5_in_h.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [|
      constructor; [| constructor; [| constructor; [| constructor]]]]]]]]].
    + exists (snd ht4_check_failed_spec). split; [| apply funspec_sub_refl].
      apply htl5_find_Gr, IH. unfold htl5_Gh, ht4c_G1. left; reflexivity.
    + exists (snd ht4_draw_size_spec). split; [| apply funspec_sub_refl].
      apply htl5_find_Gr, IH. unfold htl5_Gh, ht4c_Gdraw. simpl; repeat (first [left; reflexivity | right]).
    + exists (snd ht4_draw_u64_spec). split; [| apply funspec_sub_refl].
      apply htl5_find_Gr, IH. unfold htl5_Gh, ht4c_Gdraw. simpl; repeat (first [left; reflexivity | right]).
    + exists (snd (@ht4_le32_store_spec W_prim_aead)). split; [| apply ht4c_le32_store_sub].
      apply htl5_find_Gr, IH. unfold htl5_Gh, ht4c_G1. simpl; repeat (first [left; reflexivity | right]).
    + exists (snd (@ht4_bytes_eq_spec W_prim_aead)). split; [| apply ht4c_bytes_eq_sub].
      apply htl5_find_Gr, IH. unfold htl5_Gh, ht4c_G1. simpl; repeat (first [left; reflexivity | right]).
    + exists (snd wg_validate_header_len_spec). split; [| apply funspec_sub_refl].
      apply htl5_find_Gr, htl5_in_dh. left; reflexivity.
    + exists (snd chacha20poly1305_encrypt_spec3). split; [| apply ht4_encrypt_sub].
      apply htl5_find_Gr, htl5_in_aead. unfold aead_G3b; simpl; repeat (first [left; reflexivity | right]).
    + exists (snd chacha20poly1305_decrypt_spec3b). split; [| apply ht4_decrypt_sub].
      apply htl5_find_Gr, htl5_in_aead. unfold aead_G3b; simpl; repeat (first [left; reflexivity | right]).
    + exists (snd (ref_aead_decrypt_spec_n W_prim_aead htl5_mp)). split; [| exact Hdec].
      apply htl5_find_Gr, IH. unfold htl5_Gh, ht4r_G. simpl; repeat (first [left; reflexivity | right]).
Qed.

Lemma htl5_bodies_main : asm_bodies W p Gw [htl5_main_spec].
Proof.
  apply (asm_piece_lift W p Gw [u_htl5] (fun _ => htl5_imports) [htl5_main_spec] htl5_main_piece).
  - apply htl5_norepet.
  - intros x Hx. destruct Hx as [<-|[]]. left; reflexivity.
  - constructor; [| constructor].
    split; [apply cspecs_sub_refl |]. split; [htl5_varspecs |].
    split; [apply htl5_covers_imports | htl5_funs].
Qed.

Lemma htl5_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) htl5_Gr.
Proof.
  unfold htl5_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [| apply Forall_app; split; [repeat constructor | apply htl5_cc_h]].
  apply (xa3_cc_of_covers Gb blake2s_G3); auto; [apply Hpiece | repeat constructor].
Qed.

Lemma htl5_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt htl5_post) :: htl5_Gr).
Proof.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_r4 htl5_bodies_cd (incl_refl _)) as B1.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_rpf B1 (incl_refl _)) as B2.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_c1 B2 (incl_refl _)) as B3.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_dh B3 (incl_refl _)) as B4.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_aead B4 (incl_refl _)) as B5.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_b2s B5 (incl_refl _)) as B6.
  pose proof (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_libc B6 (incl_refl _)) as B7.
  apply (asm_bodies_incl _ _ _ _ _ _ htl5_bodies_main B7).
  intros x [<-|Hx]; [left; reflexivity |]. right. exact Hx.
Qed.

Lemma htl5_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_transport_len W W_transport_len_eq htl5_cbc htl5_ext_ok htl5_post
           htl5_Gr htl5_ids htl5_IDS htl5_check htl5_cc htl5_bodies).
Qed.
End Assembly.
