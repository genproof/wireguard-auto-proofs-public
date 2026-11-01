(* law prim_aead (harness/prim_aead.c) from the AEAD piece (aead_spec3.aead_G3), the BLAKE2s piece
   (hypothesis blake2s3_ok: memzero_explicit, get_unaligned_le32), the libc piece (libc_piece.v) and the
   harness piece (main and the harness's own functions, in the world W_prim_aead of wg3_worlds.v), assembled
   with asm_lib.asm_harness_safe. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require WgNoise.contracts.x_prim_aead.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_xcs3.
Require Import WgNoise.proof.harness.prim_aead.haead_piece3.

Local Notation p := WgNoise.contracts.x_prim_aead.whole_prog.
Local Notation W := W_prim_aead.

#[local] Instance ha3_cce_libc_b2s : change_composite_env Libc.CS Blake2s.CS.
Proof. make_cs_preserve Libc.CS Blake2s.CS. Defined.
#[local] Instance ha3_cce_libc_cookie : change_composite_env Libc.CS Cookie.CS.
Proof. make_cs_preserve Libc.CS Cookie.CS. Defined.

(* the AEAD units' compspecs, from the three owners' *)
Ltac ha3_cce a b := make_cs_preserve a b.
#[local] Instance ha3_cce_l1 : change_composite_env Libc.CS Chacha.CS. Proof. ha3_cce Libc.CS Chacha.CS. Defined.
#[local] Instance ha3_cce_l2 : change_composite_env Libc.CS ChachaBlock.CS. Proof. ha3_cce Libc.CS ChachaBlock.CS. Defined.
#[local] Instance ha3_cce_l3 : change_composite_env Libc.CS Poly1305.CS. Proof. ha3_cce Libc.CS Poly1305.CS. Defined.
#[local] Instance ha3_cce_l4 : change_composite_env Libc.CS Poly1305Donna32.CS. Proof. ha3_cce Libc.CS Poly1305Donna32.CS. Defined.
#[local] Instance ha3_cce_l5 : change_composite_env Libc.CS Chacha20poly1305.CS. Proof. ha3_cce Libc.CS Chacha20poly1305.CS. Defined.
#[local] Instance ha3_cce_l6 : change_composite_env Libc.CS Shim.CS. Proof. ha3_cce Libc.CS Shim.CS. Defined.
#[local] Instance ha3_cce_b1 : change_composite_env Blake2s.CS Chacha.CS. Proof. ha3_cce Blake2s.CS Chacha.CS. Defined.
#[local] Instance ha3_cce_b2 : change_composite_env Blake2s.CS ChachaBlock.CS. Proof. ha3_cce Blake2s.CS ChachaBlock.CS. Defined.
#[local] Instance ha3_cce_b3 : change_composite_env Blake2s.CS Poly1305.CS. Proof. ha3_cce Blake2s.CS Poly1305.CS. Defined.
#[local] Instance ha3_cce_b4 : change_composite_env Blake2s.CS Poly1305Donna32.CS. Proof. ha3_cce Blake2s.CS Poly1305Donna32.CS. Defined.
#[local] Instance ha3_cce_b5 : change_composite_env Blake2s.CS Chacha20poly1305.CS. Proof. ha3_cce Blake2s.CS Chacha20poly1305.CS. Defined.
#[local] Instance ha3_cce_b6 : change_composite_env Blake2s.CS Shim.CS. Proof. ha3_cce Blake2s.CS Shim.CS. Defined.
#[local] Instance ha3_cce_c1 : change_composite_env Curve25519.CS Chacha.CS. Proof. ha3_cce Curve25519.CS Chacha.CS. Defined.
#[local] Instance ha3_cce_c2 : change_composite_env Curve25519.CS ChachaBlock.CS. Proof. ha3_cce Curve25519.CS ChachaBlock.CS. Defined.
#[local] Instance ha3_cce_c3 : change_composite_env Curve25519.CS Poly1305.CS. Proof. ha3_cce Curve25519.CS Poly1305.CS. Defined.
#[local] Instance ha3_cce_c4 : change_composite_env Curve25519.CS Poly1305Donna32.CS. Proof. ha3_cce Curve25519.CS Poly1305Donna32.CS. Defined.
#[local] Instance ha3_cce_c5 : change_composite_env Curve25519.CS Chacha20poly1305.CS. Proof. ha3_cce Curve25519.CS Chacha20poly1305.CS. Defined.
#[local] Instance ha3_cce_c6 : change_composite_env Curve25519.CS Shim.CS. Proof. ha3_cce Curve25519.CS Shim.CS. Defined.

(* haead_G without main *)
Definition ha3_Gh : funspecs :=
  [check_failed_spec; bytes_eq_spec; bytes_copy_spec; bytes_set_spec; draw_size_spec; draw_u64_spec;
   le32_store_spec; le32_load_spec; le64_store_spec; le64_load_spec;
   rc_rotl_spec; rc_qr_spec; rc_rounds_spec; rc_setup_spec; ref_chacha20_block_spec; ref_hchacha20_spec;
   rp_add_spec; rp_init_spec; rp_mul_spec; rp_block_spec; rp_padded_spec; rp_final_spec;
   ref_aead_tag_spec; ref_chacha20_xor_spec; ref_aead_encrypt_spec; ref_aead_decrypt_spec;
   ref_xaead_encrypt_spec; ref_xaead_decrypt_spec; check_decrypt_any_spec].

(* the identifiers of the real specifications (Gb has blake2s_G3's) *)
Definition ha3_ids : list ident :=
  ltac:(let l := eval compute in (map fst (libc_G W ++ blake2s_G3 ++ aead_G3 ++ ha3_Gh)) in exact l).

Lemma ha3_check : asm_check W p ha3_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma ha3_cs_sub cs : In cs all_unit_cs -> cspecs_sub cs W.
Proof.
  destruct world_ok_prim_aead as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. intros H. apply HF. right; auto.
Qed.

Ltac ha3_in_cs := unfold all_unit_cs; simpl; repeat first [left; reflexivity | right].

Ltac ha3_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac ha3_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

Lemma ha3_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma ha3_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma ha3_cc_h : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) ha3_Gh.
Proof. repeat constructor. Qed.

Section Assembly.
Variable Gb: funspecs.
Variable Hpiece: piece_ok blake2s_units3 blake2s_imports3 Gb.
Variable Hids: map fst Gb = map fst blake2s_G3.
Variable Hcov: asm_covers Gb blake2s_G3.

(* the real specifications, main excepted *)
Definition ha3_Gr : funspecs := libc_G W ++ Gb ++ aead_G3 ++ ha3_Gh.

Local Notation Gw := (@asm_Gall W p haead_post ha3_Gr ha3_ids).

Lemma ha3_IDS : map fst ha3_Gr = ha3_ids.
Proof. unfold ha3_Gr. rewrite !map_app, Hids. reflexivity. Qed.

Lemma ha3_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply ha3_IDS | apply ha3_check]. Qed.

Lemma ha3_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply ha3_IDS | apply ha3_check]. Qed.

Lemma ha3_find_Gr i s : In (i, s) ha3_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply ha3_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma ha3_in_libc ix : In ix (libc_G W) -> In ix ha3_Gr.
Proof. intros H. unfold ha3_Gr. apply in_app; left; auto. Qed.
Lemma ha3_in_b2s ix : In ix Gb -> In ix ha3_Gr.
Proof. intros H. unfold ha3_Gr. apply in_app; right; apply in_app; left; auto. Qed.
Lemma ha3_in_aead ix : In ix aead_G3 -> In ix ha3_Gr.
Proof. intros H. unfold ha3_Gr. apply in_app; right; apply in_app; right; apply in_app; left; auto. Qed.
Lemma ha3_in_h ix : In ix ha3_Gh -> In ix ha3_Gr.
Proof. intros H. unfold ha3_Gr. apply in_app; right; apply in_app; right; apply in_app; right; auto. Qed.

(* an entry of the BLAKE2s interface: Gb's entry is in Gw and covers it *)
Lemma ha3_b2s_entry i s0 : In (i, s0) blake2s_G3 ->
  exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s0.
Proof.
  intros H. unfold asm_covers in Hcov. rewrite Forall_forall in Hcov.
  destruct (Hcov _ H) as [s [Fs Sub]]; simpl in Fs.
  exists s; split; auto. apply ha3_find_Gr, ha3_in_b2s. apply initial_world.find_id_e; auto.
Qed.

(* ---------- libc ---------- *)
Lemma ha3_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply ha3_norepet.
  - intros x Hx. apply asm_Gr_incl, ha3_in_libc; auto.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply ha3_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply ha3_cs_sub; ha3_in_cs |]; split; [ha3_varspecs |]; split; [apply CI | ha3_funs].
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma ha3_covers_b2s_imports cs (CCE: change_composite_env Libc.CS cs) :
  asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply ha3_find_Gr, ha3_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs CCE).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply ha3_find_Gr, ha3_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs CCE).
Qed.

Lemma ha3_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_cookie] blake2s_imports3 Gb Hpiece).
  - apply ha3_norepet.
  - intros x Hx. apply asm_Gr_incl, ha3_in_b2s; auto.
  - rewrite Hids.
    constructor; [| constructor; [| constructor]].
    + split; [apply ha3_cs_sub; ha3_in_cs |]. split; [ha3_varspecs |].
      split; [apply (ha3_covers_b2s_imports Blake2s.CS ha3_cce_libc_b2s) | ha3_funs].
    + split; [apply ha3_cs_sub; ha3_in_cs |]. split; [ha3_varspecs |].
      split; [apply (ha3_covers_b2s_imports Cookie.CS ha3_cce_libc_cookie) | ha3_funs].
Qed.

(* ---------- AEAD ---------- *)
Lemma ha3_covers_aead_imports cs (C1: change_composite_env Libc.CS cs) (C2: change_composite_env Blake2s.CS cs)
    (C3: change_composite_env Curve25519.CS cs) :
  asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply ha3_find_Gr, ha3_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs C1).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply ha3_find_Gr, ha3_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs C1).
  - destruct (ha3_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@memzero_explicit_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_memzero_explicit_sub Blake2s.CS cs C2).
  - destruct (ha3_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@get_unaligned_le32_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_get_unaligned_le32_sub Blake2s.CS cs C2).
  - exists (snd (@crypto_memneq_spec Curve25519.CS)). split.
    + apply ha3_find_Gr, ha3_in_libc. unfold libc_G; simpl; repeat (first [left; reflexivity | right]).
    + apply (@xa3_crypto_memneq_sub Curve25519.CS cs C3).
Qed.

Lemma ha3_bodies_aead (Ha: aead_piece3_ok) : asm_bodies W p Gw aead_G3.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3 Ha).
  - apply ha3_norepet.
  - intros x Hx. apply asm_Gr_incl, ha3_in_aead; auto.
  - unfold aead_units3.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    all: split; [apply ha3_cs_sub; ha3_in_cs |]; split; [ha3_varspecs |].
    all: split; [apply ha3_covers_aead_imports; typeclasses eauto | ha3_funs].
Qed.

(* ---------- the harness ---------- *)
Lemma ha3_bodies_harness : asm_bodies W p Gw haead_G.
Proof.
  apply (asm_piece_lift W p Gw [u_haead] haead_imports haead_G haead_piece3).
  - apply ha3_norepet.
  - intros x Hx. unfold haead_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_incl, ha3_in_h; unfold ha3_Gh; repeat (first [left; reflexivity | right]) ].
  - constructor; [| constructor]. split; [apply cspecs_sub_refl |]. split; [| split].
    + ha3_varspecs.
    + unfold haead_imports. apply asm_covers_app.
      * apply asm_covers_incl; [apply ha3_norepet' |].
        intros [i s] Hx. apply asm_E_incl; [| repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity].
        unfold asm_env.env_specs. repeat destruct Hx as [<-|Hx]; try contradiction; simpl; auto 7.
      * constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
        -- exists (snd chacha20poly1305_encrypt_spec3). split; [| apply hx3_encrypt_sub].
           apply ha3_find_Gr, ha3_in_aead. unfold aead_G3; repeat (first [left; reflexivity | right]).
        -- exists (snd chacha20poly1305_decrypt_spec3). split; [| apply hx3_decrypt_sub].
           apply ha3_find_Gr, ha3_in_aead. unfold aead_G3; repeat (first [left; reflexivity | right]).
        -- exists (snd xchacha20poly1305_encrypt_spec3). split; [| apply hx3_xencrypt_sub].
           apply ha3_find_Gr, ha3_in_aead. unfold aead_G3; repeat (first [left; reflexivity | right]).
        -- exists (snd xchacha20poly1305_decrypt_spec3). split; [| apply hx3_xdecrypt_sub].
           apply ha3_find_Gr, ha3_in_aead. unfold aead_G3; repeat (first [left; reflexivity | right]).
    + ha3_funs.
Qed.

Lemma ha3_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) ha3_Gr.
Proof.
  unfold ha3_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [| apply Forall_app; split; [repeat constructor | apply ha3_cc_h]].
  apply (xa3_cc_of_covers Gb blake2s_G3); auto; [apply Hpiece | repeat constructor].
Qed.

Lemma ha3_bodies (Ha: aead_piece3_ok) :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt haead_post) :: ha3_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _
           (asm_bodies_incl _ _ _ _ _ _ ha3_bodies_libc ha3_bodies_b2s (incl_refl _))
           (asm_bodies_incl _ _ _ _ _ _ (ha3_bodies_aead Ha) ha3_bodies_harness (incl_refl _))).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. apply in_app; right. unfold haead_G. repeat (first [left; reflexivity | right]).
  - unfold ha3_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; apply in_app; left; auto |].
    apply in_app in Hx as [Hx|Hx]; [left; apply in_app; right; auto |].
    right. apply in_app in Hx as [Hx|Hx]; [apply in_app; left; auto |].
    apply in_app; right. unfold ha3_Gh in Hx. unfold haead_G.
    repeat destruct Hx as [<-|Hx]; try contradiction; repeat (first [left; reflexivity | right]).
Qed.

Lemma ha3_safe (Ha: aead_piece3_ok) : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_prim_aead W W_prim_aead_eq ha3_cbc ha3_ext_ok haead_post
           ha3_Gr ha3_ids ha3_IDS ha3_check ha3_cc (ha3_bodies Ha)).
Qed.
End Assembly.

Theorem prim_aead_safe3 :
  aead_piece3_ok -> blake2s3_ok -> harness_safe WgNoise.contracts.x_prim_aead.whole_prog.
Proof.
  intros Ha [Gb [Hp [Hi Hc]]]. exact (ha3_safe Gb Hp Hi Hc Ha).
Qed.
