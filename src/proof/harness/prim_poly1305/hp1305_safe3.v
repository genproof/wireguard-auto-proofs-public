(* law prim_poly1305 (harness/prim_poly1305.c) from the AEAD piece (aead_spec3.aead_G3), the BLAKE2s piece
   (hypothesis blake2s3_ok: memzero_explicit, get_unaligned_le32), the libc piece (libc_piece.v) and the
   harness piece (main and the harness's own functions, in the world W_prim_poly1305 of wg3_worlds.v), assembled
   with asm_lib.asm_harness_safe. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require WgNoise.contracts.x_prim_poly1305.
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
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_piece3.

Local Notation p := WgNoise.contracts.x_prim_poly1305.whole_prog.
Local Notation W := W_prim_poly1305.

#[local] Instance hp3_cce_libc_b2s : change_composite_env Libc.CS Blake2s.CS.
Proof. make_cs_preserve Libc.CS Blake2s.CS. Defined.
#[local] Instance hp3_cce_libc_cookie : change_composite_env Libc.CS Cookie.CS.
Proof. make_cs_preserve Libc.CS Cookie.CS. Defined.

(* the AEAD units' compspecs, from the three owners' *)
Ltac hp3_cce a b := make_cs_preserve a b.
#[local] Instance hp3_cce_l1 : change_composite_env Libc.CS Chacha.CS. Proof. hp3_cce Libc.CS Chacha.CS. Defined.
#[local] Instance hp3_cce_l2 : change_composite_env Libc.CS ChachaBlock.CS. Proof. hp3_cce Libc.CS ChachaBlock.CS. Defined.
#[local] Instance hp3_cce_l3 : change_composite_env Libc.CS Poly1305.CS. Proof. hp3_cce Libc.CS Poly1305.CS. Defined.
#[local] Instance hp3_cce_l4 : change_composite_env Libc.CS Poly1305Donna32.CS. Proof. hp3_cce Libc.CS Poly1305Donna32.CS. Defined.
#[local] Instance hp3_cce_l5 : change_composite_env Libc.CS Chacha20poly1305.CS. Proof. hp3_cce Libc.CS Chacha20poly1305.CS. Defined.
#[local] Instance hp3_cce_l6 : change_composite_env Libc.CS Shim.CS. Proof. hp3_cce Libc.CS Shim.CS. Defined.
#[local] Instance hp3_cce_b1 : change_composite_env Blake2s.CS Chacha.CS. Proof. hp3_cce Blake2s.CS Chacha.CS. Defined.
#[local] Instance hp3_cce_b2 : change_composite_env Blake2s.CS ChachaBlock.CS. Proof. hp3_cce Blake2s.CS ChachaBlock.CS. Defined.
#[local] Instance hp3_cce_b3 : change_composite_env Blake2s.CS Poly1305.CS. Proof. hp3_cce Blake2s.CS Poly1305.CS. Defined.
#[local] Instance hp3_cce_b4 : change_composite_env Blake2s.CS Poly1305Donna32.CS. Proof. hp3_cce Blake2s.CS Poly1305Donna32.CS. Defined.
#[local] Instance hp3_cce_b5 : change_composite_env Blake2s.CS Chacha20poly1305.CS. Proof. hp3_cce Blake2s.CS Chacha20poly1305.CS. Defined.
#[local] Instance hp3_cce_b6 : change_composite_env Blake2s.CS Shim.CS. Proof. hp3_cce Blake2s.CS Shim.CS. Defined.
#[local] Instance hp3_cce_c1 : change_composite_env Curve25519.CS Chacha.CS. Proof. hp3_cce Curve25519.CS Chacha.CS. Defined.
#[local] Instance hp3_cce_c2 : change_composite_env Curve25519.CS ChachaBlock.CS. Proof. hp3_cce Curve25519.CS ChachaBlock.CS. Defined.
#[local] Instance hp3_cce_c3 : change_composite_env Curve25519.CS Poly1305.CS. Proof. hp3_cce Curve25519.CS Poly1305.CS. Defined.
#[local] Instance hp3_cce_c4 : change_composite_env Curve25519.CS Poly1305Donna32.CS. Proof. hp3_cce Curve25519.CS Poly1305Donna32.CS. Defined.
#[local] Instance hp3_cce_c5 : change_composite_env Curve25519.CS Chacha20poly1305.CS. Proof. hp3_cce Curve25519.CS Chacha20poly1305.CS. Defined.
#[local] Instance hp3_cce_c6 : change_composite_env Curve25519.CS Shim.CS. Proof. hp3_cce Curve25519.CS Shim.CS. Defined.

Definition hp3_Gh : funspecs := filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) hp1305_G.

(* the identifiers of the real specifications (Gb has blake2s_G3's) *)
Definition hp3_ids : list ident :=
  ltac:(let l := eval compute in (map fst (libc_G W ++ blake2s_G3 ++ aead_G3 ++ hp3_Gh)) in exact l).

Lemma hp3_check : asm_check W p hp3_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hp3_cs_sub cs : In cs all_unit_cs -> cspecs_sub cs W.
Proof.
  destruct world_ok_prim_poly1305 as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. intros H. apply HF. right; auto.
Qed.

Ltac hp3_in_cs := unfold all_unit_cs; simpl; repeat first [left; reflexivity | right].

Ltac hp3_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hp3_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

Lemma hp3_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma hp3_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Section Assembly.
Variable Gb: funspecs.
Variable Hpiece: piece_ok blake2s_units3 blake2s_imports3 Gb.
Variable Hids: map fst Gb = map fst blake2s_G3.
Variable Hcov: asm_covers Gb blake2s_G3.

(* the real specifications, main excepted *)
Definition hp3_Gr : funspecs := libc_G W ++ Gb ++ aead_G3 ++ hp3_Gh.

Local Notation Gw := (@asm_Gall W p hp1305_post hp3_Gr hp3_ids).

Lemma hp3_IDS : map fst hp3_Gr = hp3_ids.
Proof. unfold hp3_Gr. rewrite !map_app, Hids. reflexivity. Qed.

Lemma hp3_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply hp3_IDS | apply hp3_check]. Qed.

Lemma hp3_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply hp3_IDS | apply hp3_check]. Qed.

Lemma hp3_find_Gr i s : In (i, s) hp3_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply hp3_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma hp3_in_libc ix : In ix (libc_G W) -> In ix hp3_Gr.
Proof. intros H. unfold hp3_Gr. apply in_app; left; auto. Qed.
Lemma hp3_in_b2s ix : In ix Gb -> In ix hp3_Gr.
Proof. intros H. unfold hp3_Gr. apply in_app; right; apply in_app; left; auto. Qed.
Lemma hp3_in_aead ix : In ix aead_G3 -> In ix hp3_Gr.
Proof. intros H. unfold hp3_Gr. apply in_app; right; apply in_app; right; apply in_app; left; auto. Qed.
Lemma hp3_in_h ix : In ix hp3_Gh -> In ix hp3_Gr.
Proof. intros H. unfold hp3_Gr. apply in_app; right; apply in_app; right; apply in_app; right; auto. Qed.

(* an entry of the BLAKE2s interface: Gb's entry is in Gw and covers it *)
Lemma hp3_b2s_entry i s0 : In (i, s0) blake2s_G3 ->
  exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s0.
Proof.
  intros H. unfold asm_covers in Hcov. rewrite Forall_forall in Hcov.
  destruct (Hcov _ H) as [s [Fs Sub]]; simpl in Fs.
  exists s; split; auto. apply hp3_find_Gr, hp3_in_b2s. apply initial_world.find_id_e; auto.
Qed.

(* ---------- libc ---------- *)
Lemma hp3_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply hp3_norepet.
  - intros x Hx. apply asm_Gr_incl, hp3_in_libc; auto.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply hp3_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply hp3_cs_sub; hp3_in_cs |]; split; [hp3_varspecs |]; split; [apply CI | hp3_funs].
Qed.

(* ---------- BLAKE2s ---------- *)
Lemma hp3_covers_b2s_imports cs (CCE: change_composite_env Libc.CS cs) :
  asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply hp3_find_Gr, hp3_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs CCE).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply hp3_find_Gr, hp3_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs CCE).
Qed.

Lemma hp3_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_cookie] blake2s_imports3 Gb Hpiece).
  - apply hp3_norepet.
  - intros x Hx. apply asm_Gr_incl, hp3_in_b2s; auto.
  - rewrite Hids.
    constructor; [| constructor; [| constructor]].
    + split; [apply hp3_cs_sub; hp3_in_cs |]. split; [hp3_varspecs |].
      split; [apply (hp3_covers_b2s_imports Blake2s.CS hp3_cce_libc_b2s) | hp3_funs].
    + split; [apply hp3_cs_sub; hp3_in_cs |]. split; [hp3_varspecs |].
      split; [apply (hp3_covers_b2s_imports Cookie.CS hp3_cce_libc_cookie) | hp3_funs].
Qed.

(* ---------- AEAD ---------- *)
Lemma hp3_covers_aead_imports cs (C1: change_composite_env Libc.CS cs) (C2: change_composite_env Blake2s.CS cs)
    (C3: change_composite_env Curve25519.CS cs) :
  asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply hp3_find_Gr, hp3_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs C1).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply hp3_find_Gr, hp3_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs C1).
  - destruct (hp3_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@memzero_explicit_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_memzero_explicit_sub Blake2s.CS cs C2).
  - destruct (hp3_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@get_unaligned_le32_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_get_unaligned_le32_sub Blake2s.CS cs C2).
  - exists (snd (@crypto_memneq_spec Curve25519.CS)). split.
    + apply hp3_find_Gr, hp3_in_libc. unfold libc_G; simpl; repeat (first [left; reflexivity | right]).
    + apply (@xa3_crypto_memneq_sub Curve25519.CS cs C3).
Qed.

Lemma hp3_bodies_aead (Ha: aead_piece3_ok) : asm_bodies W p Gw aead_G3.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3 Ha).
  - apply hp3_norepet.
  - intros x Hx. apply asm_Gr_incl, hp3_in_aead; auto.
  - unfold aead_units3.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    all: split; [apply hp3_cs_sub; hp3_in_cs |]; split; [hp3_varspecs |].
    all: split; [apply hp3_covers_aead_imports; typeclasses eauto | hp3_funs].
Qed.

(* ---------- the harness ---------- *)
Lemma hp3_bodies_harness : asm_bodies W p Gw hp1305_G.
Proof.
  apply (asm_piece_lift W p Gw [u_hp1305] hp1305_imports hp1305_G hp1305_piece3).
  - apply hp3_norepet.
  - intros x Hx. unfold hp1305_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_incl, hp3_in_h; apply filter_In; split;
                [unfold hp1305_G; repeat (first [left; reflexivity | right]) | reflexivity] ].
  - constructor; [| constructor]. split; [apply cspecs_sub_refl |]. split; [| split].
    + hp3_varspecs.
    + apply asm_covers_incl; [apply hp3_norepet' |].
      intros [i s] Hx. apply in_app in Hx as [Hx|Hx].
      * apply asm_E_incl; [| repeat destruct Hx as [Hx|Hx]; try contradiction; inv Hx; reflexivity].
        unfold asm_env.env_specs. repeat destruct Hx as [<-|Hx]; try contradiction; simpl; auto 7.
      * apply asm_Gr_incl, hp3_in_aead.
        repeat destruct Hx as [<-|Hx]; try contradiction; unfold aead_G3; repeat (first [left; reflexivity | right]).
    + hp3_funs.
Qed.

Lemma hp3_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) hp3_Gr.
Proof.
  unfold hp3_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [| repeat constructor].
  apply (xa3_cc_of_covers Gb blake2s_G3); auto; [apply Hpiece | repeat constructor].
Qed.

Lemma hp3_bodies (Ha: aead_piece3_ok) :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt hp1305_post) :: hp3_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _
           (asm_bodies_incl _ _ _ _ _ _ hp3_bodies_libc hp3_bodies_b2s (incl_refl _))
           (asm_bodies_incl _ _ _ _ _ _ (hp3_bodies_aead Ha) hp3_bodies_harness (incl_refl _))).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. apply in_app; right. unfold hp1305_G. repeat (first [left; reflexivity | right]).
  - unfold hp3_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; apply in_app; left; auto |].
    apply in_app in Hx as [Hx|Hx]; [left; apply in_app; right; auto |].
    right. apply in_app in Hx as [Hx|Hx]; [apply in_app; left; auto |].
    apply in_app; right. apply filter_In in Hx as [Hx _]; auto.
Qed.

Lemma hp3_safe (Ha: aead_piece3_ok) : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_prim_poly1305 W W_prim_poly1305_eq hp3_cbc hp3_ext_ok hp1305_post
           hp3_Gr hp3_ids hp3_IDS hp3_check hp3_cc (hp3_bodies Ha)).
Qed.
End Assembly.

Theorem prim_poly1305_safe3 :
  aead_piece3_ok -> blake2s3_ok -> harness_safe WgNoise.contracts.x_prim_poly1305.whole_prog.
Proof.
  intros Ha [Gb [Hp [Hi Hc]]]. exact (hp3_safe Gb Hp Hi Hc Ha).
Qed.
