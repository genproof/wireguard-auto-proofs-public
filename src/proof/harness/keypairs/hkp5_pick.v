(* law keypairs: the bodies of pick_live, pick_held and warn_same. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.keypairs.hkp5_reps.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

(* a segment of the live list whose last node points to tl (v1: hkp4_pick.v) *)
Local Open Scope logic.
Fixpoint hk5p_seg (ML: list (val * hk5_mk)) (tl: val) : mpred :=
  match ML with
  | [] => emp
  | (m, M) :: ML' => hk5_node m M (match ML' with [] => tl | (a, _) :: _ => a end) * hk5p_seg ML' tl
  end.

Lemma hk5p_split : forall ML1 ML2,
  hk5_mklist (ML1 ++ ML2) = hk5p_seg ML1 (hk5_head ML2) * hk5_mklist ML2.
Proof.
  induction ML1 as [|[a A] ML1 IH]; intros; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IH, sepcon_assoc.
    replace (hk5_head (ML1 ++ ML2)) with (match ML1 with [] => hk5_head ML2 | (a0, _) :: _ => a0 end);
      [reflexivity|].
    destruct ML1 as [|[b B] ?]; reflexivity.
Qed.

Lemma hk5p_seg_all : forall ML, hk5p_seg ML (hk5_head (@nil (val * hk5_mk))) * hk5_mklist [] |-- hk5_mklist ML.
Proof.
  intros. rewrite <- hk5p_split, app_nil_r. apply derives_refl.
Qed.

Lemma hk5p_seg_snoc : forall ML1 m M tl,
  hk5p_seg (ML1 ++ [(m, M)]) tl = hk5p_seg ML1 m * hk5_node m M tl.
Proof.
  induction ML1 as [|[a A] ML1 IH]; intros; simpl.
  - rewrite emp_sepcon, sepcon_emp; auto.
  - rewrite IH, sepcon_assoc.
    replace (match ML1 ++ [(m, M)] with [] => tl | (a0, _) :: _ => a0 end)
      with (match ML1 with [] => m | (a0, _) :: _ => a0 end); [reflexivity|].
    destruct ML1 as [|[b B] ?]; reflexivity.
Qed.

Lemma hk5p_fold : forall ML ML1 m0 M0 ML2, ML = ML1 ++ (m0, M0) :: ML2 ->
  hk5p_seg ML1 m0 * hk5_node m0 M0 (hk5_head ML2) * hk5_mklist ML2 |-- hk5_mklist ML.
Proof.
  intros; subst. rewrite hk5p_split. simpl hk5_head. simpl hk5_mklist. rewrite sepcon_assoc. apply derives_refl.
Qed.

Lemma hk5p_node_valid_pointer : forall m M nx, hk5_node m M nx |-- valid_pointer m.
Proof.
  intros. unfold hk5_node. entailer!.
Qed.
#[local] Hint Resolve hk5p_node_valid_pointer : valid_pointer.

Lemma hk5p_node_fold : forall m M nx, Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5 (hk5_mk_val M nx) m * malloc_token Ews t_mk5 m |-- hk5_node m M nx.
Proof.
  intros. unfold hk5_node. entailer!.
Qed.

Lemma hk5p_node_local_facts : forall m M nx, hk5_node m M nx |-- !! isptr m.
Proof.
  intros. unfold hk5_node. entailer!.
Qed.
#[local] Hint Resolve hk5p_node_local_facts : saturate_local.

Lemma hk5p_mklist_local_facts : forall ML, hk5_mklist ML |-- !! is_pointer_or_null (hk5_head ML).
Proof.
  intros [|[m M] ML]; simpl hk5_mklist; simpl hk5_head.
  - entailer!.
  - unfold hk5_node. entailer!.
Qed.
#[local] Hint Resolve hk5p_mklist_local_facts : saturate_local.

Local Open Scope Z_scope.

Lemma hkp5_pick_live_body :
  @semax_body hkp5_V hk5_Gpick W_keypairs KC.f_pick_live hk5_pick_live_spec.
Proof.
  start_function.
  assert_PROP (is_pointer_or_null (hk5_head ML)) as Hhd.
  { destruct ML as [|[m M] ML']; simpl hk5_head; [entailer!|]. simpl hk5_mklist. unfold hk5_node. Intros.
    entailer!. }
  forward.
  forward_call tt.
  Intros n.
  destruct ML as [|[m M] ML'].
  { forward_if.
    - forward. Exists nullval. entailer!.
    - contradiction. }
  simpl hk5_mklist.
  forward_if.
  { forward; unfold hk5_node; Intros; entailer!. }
  forward_loop (EX ML1: list (val * hk5_mk), EX m0: val, EX M0: hk5_mk, EX ML2: list (val * hk5_mk), EX nz: Z,
    PROP ((m, M) :: ML' = ML1 ++ (m0, M0) :: ML2; 0 <= nz <= Int64.max_unsigned)
    LOCAL (temp KC._n (Vlong (Int64.repr nz)); temp KC._k m0; gvars gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ((m, M) :: ML')) (gv KC._live); hk5p_seg ML1 m0;
         hk5_node m0 M0 (hk5_head ML2); hk5_mklist ML2))
  break: (EX ML1: list (val * hk5_mk), EX m0: val, EX M0: hk5_mk, EX ML2: list (val * hk5_mk),
    PROP ((m, M) :: ML' = ML1 ++ (m0, M0) :: ML2)
    LOCAL (temp KC._k m0; gvars gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ((m, M) :: ML')) (gv KC._live); hk5p_seg ML1 m0;
         hk5_node m0 M0 (hk5_head ML2); hk5_mklist ML2)).
  { Exists (@nil (val * hk5_mk)) m M ML' n. simpl hk5p_seg. entailer!. }
  { Intros ML1 m0 M0 ML2 nz.
    forward_if (EX b: bool,
      PROP (b = true <-> (nz > 0 /\ ML2 <> []))
      LOCAL (temp KC._t'2 (Val.of_bool b); temp KC._n (Vlong (Int64.repr nz)); temp KC._k m0; gvars gv)
      SEP (data_at Ews (tptr t_mk5) (hk5_head ((m, M) :: ML')) (gv KC._live); hk5p_seg ML1 m0;
           hk5_node m0 M0 (hk5_head ML2); hk5_mklist ML2)).
    - rewrite !Int64.unsigned_repr in H3 by rep_lia.
      unfold hk5_node at 1. Intros. unfold hk5_mk_val. forward. fold (hk5_mk_val M0 (hk5_head ML2)).
      sep_apply (hk5p_node_fold m0 M0 (hk5_head ML2) ltac:(split; assumption)).
      destruct ML2 as [|[m2 M2] ML2'].
      + forward. Exists false. entailer!.
        split; [discriminate|]. intros [_ ?]. congruence.
      + simpl hk5_head. simpl hk5_mklist. Intros. forward. Exists true. entailer!.
        * split; [split; [intros _; split; [lia|discriminate]|reflexivity]|].
          destruct m2; try contradiction. reflexivity.
        * simpl hk5_head. simpl hk5_mklist. cancel.
    - forward. Exists false. rewrite !Int64.unsigned_repr in H3 by rep_lia. entailer!.
    - Intros b.
      forward_if (PROP (nz > 0 /\ ML2 <> [])
        LOCAL (temp KC._n (Vlong (Int64.repr nz)); temp KC._k m0; gvars gv)
        SEP (data_at Ews (tptr t_mk5) (hk5_head ((m, M) :: ML')) (gv KC._live); hk5p_seg ML1 m0;
             hk5_node m0 M0 (hk5_head ML2); hk5_mklist ML2)).
      + forward. entailer!. apply H3. destruct b; [reflexivity|]. discriminate.
      + forward. Exists ML1 m0 M0 ML2. entailer!.
      + Intros. destruct ML2 as [|[m2 M2] ML2']; [contradiction|].
        unfold hk5_node at 1. Intros. unfold hk5_mk_val. forward.
        fold (hk5_mk_val M0 (hk5_head ((m2, M2) :: ML2'))).
        sep_apply (hk5p_node_fold m0 M0 (hk5_head ((m2, M2) :: ML2')) ltac:(split; assumption)).
        forward.
        Exists (ML1 ++ [(m0, M0)]) m2 M2 ML2' (nz - 1). rewrite hk5p_seg_snoc.
        entailer!.
        * rewrite <- app_assoc. auto.
        * simpl hk5_head. simpl hk5_mklist. cancel. }
  Intros ML1 m0 M0 ML2.
  forward.
  Exists m0.
  sep_apply (hk5p_fold ((m, M) :: ML') ML1 m0 M0 ML2 H1).
  entailer!.
  right. split; [discriminate|]. change (In m0 (map fst ((m, M) :: ML'))). rewrite H1, map_app. apply in_or_app. right. left. reflexivity.
Qed.

(* pick_held's result over a prefix L of the list *)
Definition hk5p_held_ok (r: val) (L: list (val * hk5_mk)) : Prop :=
  (r = nullval /\ Forall (fun x => m5_held (snd x) = Int64.zero) L) \/
  (exists M, In (r, M) L /\ m5_held M <> Int64.zero).

Lemma hk5p_held_ok_nil : hk5p_held_ok nullval [].
Proof. left. split; [reflexivity | constructor]. Qed.

Lemma hk5p_held_ok_skip r L m M : hk5p_held_ok r L -> m5_held M = Int64.zero -> hk5p_held_ok r (L ++ [(m, M)]).
Proof.
  intros [[-> HF] | (M' & HI & HM')] Hz.
  - left. split; [reflexivity|]. apply Forall_app. split; [assumption|]. constructor; [exact Hz | constructor].
  - right. exists M'. split; [apply in_or_app; left; assumption | assumption].
Qed.

Lemma hk5p_held_ok_take m M L1 L2 : m5_held M <> Int64.zero -> hk5p_held_ok m (L1 ++ (m, M) :: L2).
Proof.
  intros Hn. right. exists M. split; [apply in_or_app; right; left; reflexivity | assumption].
Qed.

Lemma hk5p_held_pos h : Int64.unsigned (Int64.repr 0) < Int64.unsigned h -> h <> Int64.zero.
Proof. intros Hl E. subst h. rewrite Int64.unsigned_zero in Hl. rewrite Int64.unsigned_repr in Hl by rep_lia. lia. Qed.

Lemma hk5p_held_zero h : Int64.unsigned (Int64.repr 0) >= Int64.unsigned h -> h = Int64.zero.
Proof.
  intros Hl. rewrite Int64.unsigned_repr in Hl by rep_lia. pose proof (Int64.unsigned_range h).
  rewrite <- (Int64.repr_unsigned h). replace (Int64.unsigned h) with 0 by lia. reflexivity.
Qed.

Lemma hkp5_pick_held_body :
  @semax_body hkp5_V hk5_Gpick W_keypairs KC.f_pick_held hk5_pick_held_spec.
Proof.
  start_function.
  forward.
  forward_call tt.
  Intros n.
  forward_loop (EX ML1: list (val * hk5_mk), EX ML2: list (val * hk5_mk), EX r: val, EX nz: Z,
    PROP (ML = ML1 ++ ML2; hk5p_held_ok r ML1; 0 <= nz <= Int64.max_unsigned)
    LOCAL (temp KC._r r; temp KC._n (Vlong (Int64.repr nz)); temp KC._k (hk5_head ML2); gvars gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5p_seg ML1 (hk5_head ML2); hk5_mklist ML2))
  continue: (EX ML1: list (val * hk5_mk), EX m0: val, EX M0: hk5_mk, EX ML2: list (val * hk5_mk), EX r: val,
    EX nz: Z,
    PROP (ML = ML1 ++ (m0, M0) :: ML2; hk5p_held_ok r (ML1 ++ [(m0, M0)]); 0 <= nz <= Int64.max_unsigned)
    LOCAL (temp KC._r r; temp KC._n (Vlong (Int64.repr nz)); temp KC._k m0; gvars gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5p_seg ML1 m0;
         hk5_node m0 M0 (hk5_head ML2); hk5_mklist ML2))
  break: (EX r: val,
    PROP (hk5p_held_ok r ML)
    LOCAL (temp KC._r r; gvars gv)
    SEP (data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live); hk5_mklist ML)).
  { forward. Exists (@nil (val * hk5_mk)) ML nullval n. simpl hk5p_seg. entailer!. apply hk5p_held_ok_nil. }
  { Intros ML1 ML2 r nz.
    forward_if.
    { destruct ML2 as [|[m2 M2] ML2']; simpl hk5_head; simpl hk5_mklist; entailer!. }
    2: { forward.
      destruct ML2 as [|[m2 M2] ML2']; [|simpl hk5_head in H3; simpl hk5_mklist; entailer!].
      Exists r. rewrite app_nil_r in H0. subst ML. sep_apply (hk5p_seg_all ML1). entailer!. }
    destruct ML2 as [|[m0 M0] ML2]; [simpl hk5_head in H3; contradiction|].
    simpl hk5_head. simpl hk5_mklist. Intros.
    unfold hk5_node at 1. Intros. unfold hk5_mk_val. forward. fold (hk5_mk_val M0 (hk5_head ML2)).
    sep_apply (hk5p_node_fold m0 M0 (hk5_head ML2) ltac:(split; assumption)).
    forward_if.
    { forward.
      forward_if.
      { forward. Exists m0. sep_apply (hk5p_fold ML ML1 m0 M0 ML2 H0). entailer!.
        apply hk5p_held_ok_take. apply hk5p_held_pos; assumption. }
      forward. Exists ML1 m0 M0 ML2 m0 (nz - 1). entailer!.
      split; [apply (hk5p_held_ok_take m0 M0 ML1 []); apply hk5p_held_pos; assumption|].
      assert (nz <> 0) by (intro; subst nz; contradiction). lia. }
    { forward. Exists ML1 m0 M0 ML2 r nz. entailer!.
      apply hk5p_held_ok_skip; [assumption|]. apply hk5p_held_zero; assumption. }
  }
  { Intros ML1 m0 M0 ML2 r nz.
    unfold hk5_node at 1. Intros. unfold hk5_mk_val. forward. fold (hk5_mk_val M0 (hk5_head ML2)).
    sep_apply (hk5p_node_fold m0 M0 (hk5_head ML2) ltac:(split; assumption)).
    Exists (ML1 ++ [(m0, M0)]) ML2 r nz. rewrite hk5p_seg_snoc. entailer!.
    rewrite <- app_assoc. reflexivity. }
  Intros r. forward. Exists r. entailer!.
Qed.

(* warn_same: the shim's wg_shim_refcount_warn (refwarn4, Noise.CS) read at W_keypairs *)
#[local] Instance hk5p_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hk5p_warr_cs sh (v: list val) p :
  @data_at Noise.CS sh (tarray tulong 5) v p = @data_at W_keypairs sh (tarray tulong 5) v p.
Proof.
  refine (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_keypairs hk5p_CCE sh (tarray tulong 5) v v
    _ _)); [apply JMeq_refl | reflexivity].
Qed.

Lemma hkp5_warn_same_body :
  @semax_body hkp5_V [] W_keypairs KC.f_warn_same hk5_warn_same_spec.
Proof.
  start_function.
  unfold refwarn4, hk5_warr. Intros.
  rewrite hk5p_warr_cs.
  change _wg_shim_refcount_warn with KC._wg_shim_refcount_warn.
  destruct H as (Hl0 & Hlm & Hlw & Heq & _).
  forward_for_simple_bound 5 (EX i: Z,
    PROP () LOCAL (gvars gv)
    SEP (data_at Ews (tarray tulong 5) (map Vlong w) (gv KC._wg_shim_refcount_warn);
         data_at Ews (tarray tulong 5) (map Vlong w0) (gv KC._warn0);
         data_at Ews (tarray tulong 5) (map Vlong mw) (gv KC._m_warn))).
  { entailer!. }
  { cbv beta.
    assert (E1: Znth i (map Vlong w) = Vlong (Znth i w)) by (rewrite Znth_map by lia; reflexivity).
    assert (E2: Znth i (map Vlong w0) = Vlong (Znth i w0)) by (rewrite Znth_map by lia; reflexivity).
    assert (E3: Znth i (map Vlong mw) = Vlong (Znth i mw)) by (rewrite Znth_map by lia; reflexivity).
    forward. forward. forward.
    forward_if.
    { exfalso. apply H3. rewrite Heq by lia.
      rewrite Int64.sub_add_l, Int64.sub_idem, Int64.add_zero_l. reflexivity. }
    forward. entailer!. }
  forward.
  unfold refwarn4, hk5_warr. rewrite hk5p_warr_cs. entailer!.
Qed.

Lemma hkp5_pick_bodies :
  @semax_body hkp5_V hk5_Gpick W_keypairs KC.f_pick_live hk5_pick_live_spec /\
  @semax_body hkp5_V hk5_Gpick W_keypairs KC.f_pick_held hk5_pick_held_spec /\
  @semax_body hkp5_V [] W_keypairs KC.f_warn_same hk5_warn_same_spec.
Proof.
  exact (conj hkp5_pick_live_body (conj hkp5_pick_held_body hkp5_warn_same_body)).
Qed.
