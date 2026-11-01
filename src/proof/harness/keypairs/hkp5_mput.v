(* law keypairs: the bodies of mk_unlink, m_get and m_put.
*)
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

(* ---------------------------------------------------------------------- *)
(* mk_unlink (adapted from v1's hkp4_unlink.v)                              *)
(* ---------------------------------------------------------------------- *)

(* the walked prefix ML1 of the live list, with a hole at the link cell l (&live or the last node's next field):
   giving back the cell and any suffix rebuilds the whole list *)
Definition hkp5_mput_hole (gv: globals) (ML1: list (val * hk5_mk)) (l: val) : mpred :=
  ALL ML2: list (val * hk5_mk),
    (data_at Ews (tptr t_mk5) (hk5_head ML2) l * hk5_mklist ML2) -*
    (data_at Ews (tptr t_mk5) (hk5_head (ML1 ++ ML2)) (gv KC._live) * hk5_mklist (ML1 ++ ML2)).

Lemma hkp5_mput_hole_nil gv : emp |-- hkp5_mput_hole gv [] (gv KC._live).
Proof.
  unfold hkp5_mput_hole. apply allp_right; intros ML2. apply -> wand_sepcon_adjoint.
  rewrite emp_sepcon. simpl app. apply derives_refl.
Qed.

Lemma hkp5_mput_hole_use gv ML1 ML2 l :
  data_at Ews (tptr t_mk5) (hk5_head ML2) l * hk5_mklist ML2 * hkp5_mput_hole gv ML1 l |--
  data_at Ews (tptr t_mk5) (hk5_head (ML1 ++ ML2)) (gv KC._live) * hk5_mklist (ML1 ++ ML2).
Proof.
  unfold hkp5_mput_hole.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply allp_left with ML2; apply derives_refl] |].
  apply modus_ponens_wand.
Qed.

Lemma hkp5_mput_node_split (m: val) M (nx: val) :
  data_at Ews t_mk5 (hk5_mk_val M nx) m |--
  field_at Ews t_mk5 (DOT KC._next) nx m *
  (ALL x: val, field_at Ews t_mk5 (DOT KC._next) x m -* data_at Ews t_mk5 (hk5_mk_val M x) m).
Proof.
  unfold data_at.
  eapply derives_trans.
  { apply (nested_field_ramif' Ews t_mk5 nil (DOT KC._next) (hk5_mk_val M nx) nx m).
    - apply JMeq_refl.
    - simpl. split; [simpl; auto | simpl; unfold in_members; simpl; auto 20]. }
  apply sepcon_derives; [apply derives_refl |].
  apply allp_right; intros x. apply allp_left with x. apply allp_left with x.
  rewrite prop_imp by apply JMeq_refl. apply derives_refl.
Qed.

Lemma hkp5_mput_rem_use (m: val) M (y: val) :
  field_at Ews t_mk5 (DOT KC._next) y m *
  (ALL x: val, field_at Ews t_mk5 (DOT KC._next) x m -* data_at Ews t_mk5 (hk5_mk_val M x) m) |--
  data_at Ews t_mk5 (hk5_mk_val M y) m.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply allp_left with y; apply derives_refl] |].
  apply modus_ponens_wand.
Qed.

Lemma hkp5_mput_hole_step gv ML1 l (m: val) M :
  Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32 ->
  data_at Ews (tptr t_mk5) m l * hkp5_mput_hole gv ML1 l *
  (ALL x: val, field_at Ews t_mk5 (DOT KC._next) x m -* data_at Ews t_mk5 (hk5_mk_val M x) m) *
  malloc_token Ews t_mk5 m |--
  hkp5_mput_hole gv (ML1 ++ [(m, M)]) (field_address t_mk5 (DOT KC._next) m).
Proof.
  intros HZ. unfold hkp5_mput_hole at 2. apply allp_right; intros ML2. apply -> wand_sepcon_adjoint.
  rewrite <- app_assoc. simpl app.
  eapply derives_trans; [| apply (hkp5_mput_hole_use gv ML1 ((m, M) :: ML2) l)].
  simpl hk5_mklist. simpl hk5_head. unfold hk5_node.
  replace (data_at Ews (tptr t_mk5) (hk5_head ML2) (field_address t_mk5 (DOT KC._next) m))
    with (field_at Ews t_mk5 (DOT KC._next) (hk5_head ML2) m) by (rewrite field_at_data_at; reflexivity).
  rewrite prop_true_andp by auto.
  sep_apply (hkp5_mput_rem_use m M (hk5_head ML2)). cancel.
Qed.

Lemma hkp5_mput_mklist_valid ML x :
  In x (map fst ML) -> hk5_mklist ML |-- valid_pointer x.
Proof.
  induction ML as [| [m M] ML IH]; simpl; intros Hin; [contradiction |].
  unfold hk5_node. destruct Hin as [<- | Hin].
  - apply sepcon_valid_pointer1. apply andp_left2. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [auto | simpl; lia].
  - apply sepcon_valid_pointer2. auto.
Qed.

Lemma hkp5_mput_mklist_head ML :
  hk5_mklist ML |-- !! is_pointer_or_null (hk5_head ML).
Proof.
  destruct ML as [| [m M] ML]; simpl; [entailer! |].
  unfold hk5_node. entailer!.
Qed.

Lemma hkp5_mput_adel_app {A: Type} (ML1: list (val * A)) k (Mk: A) B :
  ~ In k (map fst ML1) -> adel (ML1 ++ (k, Mk) :: B) k = ML1 ++ B.
Proof.
  induction ML1 as [| [x X] ML1 IH]; simpl; intros Hn.
  - destruct (EqDec_val k k); congruence.
  - destruct (EqDec_val x k); [tauto |]. rewrite IH; auto.
Qed.

Lemma hkp5_mput_unlink_body :
  @semax_body hkp5_V [] W_keypairs KC.f_mk_unlink hk5_mk_unlink_spec.
Proof.
  start_function.
  forward.
  forward_loop
    (EX ML1: list (val * hk5_mk), EX ML2: list (val * hk5_mk), EX l: val,
      PROP (ML = ML1 ++ ML2; ~ In k (map fst ML1); In k (map fst ML2))
      LOCAL (temp KC._l l; temp KC._k k; gvars gv)
      SEP (data_at Ews (tptr t_mk5) (hk5_head ML2) l; hk5_mklist ML2; hkp5_mput_hole gv ML1 l))
  continue:
    (EX ML1: list (val * hk5_mk), EX m: val, EX M: hk5_mk, EX ML2: list (val * hk5_mk), EX l: val,
      PROP (ML = ML1 ++ (m, M) :: ML2; ~ In k (map fst ML1); m <> k; In k (map fst ML2))
      LOCAL (temp KC._l l; temp KC._k k; gvars gv)
      SEP (data_at Ews (tptr t_mk5) m l; hk5_node m M (hk5_head ML2); hk5_mklist ML2; hkp5_mput_hole gv ML1 l))
  break:
    (PROP () LOCAL ()
     SEP (data_at Ews (tptr t_mk5) (hk5_head (adel ML k)) (gv KC._live); hk5_mklist (adel ML k);
          data_at_ Ews t_mk5 k; malloc_token Ews t_mk5 k)).
  - Exists (@nil (val * hk5_mk)) ML (gv KC._live). entailer!. apply hkp5_mput_hole_nil.
  - (* the test *l != NULL, then *l == k *)
    Intros ML1 ML2 l.
    destruct ML2 as [| [m M] ML2]; [simpl in *; contradiction |].
    simpl hk5_mklist; simpl hk5_head. unfold hk5_node. Intros.
    assert_PROP (isptr m) by entailer!.
    forward.
    forward_if; [| subst m; contradiction].
    forward.
    forward_if.
    { apply denote_tc_test_eq_split; [auto 50 with valid_pointer |].
      simpl in H3. destruct H3 as [<- | Hk]; [auto 50 with valid_pointer |].
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply hkp5_mput_mklist_valid; auto. }
    2: { forward. Exists ML1 m M ML2 l. unfold hk5_node. entailer!.
         simpl in H3. destruct H3; [congruence | auto]. }
    subst m.
    sep_apply (hkp5_mput_mklist_head ML2). Intros.
    forward.
    forward.
    forward.
    subst ML. rewrite hkp5_mput_adel_app by auto.
    sep_apply (hkp5_mput_hole_use gv ML1 ML2 l).
    sep_apply (data_at_data_at_ Ews t_mk5 (hk5_mk_val M (hk5_head ML2)) k).
    entailer!.
  - (* l = &(l[0]->next): the node joins the walked prefix *)
    Intros ML1 m M ML2 l. unfold hk5_node. Intros.
    assert_PROP (isptr m) by entailer!.
    forward. forward.
    sep_apply (hkp5_mput_node_split m M (hk5_head ML2)).
    sep_apply (hkp5_mput_hole_step gv ML1 l m M); [auto |].
    Exists (ML1 ++ [(m, M)]) ML2 (field_address t_mk5 (DOT KC._next) m).
    rewrite field_at_data_at.
    entailer!.
    split; [rewrite <- app_assoc; reflexivity | rewrite map_app, in_app_iff; simpl; intuition].
  - (* after the loop (left by break only): the function's postcondition *)
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION. simpl RA_normal.
    unfold stackframe_of. simpl. intros rho.
    rewrite sepcon_emp. apply andp_left2. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* list lemmas for m_get / m_put (adapted from v1's hkp4_mput.v)            *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_mput_afind_in : forall {A: Type} (l: list (val * A)) k,
  In k (map fst l) -> exists M, afind l k = Some M.
Proof.
  induction l as [|[x w] l IH]; simpl; intros k Hin; [contradiction|].
  destruct (EqDec_val x k); [eauto|]. destruct Hin; [congruence|]. auto.
Qed.

Lemma hkp5_mput_map_fst_aupd : forall {A: Type} (l: list (val * A)) k v,
  map fst (aupd l k v) = map fst l.
Proof.
  induction l as [|[x w] l IH]; simpl; intros; auto.
  destruct (EqDec_val x k); simpl; f_equal; auto.
Qed.

Lemma hkp5_mput_head_aupd : forall {A: Type} (l: list (val * A)) k v,
  hk5_head (aupd l k v) = hk5_head l.
Proof.
  destruct l as [|[x w] l]; simpl; intros; auto. destruct (EqDec_val x k); auto.
Qed.

Lemma hkp5_mput_adel_aupd : forall {A: Type} (l: list (val * A)) k v,
  adel (aupd l k v) k = adel l k.
Proof.
  induction l as [|[x w] l IH]; simpl; intros; auto.
  destruct (EqDec_val x k); simpl.
  - rewrite if_true by auto. auto.
  - rewrite if_false by auto. f_equal; auto.
Qed.

Lemma hkp5_mput_open : forall ML k M, afind ML k = Some M ->
  exists nx (Rest: mpred), hk5_mklist ML = (hk5_node k M nx * Rest)%logic /\
    forall M', hk5_mklist (aupd ML k M') = (hk5_node k M' nx * Rest)%logic.
Proof.
  induction ML as [|[x w] ML IH]; simpl; intros k M Hf; [discriminate|].
  destruct (EqDec_val x k).
  - subst x. inv Hf. exists (hk5_head ML), (hk5_mklist ML). split; auto.
  - destruct (IH k M Hf) as [nx [Rest [E1 E2]]].
    exists nx, (hk5_node x w (hk5_head ML) * Rest)%logic. split.
    + rewrite E1. apply pred_ext; cancel.
    + intros M'. simpl. rewrite hkp5_mput_head_aupd, E2. apply pred_ext; cancel.
Qed.

Lemma hkp5_mput_warn_bump mw t :
  0 <= t < Zlength mw ->
  upd_Znth t (map Vlong mw) (Vlong (Int64.add (Znth t mw) (Int64.repr 1))) = map Vlong (warn_bump mw t).
Proof.
  intros Ht. unfold warn_bump. rewrite upd_Znth_map. reflexivity.
Qed.

Lemma hkp5_mput_body :
  @semax_body hkp5_V hk5_Gm_put W_keypairs KC.f_m_put hk5_m_put_spec.
Proof.
start_function.
destruct (eq_dec k nullval) as [Hk0|Hk0].
{ subst k. forward_if; [forward | contradiction]. }
destruct H as [H|Hin]; [contradiction|].
destruct (hkp5_mput_afind_in ML k Hin) as [M HM].
destruct (hkp5_mput_open ML k M HM) as [nx [Rest [E1 E2]]].
rewrite E1. unfold hk5_node, hk5_warr. Intros.
forward_if; [contradiction|].
forward_if (PROP () LOCAL (gvars gv; temp KC._k k)
  SEP (mem_mgr gv; data_at Ews (tptr t_mk5) (hk5_head ML) (gv KC._live);
       data_at Ews t_mk5 (hk5_mk_val (if unref then m5_unhash M else M) nx) k; malloc_token Ews t_mk5 k; Rest;
       data_at Ews tulong (Vlong fr) (gv KC._m_frees); data_at Ews (tarray tulong 5) (map Vlong mw) (gv KC._m_warn))).
{ forward. destruct unref; [|contradiction]. entailer!. }
{ forward. destruct unref; [discriminate|]. entailer!. }
set (M1 := if unref then m5_unhash M else M).
assert (Hr1: m5_refs M1 = m5_refs M) by (subst M1; destruct unref; reflexivity).
assert (HZ1: Zlength (m5_send M1) = 32 /\ Zlength (m5_recv M1) = 32) by (subst M1; destruct unref; simpl; auto).
assert (Hfold0: hk5_mklist (if unref then aupd ML k M1 else ML) = (hk5_node k M1 nx * Rest)%logic)
  by (subst M1; destruct unref; [apply E2 | apply E1]).
assert (Hhd0: hk5_head (if unref then aupd ML k M1 else ML) = hk5_head ML)
  by (destruct unref; [apply hkp5_mput_head_aupd | reflexivity]).
forward.
forward_if.
- (* saturated: m_warn[REFCOUNT_SUB_UAF]++, nothing else *)
  forward. forward. forward.
  assert (Hput: hk5_put k unref ML fr mw = ((if unref then aupd ML k M1 else ML), fr, warn_bump mw REFCOUNT_SUB_UAF)).
  { unfold hk5_put. rewrite if_false by auto. rewrite HM. rewrite <- Hr1, H4. reflexivity. }
  rewrite Hput. simpl fst; simpl snd. rewrite Hhd0, Hfold0. unfold hk5_node, hk5_warr.
  rewrite (hkp5_mput_warn_bump mw 3) by lia. entailer!.
  unfold warn_bump. rewrite upd_Znth_Zlength by (unfold REFCOUNT_SUB_UAF; lia). auto.
- (* one reference less; at 0 unlinked and freed *)
  forward. forward. forward.
  set (r := Int.sub (m5_refs M1) (Int.repr 1)).
  assert (HZ: Zlength (m5_send (m5_set_refs M1 r)) = 32 /\ Zlength (m5_recv (m5_set_refs M1 r)) = 32)
    by (simpl; auto).
  assert (Hput: hk5_put k unref ML fr mw =
    if Int.eq r Int.zero then (adel ML k, Int64.add fr Int64.one, mw) else (aupd ML k (m5_set_refs M1 r), fr, mw)).
  { unfold hk5_put. rewrite if_false by auto. rewrite HM. rewrite <- Hr1.
    rewrite Int.eq_false by (intro Hc; apply H4; rewrite Hc; apply Int.same_if_eq; reflexivity).
    subst r M1. rewrite Hr1. reflexivity. }
  replace_SEP 2 (data_at Ews t_mk5 (hk5_mk_val (m5_set_refs M1 r) nx) k).
  { entailer!. }
  assert (Hfold: (data_at Ews t_mk5 (hk5_mk_val (m5_set_refs M1 r) nx) k * malloc_token Ews t_mk5 k * Rest)%logic
    |-- hk5_mklist (aupd ML k (m5_set_refs M1 r))).
  { rewrite E2. unfold hk5_node. entailer!. }
  forward_if.
  + sep_apply Hfold.
    rewrite <- (hkp5_mput_head_aupd ML k (m5_set_refs M1 r)).
    forward_call (gv, aupd ML k (m5_set_refs M1 r), k).
    { rewrite hkp5_mput_map_fst_aupd. auto. }
    forward_call (t_mk5, k, gv).
    { rewrite if_false by auto. cancel. }
    forward. forward.
    entailer!.
    rewrite Hput, H5, Int.eq_true, hkp5_mput_adel_aupd. simpl fst; simpl snd. unfold hk5_warr. entailer!.
  + forward. rewrite Hput, Int.eq_false by auto. simpl fst; simpl snd.
    rewrite hkp5_mput_head_aupd. sep_apply Hfold. unfold hk5_warr. entailer!.
Qed.

Lemma hkp5_mput_get_body :
  @semax_body hkp5_V [] W_keypairs KC.f_m_get hk5_m_get_spec.
Proof.
start_function.
destruct (hkp5_mput_open ML k M H) as [nx [Rest [E1 E2]]].
rewrite E1. unfold hk5_node, hk5_warr. Intros.
forward.
forward_if (PROP () LOCAL (temp KC._t'1 (Val.of_bool (hk5_get_sat (m5_refs M))); temp KC._k k; gvars gv)
  SEP (data_at Ews t_mk5 (hk5_mk_val M nx) k; malloc_token Ews t_mk5 k; Rest;
       data_at Ews (tarray tulong 5) (map Vlong mw) (gv KC._m_warn))).
{ forward. entailer!. unfold hk5_get_sat. rewrite H4. reflexivity. }
{ forward. forward. entailer!. unfold hk5_get_sat, hk5_INT_MAX. rewrite (Int.eq_false _ _ H4). simpl orb.
  rewrite hk5_sat_eq. destruct (Int.eq _ _); reflexivity. }
forward_if.
- forward. forward. forward.
  assert (Hs: hk5_get_sat (m5_refs M) = true) by (destruct (hk5_get_sat _); [reflexivity | inv H4]).
  unfold hk5_get_refs, hk5_get_warn; rewrite Hs. rewrite E2. unfold hk5_node, hk5_warr.
  replace (Int.repr (-1073741824)) with REFCOUNT_SATURATED by (apply Int.same_if_eq; reflexivity).
  change (Int64.repr (Int.signed (Int.repr 1))) with (Int64.repr 1).
  rewrite hkp5_mput_warn_bump by lia.
  entailer!.
  rewrite Zlength_map in H9. exact H9.
- forward. forward.
  assert (Hs: hk5_get_sat (m5_refs M) = false) by (destruct (hk5_get_sat _); [inv H4 | reflexivity]).
  unfold hk5_get_refs, hk5_get_warn; rewrite Hs. rewrite E2. unfold hk5_node, hk5_warr.
  entailer!.
Qed.

Lemma hkp5_mput_bodies :
  @semax_body hkp5_V [] W_keypairs KC.f_mk_unlink hk5_mk_unlink_spec /\
  @semax_body hkp5_V [] W_keypairs KC.f_m_get hk5_m_get_spec /\
  @semax_body hkp5_V hk5_Gm_put W_keypairs KC.f_m_put hk5_m_put_spec.
Proof.
  split; [exact hkp5_mput_unlink_body |].
  split; [exact hkp5_mput_get_body | exact hkp5_mput_body].
Qed.
