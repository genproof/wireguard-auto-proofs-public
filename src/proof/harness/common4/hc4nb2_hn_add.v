(* the body of hnodes_add, adapted from v1's
   hc_hnodes_bodies3.v (hnb3_add_A): the node has one more field (rest), the reference count is draw_peer_refs(),
   the proof compspecs is CS4nb and the world's CSw is abstract (cspecs_sub CS4nb CSw). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_hn_common.
Require Import WgNoise.proof.harness.common4.hc4nb2_hn_sub.
Require WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HI := WgNoise.harness.x_consume_initiation_any.code.

(* a node's p and next fields at CS4nb, the rest of it hidden *)
Section Cell.
#[local] Existing Instance CKS.
Definition hc4nb_hna_mid (N: hnode4) (l: val) : mpred :=
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) l *
  @field_at CKS Ews t_hnode4 (DOT HC._refs) (hn_refs N) l * spacer Ews 300 304 l *
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l.

Lemma hc4nb_hna_cell_pn N nx l :
  hc4nb_cell N nx l =
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) (hn_p N) l * @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l *
  hc4nb_hna_mid N l.
Proof.
  unfold hc4nb_cell, hc4nb_hna_mid. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4nb _ Ews t_hnode4 (DOT HC._next) nx nx l) by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hc4nb_hna_cell_ N nx l : hc4nb_cell N nx l |-- @data_at_ CS4nb Ews t_hnode4 l.
Proof.
  unfold hc4nb_cell. sep_apply (@data_at_data_at_ CKS). rewrite (@data_at__cs_eq CKS CS4nb hc4nb2_hn_CKS_4) by reflexivity.
  apply derives_refl.
Qed.

Definition hc4nb_hna_N0 (n: val) : hnode4 :=
  mkHN4 n Vundef (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap).

Lemma hc4nb_hna_cell_new l :
  @data_at_ CS4nb Ews t_hnode4 l |-- hc4nb_cell (hc4nb_hna_N0 l) Vundef l.
Proof.
  rewrite <- (@data_at__cs_eq CKS CS4nb hc4nb2_hn_CKS_4) by reflexivity.
  unfold hc4nb_cell, data_at_, field_at_, data_at. apply derives_refl.
Qed.
End Cell.

Lemma hc4nb_hna_cell_fold N nx l :
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) (hn_p N) l * @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l *
  hc4nb_hna_mid N l |-- hc4nb_cell N nx l.
Proof. rewrite hc4nb_hna_cell_pn. apply derives_refl. Qed.

(* the new node: its p and next fields at CS4nb, the rest (undefined) behind a Definition *)
Definition hc4nb_hna_newmid (l: val) : mpred := hc4nb_hna_mid (hc4nb_hna_N0 l) l.

Lemma hc4nb_hna_new_split l :
  @data_at_ CS4nb Ews t_hnode4 l |--
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) Vundef l * @field_at CS4nb Ews t_hnode4 (DOT HC._next) Vundef l *
  hc4nb_hna_newmid l.
Proof.
  sep_apply (hc4nb_hna_cell_new l). rewrite hc4nb_hna_cell_pn. unfold hc4nb_hna_newmid. apply derives_refl.
Qed.

Lemma hc4nb_hna_new_fold v nx l :
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) v l * @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l *
  hc4nb_hna_newmid l |--
  hc4nb_cell (mkHN4 l v (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)) nx l.
Proof. rewrite hc4nb_hna_cell_pn. unfold hc4nb_hna_newmid. apply derives_refl. Qed.

Lemma hc4nb_hna_new_free v nx l :
  @field_at CS4nb Ews t_hnode4 (DOT HC._p) v l * @field_at CS4nb Ews t_hnode4 (DOT HC._next) nx l *
  hc4nb_hna_newmid l |-- @data_at_ CS4nb Ews t_hnode4 l.
Proof. sep_apply (hc4nb_hna_new_fold v nx l). apply hc4nb_hna_cell_. Qed.

Lemma hc4nb_hna_p_valid v l : @field_at CS4nb Ews t_hnode4 (DOT HC._p) v l |-- valid_pointer l.
Proof.
  apply (@field_at_valid_ptr0 CS4nb); [apply readable_nonidentity; auto | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma hc4nb_hna_mid_eq N M l :
  hn_snap N = hn_snap M -> hn_refs N = hn_refs M -> hn_rest N = hn_rest M ->
  hc4nb_hna_mid N l = hc4nb_hna_mid M l.
Proof. intros A B C. unfold hc4nb_hna_mid. rewrite A, B, C. reflexivity. Qed.

(* the world compspecs as a hypothesis that typeclass resolution does not take for the proof's compspecs CS4nb *)
Definition hc4nb_hna_csw := compspecs.
#[local] Typeclasses Opaque hc4nb_hna_csw.

#[local] Instance hc4nb_hna_CCE_N_H : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Lemma hc4nb_hna_bytes_NH sh n (v: list val) p :
  @data_at Noise.CS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hc4nb_hna_pk_find_app PS1 PS2 pub :
  pk_find (PS1 ++ PS2) pub = match pk_find PS1 pub with Some r => Some r | None => pk_find PS2 pub end.
Proof.
  induction PS1 as [|[[a sh] P] PS1 IH]; simpl; auto.
  destruct (bytes_eqb (hs_rstatic (p_hs P)) pub); auto.
Qed.

Lemma hc4nb_hna_peer_isptr sh p P : peer_rep sh p P |-- !! isptr p.
Proof. unfold peer_rep. Intros. apply prop_right. destruct H as [Hp _]; exact Hp. Qed.

Lemma hc4nb_hna_wand_intro A B (Fr: list mpred) :
  fold_right_sepcon Fr * B |-- A -> B * fold_right_sepcon Fr |-- B * (B -* A).
Proof. intros HA. apply sepcon_derives; [auto|]. apply wand_sepcon_adjoint. exact HA. Qed.

Lemma hc4nb_hna_rs sh p P :
  peer_rep sh p P |--
  !! (Zlength (hs_rstatic (p_hs P)) = 32) &&
  (hbytes sh (hs_rstatic (p_hs P)) (offset_val 136 p) *
   (hbytes sh (hs_rstatic (p_hs P)) (offset_val 136 p) -* peer_rep sh p P)).
Proof.
  unfold peer_rep at 1, hs_rep at 1. Intros.
  apply andp_right; [apply prop_right; destruct H0 as (_ & HL & _); exact HL|].
  assert_PROP (@field_compatible Noise.CS t_hs (DOT I._remote_static) (hs_addr p)) by entailer!.
  assert (E: offset_val 88 (hs_addr p) = offset_val 136 p) by (unfold hs_addr; rewrite offset_offset_val; reflexivity).
  rewrite (@field_at_data_at Noise.CS sh t_hs (DOT I._remote_static)).
  unfold field_address; rewrite if_true by auto.
  change (@nested_field_offset Noise.CS t_hs (DOT I._remote_static)) with 88.
  change (@nested_field_type Noise.CS t_hs (DOT I._remote_static)) with (tarray tuchar 32).
  rewrite E.
  pose proof H0 as (_ & HL & _).
  unfold hbytes; rewrite HL, <- !hc4nb_hna_bytes_NH.
  eapply derives_trans; [|apply hc4nb_hna_wand_intro].
  { cancel. match goal with |- ?X |-- fold_right_sepcon ?F => unify F [X] end.
    simpl fold_right_sepcon. rewrite sepcon_emp. apply derives_refl. }
  simpl fold_right_sepcon. rewrite sepcon_emp.
  unfold peer_rep, hs_rep.
  rewrite (@field_at_data_at Noise.CS sh t_hs (DOT I._remote_static)).
  unfold field_address; rewrite if_true by auto.
  change (@nested_field_offset Noise.CS t_hs (DOT I._remote_static)) with 88.
  change (@nested_field_type Noise.CS t_hs (DOT I._remote_static)) with (tarray tuchar 32).
  rewrite E.
  Intros lk. Exists lk. entailer!.
Qed.

Lemma hc4nb_hna_wand_intro_all {A: Type} (Q: A -> mpred) B B' (Fr: list mpred) :
  (forall r, fold_right_sepcon Fr * B' r |-- Q r) -> B * fold_right_sepcon Fr |-- B * (ALL r: A, (B' r -* Q r)).
Proof. intros HA. apply sepcon_derives; [auto|]. apply allp_right; intros r. apply wand_sepcon_adjoint. apply HA. Qed.

Lemma hc4nb_hna_refs sh p P :
  peer_rep sh p P |--
  @field_at CS4nb sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  (ALL r: int, (@field_at CS4nb sh t_peer (DOT I._refcount) (Vint r) p -* peer_rep sh p (p_set_refs P r))).
Proof.
  unfold peer_rep at 1. Intros.
  rewrite (@field_at_cs_eq Noise.CS CS4nb _ sh t_peer (DOT I._refcount) (Vint (p_refs P)) (Vint (p_refs P)) p)
    by (try apply JMeq_refl; reflexivity).
  eapply derives_trans; [|apply (hc4nb_hna_wand_intro_all (fun r => peer_rep sh p (p_set_refs P r)))].
  { cancel. match goal with |- ?X |-- fold_right_sepcon ?F => unify F [X] end.
    simpl fold_right_sepcon. rewrite sepcon_emp. apply derives_refl. }
  intros r. simpl fold_right_sepcon. rewrite sepcon_emp.
  unfold peer_rep, p_set_refs; cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  rewrite <- (@field_at_cs_eq Noise.CS CS4nb _ sh t_peer (DOT I._refcount) (Vint r) (Vint r) p)
    by (try apply JMeq_refl; reflexivity).
  entailer!.
Qed.

Lemma hc4nb_hna_reasm CSw l0 it nx N NS1 NS2 PS1 x PS2 :
  it = hn_addr N ->
  hc4nb_seg CSw l0 it NS1 * @malloc_token CSw Ews t_hnode4 it * hc4nb_cell N nx it *
  @malloc_token CSw Ews t_peer (hn_p N) * hnodes_rep4 CSw nx NS2 *
  peers_rep PS1 * peer_item_rep x * peers_rep PS2
  |-- hnodes_rep4 CSw l0 (NS1 ++ N :: NS2) * peers_rep (PS1 ++ x :: PS2).
Proof.
  intros Hit. sep_apply (hc4nb_seg_snoc CSw l0 it nx N NS1 Hit).
  sep_apply (hc4nb_seg_rep CSw l0 nx (NS1 ++ [N]) NS2). rewrite <- app_assoc. simpl app.
  unfold peers_rep; rewrite iter_sepcon_app; simpl iter_sepcon. cancel.
Qed.

Ltac hc4nb_hna_absurd :=
  first [discriminate | contradiction |
         (exfalso; match goal with H: ?a <> ?a |- _ => apply H; reflexivity end) |
         (exfalso; match goal with H: Int.one = Int.zero |- _ => discriminate H end)].

Lemma hc4nb_hna_and1 b : 0 <= b <= Byte.max_unsigned -> Int.and (Int.repr b) (Int.repr 1) = Int.repr (Z.land b 1).
Proof. intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma hc4nb_hna_land1 b : Z.land b 1 = 0 \/ Z.land b 1 = 1.
Proof.
  pose proof (Z.land_ones b 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E.
  rewrite E. pose proof (Z.mod_pos_bound b 2 ltac:(lia)). lia.
Qed.

Lemma hc4nb_hna_psk_split {cs} {CCE: change_composite_env HCS cs} shk q v bs :
  readable_share shk -> q = nullval \/ q = v -> isptr v -> Zlength bs = 32 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at cs Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) v =
  (if eq_dec q nullval then emp else hbytes shk (map Byte.repr bs) q) *
  (if eq_dec q nullval then @data_at cs Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) v
   else @data_at cs (Share.comp shk) (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) v).
Proof.
  intros Hsh Hq Hv HL HB. destruct (eq_dec q nullval) as [E|E].
  { rewrite emp_sepcon; auto. }
  destruct Hq as [Hq|Hq]; [contradiction|subst q].
  rewrite <- (@data_at_share_join cs shk (Share.comp shk) Tsh) by apply join_comp_Tsh. f_equal.
  unfold hbytes. rewrite Zlength_map, HL.
  rewrite (@data_at_cs_eq HCS cs CCE shk (tarray tuchar 32) (bytes (map Byte.repr bs)) (bytes (map Byte.repr bs)) v);
    [|apply JMeq_refl|reflexivity]. f_equal.
  unfold bytes. rewrite map_map. apply map_ext_in. intros b Hb. rewrite Forall_forall in HB.
  unfold Vubyte. rewrite Byte.unsigned_repr by (apply HB; auto). reflexivity.
Qed.

Lemma hc4nb_hna_inst {A: Type} (F Q: A -> mpred) r : F r * (ALL x: A, (F x -* Q x)) |-- Q r.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (allp_instantiate _ r)]|].
  apply modus_ponens_wand.
Qed.

(* malloc / free of the node and the peer at the abstract world CSw *)
Lemma hc4nb_hna_node_to4 (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) l :
  @malloc_token CSw Ews t_hnode4 l * @data_at_ CSw Ews t_hnode4 l |--
  @malloc_token CSw Ews t_hnode4 l * @data_at_ CS4nb Ews t_hnode4 l.
Proof. apply (hc4nb2_hn_sub_to4 CSw HSUB HC._hnode); try (vm_compute; discriminate); reflexivity. Qed.

Lemma hc4nb_hna_node_tow (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) l :
  @malloc_token CSw Ews t_hnode4 l * @data_at_ CS4nb Ews t_hnode4 l |--
  @malloc_token CSw Ews t_hnode4 l * @data_at_ CSw Ews t_hnode4 l.
Proof. apply (hc4nb2_hn_sub_tow CSw HSUB HC._hnode); try (vm_compute; discriminate); reflexivity. Qed.

Lemma hc4nb_hna_peer_to4 (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) l :
  @malloc_token CSw Ews t_peer l * @data_at_ CSw Ews t_peer l |--
  @malloc_token CSw Ews t_peer l * @data_at_ Noise.CS Ews t_peer l.
Proof.
  eapply derives_trans; [apply (hc4nb2_hn_sub_to4 CSw HSUB I._wg_peer); [vm_compute; discriminate ..| reflexivity | reflexivity]|].
  rewrite (@data_at__cs_eq CS4nb Noise.CS _ Ews (Tstruct I._wg_peer noattr) l) by reflexivity. apply derives_refl.
Qed.

Lemma hc4nb_hna_sizeof_node (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) : @sizeof CSw t_hnode4 = 488.
Proof. unfold t_hnode4. rewrite (hc4nb2_hn_sub_sizeof CSw HSUB HC._hnode) by (vm_compute; discriminate). reflexivity. Qed.

Lemma hc4nb_hna_sizeof_peer (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) : @sizeof CSw t_peer = @sizeof CS4nb t_peer.
Proof. unfold t_peer. rewrite (hc4nb2_hn_sub_sizeof CSw HSUB I._wg_peer) by (vm_compute; discriminate). reflexivity. Qed.

Lemma hc4nb_hna_rep_fold (CSw: compspecs) n N nx NS :
  n = hn_addr N ->
  hc4nb_cell N nx n * @malloc_token CSw Ews t_peer (hn_p N) * @malloc_token CSw Ews t_hnode4 n *
  hnodes_rep4 CSw nx NS |-- hnodes_rep4 CSw n (N :: NS).
Proof.
  intros E. rewrite hc4nb_rep_cons. apply andp_right; [apply prop_right; auto|].
  Exists nx. subst n. cancel.
Qed.

Lemma hc4nb_hna_rep_fold_new (CSw: compspecs) n p nx NS :
  hc4nb_cell (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)) nx n *
  @malloc_token CSw Ews t_peer p * @malloc_token CSw Ews t_hnode4 n * hnodes_rep4 CSw nx NS
  |-- hnodes_rep4 CSw n (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS).
Proof. apply (hc4nb_hna_rep_fold CSw n (mkHN4 n p _ Vundef _) nx NS eq_refl). Qed.

(* malloc's preconditions at the abstract CSw (VST's my_auto loops on them) *)
Lemma hc4nb_hna_pre_node (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) :
  fold_right_and True [0 <= @sizeof CSw t_hnode4 <= Ptrofs.max_unsigned;
                       @complete_legal_cosu_type (@cenv_cs CSw) t_hnode4 = true;
                       @natural_aligned CSw natural_alignment t_hnode4 = true].
Proof.
  unfold t_hnode4; cbn [fold_right_and].
  rewrite (hc4nb2_hn_sub_sizeof CSw HSUB HC._hnode) by (vm_compute; discriminate).
  rewrite (hc4nb2_hn_sub_cl CSw HSUB HC._hnode) by (vm_compute; discriminate).
  rewrite (hc4nb2_hn_sub_na CSw HSUB HC._hnode) by (vm_compute; discriminate).
  vm_compute. split; [split; discriminate | split; [reflexivity | split; [reflexivity | exact I]]].
Qed.

Lemma hc4nb_hna_pre_peer (CSw: compspecs) (HSUB: cspecs_sub CS4nb CSw) :
  fold_right_and True [0 <= @sizeof CSw t_peer <= Ptrofs.max_unsigned;
                       @complete_legal_cosu_type (@cenv_cs CSw) t_peer = true;
                       @natural_aligned CSw natural_alignment t_peer = true].
Proof.
  unfold t_peer; cbn [fold_right_and].
  rewrite (hc4nb2_hn_sub_sizeof CSw HSUB I._wg_peer) by (vm_compute; discriminate).
  rewrite (hc4nb2_hn_sub_cl CSw HSUB I._wg_peer) by (vm_compute; discriminate).
  rewrite (hc4nb2_hn_sub_na CSw HSUB I._wg_peer) by (vm_compute; discriminate).
  vm_compute. split; [split; discriminate | split; [reflexivity | split; [reflexivity | exact I]]].
Qed.

(* forward_call of malloc, step by step (fwd_call' with our own argument and precondition proofs) *)
Ltac hc4nb_hna_setup W VL :=
  prove_call_setup1 funspec_sub_refl;
  [ .. |
    match goal with |- call_setup1 _ _ _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _ _ _ -> _ =>
      check_witness_type (@nil Type) A W end;
    let H := fresh "SetupOne" in intro H;
    match goal with |- @semax ?CS _ _ (PROPx ?P (LOCALx ?L (SEPx ?R'))) _ _ =>
      let Frame := fresh "Frame" in evar (Frame: list mpred);
      exploit (call_setup2_i _ _ _ _ _ _ _ _ R' R' _ _ _ _ (@nil Type) _ _ _ _ _ _ _ H W Frame); clear H end;
    simpl functors.MixVariantFunctor._functor;
    [ try_convertPreElim | check_prove_local2ptree | VL | auto 50 with derives | check_gvars_spec
    | cancel_for_forward_call | ] ].

Ltac hc4nb_hna_y tpre :=
  let H := fresh in intro H;
  eapply (semax_call_id1_y_wow H);
  clear H;
  lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
  [ check_result_type | check_result_type
  | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
  | (clear; let H := fresh in intro H; inversion H)
  | match_postcondition
  | prove_delete_temp
  | prove_delete_temp
  | unify_postcondition_exps
  | tpre ].

Ltac hc4nb_hna_1 tpre :=
  let H := fresh in intro H;
  eapply (semax_call_id1_wow H);
  clear H;
  lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
  [ check_result_type
  | apply Logic.I
  | match_postcondition
  | prove_delete_temp
  | unify_postcondition_exps
  | tpre ].

(* the postcondition's two cases behind Definitions: Floyd's change_compspecs (forward's return) then never meets
   their CKS terms (a conversion that cost minutes in the kernel) *)
Definition hc4nb_hna_pnull (CSw: compspecs) (shl: share) (lp l0: val) (NS: list hnode4)
    (PS: list (val * share * peer)) (shd: share) (wg: val) (D: device) (head: val) : mpred :=
  @data_at CKS shl (tptr t_hnode4) l0 lp * hnodes_rep4 CSw l0 NS * peers_rep PS *
  device_rep shd wg D * ptable shd (d_ptab D) head.

Definition hc4nb_hna_pok (x25519: list byte -> list byte -> list byte) (CSw: compspecs) (shl: share) (lp: val)
    (NS: list hnode4) (PS: list (val * share * peer)) (shd: share) (wg: val) (D: device) (head: val)
    (PUB: list byte) (id: int64) (n p: val) (PSK: list byte) (r: int) : mpred :=
  @data_at CKS shl (tptr t_hnode4) n lp *
  hnodes_rep4 CSw n (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS) *
  peers_rep ((p, Ews, p_set_refs (setup_peer_val x25519 D wg p head PUB PSK id) r) :: PS) *
  entry_out Ews (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero) *
  device_rep shd wg D * ptable shd (d_ptab D) p.

Section Spec.
Variable x25519: list byte -> list byte -> list byte.
Variable CSw: compspecs.
#[local] Existing Instance HCS.
Definition hc4nb_hna_spec :=
  DECLARE HI._hnodes_add
  WITH gv: globals, shl: share, lp: val, l0: val, NS: list hnode4, PS: list (val * share * peer),
       shd: share, wg: val, D: device, head: val, shk: share, pk: val, PUB: list byte, id: int64
  PRE [ tptr (tptr t_hnode4), tptr t_dev, tptr tuchar, tulong ]
    PROP (writable_share shl; writable_share shd; readable_share shk; Zlength PUB = 32; hnodes_peers4 NS PS;
          peers_wf PS; is_pointer_or_null head)
    PARAMS (lp; wg; pk; Vlong id) GLOBALS (gv)
    SEP (@data_at CKS shl (tptr t_hnode4) l0 lp; hnodes_rep4 CSw l0 NS; peers_rep PS;
         device_rep shd wg D; ptable shd (d_ptab D) head; hbytes shk PUB pk; mem_mgr gv; wg_consts gv)
  POST [ tptr t_hnode4 ] EX n: val, EX p: val, EX PSK: list byte, EX r: int,
    PROP (pk_find PS PUB <> None -> n = nullval;
          n <> nullval -> Zlength PSK = 32 /\ 0 < Int.unsigned r < 2147483647)
    RETURN (n)
    SEP (if eq_dec n nullval then hc4nb_hna_pnull CSw shl lp l0 NS PS shd wg D head
         else hc4nb_hna_pok x25519 CSw shl lp NS PS shd wg D head PUB id n p PSK r;
         hbytes shk PUB pk; mem_mgr gv; wg_consts gv).
End Spec.

Lemma hc4nb_hna_pnull_fold (CSw: compspecs) shl lp l0 NS PS shd wg D head :
  @data_at CS4nb shl (tptr t_hnode4) l0 lp * hnodes_rep4 CSw l0 NS * peers_rep PS *
  device_rep shd wg D * ptable shd (d_ptab D) head |-- hc4nb_hna_pnull CSw shl lp l0 NS PS shd wg D head.
Proof.
  unfold hc4nb_hna_pnull.
  rewrite (@data_at_cs_eq CKS CS4nb _ shl (tptr t_hnode4) l0 l0 lp) by (apply JMeq_refl || reflexivity).
  apply derives_refl.
Qed.

Lemma hc4nb_hna_pok_fold x25519 (CSw: compspecs) shl lp NS PS shd wg D head PUB id n p PSK r :
  @data_at CS4nb shl (tptr t_hnode4) n lp *
  hnodes_rep4 CSw n (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS) *
  peer_rep Ews p (p_set_refs (setup_peer_val x25519 D wg p head PUB PSK id) r) * peers_rep PS *
  entry_out Ews (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero) *
  device_rep shd wg D * ptable shd (d_ptab D) p
  |-- hc4nb_hna_pok x25519 CSw shl lp NS PS shd wg D head PUB id n p PSK r.
Proof.
  unfold hc4nb_hna_pok.
  rewrite (@data_at_cs_eq CKS CS4nb _ shl (tptr t_hnode4) n n lp) by (apply JMeq_refl || reflexivity).
  rewrite hc4nb2_hn_peers_cons. unfold peer_item_rep. cancel.
Qed.

Section Add.
#[local] Existing Instance CS4nb.

Lemma hc4nb_hna_body' (x25519: list byte -> list byte -> list byte) (CSw: hc4nb_hna_csw) :
  cspecs_sub CS4 CSw ->
  @semax_body [] (hc4nb_G_hnodes_add x25519 CSw) CS4nb HI.f_hnodes_add (hc4nb_hna_spec x25519 CSw).
Proof.
  intros HSUB0. pose proof (hc4nb2_hn_sub_trans CSw HSUB0) as HSUB. clear HSUB0. start_function.
  match goal with Hh: is_pointer_or_null head |- _ => rename Hh into Hhead end.
  rewrite (@data_at_cs_eq CKS CS4nb _ shl (tptr t_hnode4) l0 l0 lp) by (apply JMeq_refl || reflexivity).
  apply -> seq_assoc. forward.
  forward_loop (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
      EX PS2: list (val * share * peer), EX it: val,
    PROP (NS = NS1 ++ NS2; PS = PS1 ++ PS2; hnodes_peers4 NS2 PS2; pk_find PS1 PUB = None)
    LOCAL (temp HI._it it; lvar HI._psk (tarray tuchar 32) v_psk; gvars gv; temp HI._l lp;
           temp HI._wg wg; temp HI._pub pk; temp HI._id (Vlong id))
    SEP (data_at_ Tsh (tarray tuchar 32) v_psk; data_at shl (tptr t_hnode4) l0 lp;
         hc4nb_seg CSw l0 it NS1; hnodes_rep4 CSw it NS2;
         peers_rep PS1; peers_rep PS2;
         device_rep shd wg D; ptable shd (d_ptab D) head; hbytes shk PUB pk; mem_mgr gv; wg_consts gv))
  continue: (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
      EX x: val * share * peer, EX PS2: list (val * share * peer), EX nx: val,
    PROP (NS = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; hnodes_peers4 NS2 PS2; hn_p N = peer_addr4 x;
          pk_find (PS1 ++ [x]) PUB = None)
    LOCAL (temp HI._it (hn_addr N); lvar HI._psk (tarray tuchar 32) v_psk; gvars gv; temp HI._l lp;
           temp HI._wg wg; temp HI._pub pk; temp HI._id (Vlong id))
    SEP (data_at_ Tsh (tarray tuchar 32) v_psk; data_at shl (tptr t_hnode4) l0 lp;
         hc4nb_seg CSw l0 (hn_addr N) NS1;
         @malloc_token CSw Ews t_hnode4 (hn_addr N);
         hc4nb_cell N nx (hn_addr N);
         @malloc_token CSw Ews t_peer (hn_p N);
         hnodes_rep4 CSw nx NS2;
         peers_rep PS1; peer_item_rep x; peers_rep PS2;
         device_rep shd wg D; ptable shd (d_ptab D) head; hbytes shk PUB pk; mem_mgr gv; wg_consts gv))
  break: (PROP (pk_find PS PUB = None)
    LOCAL (lvar HI._psk (tarray tuchar 32) v_psk; gvars gv; temp HI._l lp;
           temp HI._wg wg; temp HI._pub pk; temp HI._id (Vlong id))
    SEP (data_at_ Tsh (tarray tuchar 32) v_psk; data_at shl (tptr t_hnode4) l0 lp;
         hnodes_rep4 CSw l0 NS; peers_rep PS;
         device_rep shd wg D; ptable shd (d_ptab D) head; hbytes shk PUB pk; mem_mgr gv; wg_consts gv)).
  { Exists (@nil hnode4) NS (@nil (val * share * peer)) PS l0. entailer!. sep_apply (hc4nb_seg_nil CSw l0).
    cancel. }
  { Intros NS1 NS2 PS1 PS2 it.
    forward_if.
    { destruct NS2 as [|N NS2]. { rewrite hc4nb_rep_nil. Intros. subst. contradiction. }
      rewrite hc4nb_rep_cons. Intros nx.
      destruct (hc4nb_peers_cons N NS2 PS2 H4) as ([[a sha] P] & PS2' & EPS2 & Ha & HP2).
      subst PS2. rename PS2' into PS2. simpl in Ha. subst a.
      assert_PROP (isptr (hn_p N)).
      { rewrite hc4nb2_hn_peers_cons. simpl peer_item_rep. sep_apply (hc4nb_hna_peer_isptr sha (hn_p N) P). entailer!. }
      rewrite hc4nb_hna_cell_pn. Intros.
      forward.
      rewrite hc4nb2_hn_peers_cons. simpl peer_item_rep.
      assert (WS: writable_share sha).
      { subst PS; unfold peers_wf in H1; rewrite Forall_app in H1; destruct H1 as [_ H1]; inversion H1; auto. }
      sep_apply (hc4nb_hna_rs sha (hn_p N) P). Intros.
      forward_call (sha, offset_val 136 (hn_p N), hs_rstatic (p_hs P), shk, pk, PUB).
      { apply prop_right. rewrite H9. cbv [firstn Datatypes.length typeof eval_cast eval_field]. simpl. normalize. }
      sep_apply (modus_ponens_wand (hbytes sha (hs_rstatic (p_hs P)) (offset_val 136 (hn_p N))) (peer_rep sha (hn_p N) P)).
      sep_apply (hc4nb_hna_cell_fold N nx it).
      destruct (bytes_eqb (hs_rstatic (p_hs P)) PUB) eqn:EB.
      { forward_if; [|hc4nb_hna_absurd].
        forward.
        Exists nullval nullval (@nil byte) Int.zero. rewrite if_true by auto. entailer!.
        sep_apply (hc4nb_hna_reasm CSw l0 (hn_addr N) nx N NS1 NS2 PS1 (hn_p N, sha, P) PS2 eq_refl).
        unfold peer_item_rep.
        sep_apply (hc4nb_hna_pnull_fold CSw shl lp l0 (NS1 ++ N :: NS2) (PS1 ++ (hn_p N, sha, P) :: PS2) shd wg D head).
        cancel. }
      forward_if; [hc4nb_hna_absurd|].
      forward. subst it. Exists NS1 N NS2 PS1 (hn_p N, sha, P) PS2 nx.
      entailer!.
      rewrite hc4nb_hna_pk_find_app, H5; simpl; rewrite EB; auto. }
    { forward.
      assert_PROP (NS2 = []) by (entailer!; tauto). subst NS2.
      apply hc4nb_peers_nil in H4. subst PS2.
      rewrite !app_nil_r in *. subst NS PS.
      sep_apply (hc4nb_seg_rep CSw l0 it NS1 []). rewrite app_nil_r.
      entailer!. } }
  { Intros NS1 N NS2 PS1 x PS2 nx.
    rewrite hc4nb_hna_cell_pn. Intros.
    assert_PROP (is_pointer_or_null nx) by entailer!.
    forward.
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) PS2 nx. entailer!.
    { split; rewrite <- app_assoc; auto. }
    sep_apply (hc4nb_hna_cell_fold N nx (hn_addr N)).
    sep_apply (hc4nb_seg_snoc CSw l0 (hn_addr N) nx N NS1 eq_refl).
    rewrite hc4nb2_hn_peers_app. cancel. }
  Intros.
  eapply semax_seq';
    [ hc4nb_hna_setup (t_hnode4, gv)
        ltac:(apply prop_right; rewrite (hc4nb_hna_sizeof_node CSw HSUB); vm_compute; reflexivity);
      clear_Delta_specs; clear_MORE_POST;
      [ .. | hc4nb_hna_y ltac:(apply (hc4nb_hna_pre_node CSw HSUB)) ]
    | after_forward_call ].
  Intros n.
  destruct (eq_dec n nullval) as [En|En].
  { subst n. forward_if; [|hc4nb_hna_absurd]. forward. Exists nullval nullval (@nil byte) Int.zero.
    rewrite if_true by auto. entailer!.
    sep_apply (hc4nb_hna_pnull_fold CSw shl lp l0 NS PS shd wg D head). cancel. }
  Intros.
  sep_apply (hc4nb_hna_node_to4 CSw HSUB n).
  sep_apply (hc4nb_hna_new_split n). Intros.
  freeze FRT := (@malloc_token CSw Ews t_hnode4 n).
  forward_if.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    apply sepcon_valid_pointer1. do 10 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply hc4nb_hna_p_valid. }
  { exfalso; auto. }
  thaw FRT.
  rewrite <- seq_assoc.
  eapply semax_seq';
    [ hc4nb_hna_setup (t_peer, gv)
        ltac:(apply prop_right; rewrite (hc4nb_hna_sizeof_peer CSw HSUB); vm_compute; reflexivity);
      clear_Delta_specs; clear_MORE_POST;
      [ .. | hc4nb_hna_1 ltac:(apply (hc4nb_hna_pre_peer CSw HSUB)) ]
    | after_forward_call ].
  Intros p.
  freeze FRT := (@malloc_token CSw Ews t_hnode4 n).
  destruct (eq_dec p nullval) as [Ep|Ep].
  { subst p. forward. forward. forward_if; [|hc4nb_hna_absurd].
    thaw FRT. sep_apply (hc4nb_hna_new_free nullval Vundef n). sep_apply (hc4nb_hna_node_tow CSw HSUB n).
    forward_call (t_hnode4, n, gv).
    { rewrite if_false by auto. cancel. }
    forward. Exists nullval nullval (@nil byte) Int.zero. rewrite if_true by auto. entailer!.
    sep_apply (hc4nb_hna_pnull_fold CSw shl lp l0 NS PS shd wg D head). cancel. }
  Intros. sep_apply (hc4nb_hna_peer_to4 CSw HSUB p). Intros.
  freeze FRP := (@malloc_token CSw Ews t_peer p).
  forward. forward.
  forward_if; [contradiction|].
  forward_call (v_psk, 32, Tsh). Intros bs.
  forward_call tt. Intros b.
  freeze FR := (@data_at_ Noise.CS Ews t_peer p) (@field_at CS4nb Ews t_hnode4 (DOT HC._p) p n)
    (@field_at CS4nb Ews t_hnode4 (DOT HC._next) Vundef n) (hc4nb_hna_newmid n) (FRZL FRP) (FRZL FRT).
  forward_if (PROP () LOCAL (temp HI._t'5 (if Z.eq_dec (Z.land b 1) 0 then nullval else v_psk);
      temp HI._t'10 p; temp HI._t'3 p; temp HI._n n;
      lvar HI._psk (tarray tuchar 32) v_psk; gvars gv; temp HI._l lp; temp HI._wg wg; temp HI._pub pk;
      temp HI._id (Vlong id))
    SEP (FRZL FR; data_at Tsh (tarray tuchar 32) (map (fun b0 : Z => Vint (Int.repr b0)) bs) v_psk; mem_mgr gv;
         data_at shl (tptr t_hnode4) l0 lp; hnodes_rep4 CSw l0 NS; peers_rep PS;
         device_rep shd wg D; ptable shd (d_ptab D) head; hbytes shk PUB pk; wg_consts gv)).
  { forward. rewrite !Int.unsigned_repr in H8' by rep_lia. rewrite if_false by auto. entailer!. }
  { forward. rewrite hc4nb_hna_and1 in H8 by auto. rewrite if_true. entailer!.
    destruct (hc4nb_hna_land1 b) as [E|E]; auto. rewrite E in H8. discriminate H8. }
  set (q := if Z.eq_dec (Z.land b 1) 0 then nullval else v_psk).
  assert_PROP (isptr v_psk) by entailer!.
  assert (Hq: q = nullval \/ q = v_psk) by (unfold q; destruct (Z.eq_dec _ _); auto).
  thaw FR. Intros.
  forward.
  rewrite (@hc4nb_hna_psk_split CS4nb _ shk q v_psk bs) by auto.
  forward_call (gv, Ews, p, shd, wg, D, head, shk, pk, PUB, q, map Byte.repr bs, id).
  { cancel. }
  { rewrite Zlength_map; auto. }
  gather_SEP 5 12. rewrite <- (@hc4nb_hna_psk_split CS4nb _ shk q v_psk bs) by auto.
  forward_call tt. Intros r.
  forward.
  set (P0 := setup_peer_val x25519 D wg p head PUB (if eq_dec q nullval then zeros32 else map Byte.repr bs) id).
  sep_apply (hc4nb_hna_refs Ews p P0). Intros.
  forward.
  sep_apply (hc4nb_hna_inst (fun r0 => @field_at CS4nb Ews t_peer (DOT I._refcount) (Vint r0) p)
                           (fun r0 => peer_rep Ews p (p_set_refs P0 r0)) r).
  forward. forward. forward.
  thaw FRP. thaw FRT.
  sep_apply (hc4nb_hna_new_fold p l0 n).
  sep_apply (hc4nb_hna_rep_fold_new CSw n p l0 NS).
  forward. Exists n p (if eq_dec q nullval then zeros32 else map Byte.repr bs) r.
  destruct (eq_dec n nullval) as [Hn|_]; [contradiction|].
  apply andp_right.
  { apply prop_right. split; [intros C; contradiction|]. split; [|reflexivity].
    intros _. split; [|auto]. destruct (eq_dec q nullval); [reflexivity | rewrite Zlength_map; auto]. }
  unfold P0.
  sep_apply (hc4nb_hna_pok_fold x25519 CSw shl lp NS PS shd wg D head PUB id n p
               (if eq_dec q nullval then zeros32 else map Byte.repr bs) r).
  sep_apply (@data_at_data_at_ CS4nb Tsh (tarray tuchar 32)). cancel.
Time Qed.
End Add.

Lemma hc4nb_hna_body (x25519: list byte -> list byte -> list byte) (CSw: compspecs) :
  cspecs_sub CS4 CSw ->
  @semax_body [] (hc4nb_G_hnodes_add x25519 CSw) CS4nb HI.f_hnodes_add (hnodes_add4_spec x25519 CSw).
Proof. exact (hc4nb_hna_body' x25519 CSw). Qed.
