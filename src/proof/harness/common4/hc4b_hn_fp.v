(* the bodies of hnodes_free and hnodes_pick. *)
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
Require Import WgNoise.proof.harness.common4.hc4b_hn_common.
Require Import WgNoise.proof.harness.common4.hc4b_hn_sub.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HI := WgNoise.harness.x_consume_initiation_any.code.

(* a node's p and next fields at CS4, the rest of it hidden *)
Section Cell.
#[local] Existing Instance CKS.
Definition hn4_mid (N: hnode4) (l: val) : mpred :=
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) l *
  @field_at CKS Ews t_hnode4 (DOT HC._refs) (hn_refs N) l * spacer Ews 300 304 l *
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l.

Lemma hn4_cell_pn N nx l :
  hn4_cell N nx l =
  @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) l * @field_at CS4 Ews t_hnode4 (DOT HC._next) nx l * hn4_mid N l.
Proof.
  unfold hn4_cell, hn4_mid. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS CS4 _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4 _ Ews t_hnode4 (DOT HC._next) nx nx l) by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hn4_cell_fold N nx l :
  @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) l * @field_at CS4 Ews t_hnode4 (DOT HC._next) nx l * hn4_mid N l
  |-- hn4_cell N nx l.
Proof. rewrite hn4_cell_pn. apply derives_refl. Qed.

Lemma hn4_cell_ N nx l : hn4_cell N nx l |-- @data_at_ CS4 Ews t_hnode4 l.
Proof.
  unfold hn4_cell. sep_apply (@data_at_data_at_ CKS). rewrite (@data_at__cs_eq CKS CS4 hc4b_hn_CKS_4) by reflexivity. apply derives_refl.
Qed.
End Cell.

(* the world compspecs as a hypothesis that typeclass resolution does not take for the proof's compspecs CS4 *)
Definition hc4b_hn_csw := compspecs.
#[local] Typeclasses Opaque hc4b_hn_csw.

Section Pick.
#[local] Existing Instance CS4.

Lemma hc4b_hn_pick_body (CSw: hc4b_hn_csw) :
  @semax_body [] hc4_G_hnodes_pick CS4 WgNoise.harness.x_cookie_mac.code.f_hnodes_pick (hnodes_pick4_spec CSw).
Proof.
  start_function.
  forward_call tt. Intros k0.
  forward_loop (EX i: Z, EX k: Z,
    PROP (0 <= i < Zlength NS; 0 <= k <= Int64.max_unsigned)
    LOCAL (temp HC._l (hn_addr (Znth i NS)); temp HC._k (Vlong (Int64.repr k)))
    SEP (hnodes_seg4 CSw l (hn_addr (Znth i NS)) (sublist 0 i NS);
         hnodes_rep4 CSw (hn_addr (Znth i NS)) (sublist i (Zlength NS) NS)))
  break: (EX i: Z,
    PROP (0 <= i < Zlength NS)
    LOCAL (temp HC._l (hn_addr (Znth i NS)))
    SEP (hnodes_seg4 CSw l (hn_addr (Znth i NS)) (sublist 0 i NS);
         hnodes_rep4 CSw (hn_addr (Znth i NS)) (sublist i (Zlength NS) NS))).
  - destruct NS as [|N NS']; [contradiction|].
    Exists 0%Z k0. rewrite sublist_nil, sublist_same by auto. rewrite Znth_0_cons. simpl hnodes_seg4.
    rewrite hnodes_rep4_cons. Intros nx. subst l. entailer!.
    { rewrite Zlength_cons; pose proof (Zlength_nonneg NS'); lia. }
    rewrite hnodes_rep4_cons. Exists nx. entailer!.
  - Intros i k.
    rewrite (sublist_split i (i+1) (Zlength NS)) by lia. rewrite sublist_len_1 by lia.
    simpl app. rewrite hnodes_rep4_cons. Intros nx.
    rewrite hn4_cell_pn. Intros.
    forward_if (PROP () LOCAL (temp HC._t'2 (Val.of_bool (andb (negb (Z.eqb k 0)) (negb (eq_dec nx nullval))));
                               temp HC._l (hn_addr (Znth i NS)); temp HC._k (Vlong (Int64.repr k)))
                SEP (hnodes_seg4 CSw l (hn_addr (Znth i NS)) (sublist 0 i NS);
                     @malloc_token CSw Ews t_hnode4 (hn_addr (Znth i NS));
                     @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p (Znth i NS)) (hn_addr (Znth i NS));
                     @field_at CS4 Ews t_hnode4 (DOT HC._next) nx (hn_addr (Znth i NS));
                     hn4_mid (Znth i NS) (hn_addr (Znth i NS));
                     @malloc_token CSw Ews t_peer (hn_p (Znth i NS));
                     hnodes_rep4 CSw nx (sublist (i + 1) (Zlength NS) NS))).
    + forward.
      forward.
      entailer!.
      rewrite !Int64.unsigned_repr in H3 by rep_lia. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (eq_dec nx nullval) as [E|E]; [subst; reflexivity|].
      destruct nx; try contradiction; try reflexivity. simpl in PNnx; subst; contradiction E; reflexivity.
    + forward. entailer!.
      rewrite !Int64.unsigned_repr in H3 by rep_lia. replace k with 0 by lia. reflexivity.
    + forward_if.
      * forward. forward.
        assert (Hk: k <> 0 /\ nx <> nullval).
        { unfold typed_true in H3; destruct (Z.eqb_spec k 0), (EqDec_val nx nullval); simpl in H3; try discriminate; auto. }
        destruct Hk as [Hk Hnx].
        assert_PROP (nx = nullval <-> sublist (i+1) (Zlength NS) NS = []) as Hs by entailer!.
        assert (Hi: i + 1 < Zlength NS).
        { destruct (zlt (i + 1) (Zlength NS)); auto. exfalso. apply Hnx, Hs, sublist_nil_gen. lia. }
        assert_PROP (nx = hn_addr (Znth (i + 1) NS)) as Hnxa.
        { rewrite (sublist_split (i+1) (i+1+1) (Zlength NS)) by lia. rewrite sublist_len_1 by lia. simpl app.
          rewrite hnodes_rep4_cons. entailer!. }
        Exists (i + 1) (k - 1). rewrite <- Hnxa. entailer!.
        rewrite (sublist_split 0 i (i+1)) by lia. rewrite (sublist_len_1 i) by lia.
        eapply derives_trans;
          [|apply (hnodes_seg4_snoc CSw l (hn_addr (Znth i NS)) (hn_addr (Znth (i + 1) NS)) (Znth i NS) (sublist 0 i NS) eq_refl)].
        rewrite hn4_cell_pn. cancel.
      * forward. Exists i. entailer!.
        rewrite (sublist_split i (i+1) (Zlength NS)) by lia. rewrite sublist_len_1 by lia. simpl app.
        rewrite hnodes_rep4_cons. Exists nx. rewrite hn4_cell_pn. entailer!.
  - Intros i. forward. Exists i. entailer!.
    sep_apply (hnodes_seg4_rep CSw l (hn_addr (Znth i NS)) (sublist 0 i NS) (sublist i (Zlength NS) NS)).
    rewrite sublist_rejoin, sublist_same by lia. apply derives_refl.
Qed.
End Pick.

Section Free.
#[local] Existing Instance CS4.

Lemma hc4b_hn_node_free (CSw: compspecs) (HSUB: cspecs_sub CS4 CSw) N nx l :
  @malloc_token CSw Ews t_hnode4 l * hn4_cell N nx l |--
  @malloc_token CSw Ews t_hnode4 l * @data_at_ CSw Ews t_hnode4 l.
Proof.
  sep_apply (hn4_cell_ N nx l). rewrite sepcon_comm.
  apply (hc4b_hn_sub_tow CSw HSUB HC._hnode); try (vm_compute; discriminate); reflexivity.
Qed.

Lemma hc4b_hn_free_body (CSw: hc4b_hn_csw) :
  cspecs_sub CS4 CSw ->
  @semax_body [] (hc4_G_free CSw) CS4 HI.f_hnodes_free (hnodes_free4_spec CSw).
Proof.
  intros HSUB. start_function.
  forward_while (EX NS': list hnode4, EX l': val,
    PROP () LOCAL (temp HI._l l'; gvars gv)
    SEP (hnodes_rep4 CSw l' NS';
         iter_sepcon (fun N => @data_at_ CSw Ews t_peer (hn_p N)) NS'; mem_mgr gv)).
  - Exists NS l. entailer!.
  - entailer!.
  - destruct NS' as [|N NS'']. { rewrite hnodes_rep4_nil. Intros. subst. contradiction. }
    rewrite hnodes_rep4_cons. Intros nx. simpl iter_sepcon. Intros.
    assert_PROP (isptr (hn_p N)).
    { sep_apply (@data_at__local_facts CSw Ews t_peer (hn_p N)). Intros. entailer!.
      match goal with Hf: field_compatible t_peer [] _ |- _ => destruct Hf as [Hp _]; exact Hp end. }
    rewrite hn4_cell_pn. Intros.
    assert_PROP (is_pointer_or_null nx) by entailer!.
    forward. forward.
    forward_call (t_peer, hn_p N, gv).
    { rewrite if_false by (destruct (hn_p N); try contradiction; discriminate). cancel. }
    subst l'. sep_apply (hn4_cell_fold N nx (hn_addr N)).
    sep_apply (hc4b_hn_node_free CSw HSUB N nx (hn_addr N)).
    forward_call (t_hnode4, hn_addr N, gv).
    { rewrite if_false by (destruct (hn_addr N); try contradiction; discriminate). cancel. }
    forward.
    Exists (NS'', nx). entailer!. apply derives_refl.
  - forward. entailer!.
    match goal with Hn: nullval = nullval <-> _ |- _ => rewrite (proj1 Hn eq_refl) end.
    simpl. entailer!.
Qed.
End Free.
