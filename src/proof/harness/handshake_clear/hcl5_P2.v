(* law handshake_clear: main's phase P2, statements 4..5: n = draw_steps(); for (i = 0; i < n; i++) { nondet_bytes(pub, 32); hnodes_add(&peers, &w, pub, i); } (hnodes_add4: a new node and peer at the head, its entry_out joins the pool with hcl5_rep's t_add).
   (states: hcl5_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require WgNoise.harness.x_handshake_clear.code.

Require WgNoise.proof.protocol.prot3_shim_table2_pklookup.
Require WgNoise.proof.protocol.prot_body3_consume_init.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

#[local] Instance hcl5_p2_cce_H : change_composite_env HCS W_handshake_clear.
Proof. make_cs_preserve HCS W_handshake_clear. Defined.

Lemma hcl5_p2_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result (world) as an hbytes buffer (HCS) *)
Lemma hcl5_p2_pub (bs: list Z) p :
  Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_handshake_clear Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. unfold hbytes. rewrite Zlength_map, Hl, hcl5_p2_map_Vint by auto.
  rewrite (@data_at_change_composite HCS W_handshake_clear _ Tsh (tarray tuchar 32)
    (bytes (map Byte.repr bs)) (bytes (map Byte.repr bs)) (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcl5_p2_pub_back PUB p : Zlength PUB = 32 -> hbytes Tsh PUB p |-- hout Tsh 32 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hcl5_p2_saddrs (PS: list (val * share * peer)) : saddrs PS = map peer_addr4 PS.
Proof. induction PS as [| [[a sh] P] PS IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma hcl5_p2_hs_addr_inj p q : isptr p -> hs_addr q = hs_addr p -> q = p.
Proof.
  intros Hp H. destruct p as [| | | | | b o]; try contradiction. destruct q as [| | | | | b' o']; try discriminate.
  unfold hs_addr, offset_val in H.
  assert (Hb: b' = b) by congruence.
  assert (Ho: Ptrofs.add o' (Ptrofs.repr OFS_PEER_HANDSHAKE) = Ptrofs.add o (Ptrofs.repr OFS_PEER_HANDSHAKE))
    by congruence.
  apply (f_equal (fun z => Ptrofs.sub z (Ptrofs.repr OFS_PEER_HANDSHAKE))) in Ho.
  rewrite !Ptrofs.sub_add_opp, !Ptrofs.add_assoc, Ptrofs.add_neg_zero, !Ptrofs.add_zero in Ho.
  subst; reflexivity.
Qed.

(* the table invariant after a new peer's entry joined the pool *)
Lemma hcl5_p2_T_new PS T p sh P :
  isptr p -> ~ In p (map peer_addr4 PS) -> hcl5_T_ok PS [] T ->
  hcl5_T_ok ((p, sh, P) :: PS) [] (t_add T (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)).
Proof.
  intros Hp Hn (H1 & H2 & H3 & H4). unfold hcl5_T_ok, t_add; cbn [t_D].
  split; [| split; [| split]].
  - change (hs_addr p :: saddrs (t_D T) = hs_addr p :: map (fun x => hs_addr (peer_addr4 x)) PS).
    rewrite H1. reflexivity.
  - constructor; [reflexivity | exact H2].
  - constructor.
    + cbn. unfold t_entry_d, t_entry; cbn. destruct (EqDec_val (hs_addr p) (hs_addr p)); [reflexivity | congruence].
    + rewrite Forall_forall in H3 |- *. intros x Hx. specialize (H3 x Hx).
      unfold t_entry_d, t_entry in *; cbn.
      destruct (EqDec_val (hs_addr p) (hs_addr (peer_addr4 x))) as [He | He].
      * exfalso. apply Hn. symmetry in He. apply hcl5_p2_hs_addr_inj in He; [| exact Hp]. rewrite <- He. apply in_map, Hx.
      * exact H3.
  - constructor.
Qed.

Section P2.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p2_new_facts p P PS : peers_wf PS ->
  peers_rep ((p, Ews, P) :: PS) |-- !! (~ In p (map peer_addr4 PS) /\ isptr p).
Proof.
  intros Hwf. assert (Hw: peers_wf ((p, Ews, P) :: PS)) by (constructor; [apply writable_Ews | exact Hwf]).
  apply derives_trans with (!! NoDup (saddrs ((p, Ews, P) :: PS)) && peers_rep ((p, Ews, P) :: PS)).
  { apply andp_right; [apply WgNoise.proof.protocol.prot_body3_consume_init.prot3_cin_nodup; exact Hw | apply derives_refl]. }
  apply derives_extract_prop; intros Hnd.
  rewrite hcl5_p2_saddrs in Hnd. cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
  unfold peers_rep. cbn [iter_sepcon]. unfold peer_item_rep at 1. unfold peer_rep at 1. Intros.
  apply prop_right. split; [exact Hnin | destruct H as [Hp _]; exact Hp].
Qed.

(* the invariant of the peers after a successful hnodes_add *)
Lemma hcl5_p2_inv_new R L NS PS T head n p PUB PSK r id :
  x25519_props x25519 -> Zlength PUB = 32 -> Zlength PSK = 32 -> 0 < Int.unsigned r < 2147483647 ->
  isptr p -> ~ In p (map peer_addr4 PS) ->
  hcl5_inv L NS PS [] T head ->
  hcl5_inv L (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS)
    ((p, Ews, p_set_refs (setup_peer_val x25519 (hcl5_D x25519 R L) (l_w L) p head PUB PSK id) r) :: PS)
    [] (t_add T (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)) p.
Proof.
  intros Hx HPUB HPSK Hr Hp Hn (Hpok & Hwf & Hch & Hnp & HT & Hsl).
  unfold hcl5_inv. split; [| split; [| split; [| split; [| split]]]].
  - constructor; [| exact Hpok]. unfold hcl5_pok; cbn.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| exact Hr].
    unfold hs_ok; cbn. unfold zeros32, zeros, precomputed.
    destruct (_ && _)%bool; rewrite ?Hx, ?Zlength_Zrepeat by lia; repeat split; auto.
  - constructor; [apply writable_Ews | exact Hwf].
  - cbn. split; [reflexivity | exact Hch].
  - unfold hnodes_peers4 in *; cbn. f_equal. exact Hnp.
  - apply hcl5_p2_T_new; assumption.
  - constructor; [| exact Hsl]. cbn. repeat constructor; left; reflexivity.
Qed.

Lemma hcl5_P2_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_SA x25519 gv L FR) hcl5_P2
    (overridePost (hcl5_SA x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_SA, hcl5_Delta, hcl5_R, hcl5_P2. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head.
  unfold hcl5_lvars, hcl5_scr, hcl5_world, hcl5_globs, hcl5_snaps0; cbn [app].
  forward_call tt. Intros nn.
  forward_for_simple_bound nn
    (EX i: Z, EX NS': list hnode4, EX PS': list (val * share * peer), EX T': tstate, EX head': val,
     PROPx [hcl5_inv L NS' PS' [] T' head']
     (LOCALx ([temp HC._n (Vlong (Int64.repr nn))] ++ hcl5_lvars gv L)
     (SEPx (hcl5_world x25519 R L NS' NS' T' head' ++
            [peers_rep PS'] ++ hcl5_globs gv S w FR ++ hcl5_snaps0 L ++ hcl5_scr L)))).
  - Exists NS PS T head. unfold hcl5_world, hcl5_globs, hcl5_scr, hcl5_lvars, hcl5_snaps0; cbn [app]. entailer!.
  - Intros. unfold hcl5_world, hcl5_globs, hcl5_scr, hcl5_lvars, hcl5_snaps0; cbn [app].
    rewrite (hcl5_conv_bytes Tsh 32 (l_pub L)).
    forward_call (l_pub L, 32, Tsh). Intros bs.
    rewrite (hcl5_p2_pub bs) by tauto.
    rewrite <- (hcl5_conv_hnodep_v Tsh (hcl5_head NS') (l_peers L)).
    pose proof H3 as Hok. destruct H3 as (Hpok & Hwf & Hch & Hnp & HT & Hsl).
    change (ptable Tsh (l_pt L) head') with (ptable Tsh (d_ptab (hcl5_D x25519 R L)) head').
    assert_PROP (is_pointer_or_null head') as Hhp.
    { sep_apply (WgNoise.proof.protocol.prot3_shim_table2_pklookup.prot3_shim_table2_pkl_chain_ptr head' PS' Hch).
      entailer!. }
    forward_call (gv, Tsh, l_peers L, hcl5_head NS', NS', PS', Tsh, l_w L, hcl5_D x25519 R L, head', Tsh,
                  l_pub L, map Byte.repr bs, Int64.repr i).
    { rewrite Zlength_map; repeat split; first [assumption | auto with share | lia]. }
    Intros vret. destruct vret as [[[n p] PSK] r]. cbn [fst snd] in *.
    sep_apply (hcl5_p2_pub_back (map Byte.repr bs) (l_pub L)); [rewrite Zlength_map; assumption |].
    destruct (eq_dec n nullval) as [Hn | Hn].
    + Intros. rewrite (hcl5_conv_hnodep_v Tsh (hcl5_head NS') (l_peers L)).
      Exists NS' PS' T' head'. unfold hcl5_world, hcl5_globs, hcl5_scr, hcl5_lvars, hcl5_snaps0; cbn [app].
      change (d_ptab (hcl5_D x25519 R L)) with (l_pt L). entailer!.
    + Intros. destruct (H6 Hn) as [HPSK Hr].
      rewrite (hcl5_conv_hnodep_v Tsh n (l_peers L)).
      set (P := p_set_refs (setup_peer_val x25519 (hcl5_D x25519 R L) (l_w L) p head'
                              (map Byte.repr bs) PSK (Int64.repr i)) r).
      assert_PROP (~ In p (map peer_addr4 PS') /\ isptr p) as Hnd.
      { sep_apply (hcl5_p2_new_facts p P PS' Hwf). entailer!. }
      destruct Hnd as [Hnin Hpp].
      destruct HH as (Hx & Hrep). destruct Hrep as (_ & _ & _ & _ & Hadd & _).
      sep_apply (Hadd Tsh (l_it L) T' (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
      Exists (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')
        ((p, Ews, P) :: PS') (t_add T' (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)) p.
      unfold hcl5_world, hcl5_globs, hcl5_scr, hcl5_lvars, hcl5_snaps0; cbn [app].
      change (d_ptab (hcl5_D x25519 R L)) with (l_pt L).
      change (hcl5_head (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')) with n.
      entailer!.
      apply hcl5_p2_inv_new; auto. rewrite Zlength_map; assumption.
  - Intros NS' PS' T' head'. Exists R S w NS' PS' T' head'.
    unfold hcl5_world, hcl5_globs, hcl5_scr, hcl5_lvars, hcl5_snaps0; cbn [app]. entailer!.
Qed.

End P2.
