(* law handshake_receive: main's phase PC = n more peers (statements 15..16).
   From hrx5_SB to hrx5_SB (hrx5_defs.v; the cut: hrx5_cut.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require WgNoise.proof.protocol.prot3_shim_table2_pklookup.
Require WgNoise.proof.protocol.prot_body3_consume_init.
Require WgNoise.proof.protocol.prot_rep_lemmas3.
Local Open Scope Z_scope.

#[local] Instance hrx5_pc_cce_H : change_composite_env HCS W_handshake_receive.
Proof. make_cs_preserve HCS W_handshake_receive. Defined.

Lemma hrx5_pc_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result (world) as an hbytes buffer (HCS) *)
Lemma hrx5_pc_pub (bs: list Z) p :
  Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_handshake_receive Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. unfold hbytes. rewrite Zlength_map, Hl, hrx5_pc_map_Vint by auto.
  rewrite (@data_at_change_composite HCS W_handshake_receive _ Tsh (tarray tuchar 32)
    (bytes (map Byte.repr bs)) (bytes (map Byte.repr bs)) (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_pc_pub_back PUB p : Zlength PUB = 32 -> hbytes Tsh PUB p |-- hout Tsh 32 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hrx5_pc_saddrs (PS: list (val * share * peer)) : saddrs PS = map peer_addr4 PS.
Proof. induction PS as [| [[a sh] P] PS IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma hrx5_pc_new_facts p P PS : peers_wf PS ->
  peers_rep ((p, Ews, P) :: PS) |-- !! (~ In p (map peer_addr4 PS) /\ isptr p).
Proof.
  intros Hwf. assert (Hw: peers_wf ((p, Ews, P) :: PS)) by (constructor; [apply writable_Ews | exact Hwf]).
  apply derives_trans with (!! NoDup (saddrs ((p, Ews, P) :: PS)) && peers_rep ((p, Ews, P) :: PS)).
  { apply andp_right; [apply WgNoise.proof.protocol.prot_body3_consume_init.prot3_cin_nodup; exact Hw | apply derives_refl]. }
  apply derives_extract_prop; intros Hnd.
  rewrite hrx5_pc_saddrs in Hnd. cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
  unfold peers_rep. cbn [iter_sepcon]. unfold peer_item_rep at 1. unfold peer_rep at 1. Intros.
  apply prop_right. split; [exact Hnin | destruct H as [Hp _]; exact Hp].
Qed.

Lemma hrx5_pc_pool PS T p P :
  hrx5cr_pool [] PS T ->
  hrx5cr_pool [] ((p, Ews, P) :: PS) (t_add T (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)).
Proof.
  intros [H1 H2]. unfold hrx5cr_pool in *; cbn [length firstn skipn] in *.
  split; [constructor |]. cbn. constructor; [cbn; auto | exact H2].
Qed.

Section PC.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the invariant after a successful hnodes_add *)
Lemma hrx5_pc_inv_new R L sec birth NS PS T head nk n p PUB PSK r id :
  x25519_props x25519 -> Zlength PUB = 32 -> Zlength PSK = 32 -> 0 < Int.unsigned r < 2147483647 ->
  is_pointer_or_null head -> isptr p -> ~ In p (map peer_addr4 PS) ->
  hrx5_inv x25519 R L NS PS [] T head nk ->
  hrx5_inv x25519 R L (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS)
    ((p, Ews, p_set_refs (setup_peer_val x25519 (hrx5_DL x25519 R L sec birth) (l_wd L) p head PUB PSK id) r) :: PS)
    [] (t_add T (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)) p nk.
Proof.
  intros Hx HPUB HPSK Hr Hh Hp Hn (Hpok & Hwf & Hnd & Hch & Hnp & Hnk & HT).
  unfold hrx5_inv. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - constructor; [| exact Hpok]. unfold hrx5_pok; cbn.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [reflexivity | split; [exact Hr | split; [rep_lia | split; [exact Hh | auto]]]]].
    unfold hs_ok; cbn. unfold zeros32, zeros, precomputed.
    destruct (_ && _)%bool; rewrite ?Hx, ?Zlength_Zrepeat by lia; repeat split; auto.
  - constructor; [apply writable_Ews | exact Hwf].
  - cbn. constructor; assumption.
  - cbn. split; [reflexivity | exact Hch].
  - unfold hnodes_peers4 in *; cbn. f_equal. exact Hnp.
  - destruct Hnk as [Hnk | Hnk]; [left; exact Hnk | right; right; exact Hnk].
  - apply hrx5_pc_pool; exact HT.
Qed.

Lemma hrx5_PC_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SB x25519 gv L FR) hrx5_PC
    (overridePost (hrx5_SB x25519 gv L FR) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_SB, hrx5_Delta, hrx5_R, hrx5_PC. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w. Intros NS PS T head nk.
  unfold hrx5_lvars, hrx5_scr, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs; cbn [app].
  forward_call tt. Intros nn.
  forward_for_simple_bound nn
    (EX i: Z, EX NS': list hnode4, EX PS': list (val * share * peer), EX T': tstate, EX head': val,
     PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS' PS' [] T' head' nk]
     (LOCALx ([temp HM._n (Vlong (Int64.repr nn)); temp HM._nk nk; temp HM._now (Vlong (s_boot S));
               temp HM._m_lul (Vlong Int64.zero)] ++ hrx5_lvars gv L)
     (SEPx (hrx5_wcore x25519 R L sec birth T' head' PS' ++
            hrx5_rest x25519 R L NS' [] ++ hrx5_globs gv S w Int64.zero FR ++
            hrx5_rglobs gv Int64.zero ++ [hrx5_skb0 L] ++ hrx5_scr L)))).
  - Exists NS PS T head. unfold hrx5_lvars, hrx5_scr, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs; cbn [app].
    entailer!.
  - Intros. unfold hrx5_lvars, hrx5_scr, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs; cbn [app].
    rewrite (hrx5_conv_bytes Tsh 32 (l_pub L)).
    forward_call (l_pub L, 32, Tsh). Intros bs.
    rewrite (hrx5_pc_pub bs) by tauto.
    rewrite <- (hrx5_conv_hnodep_v Tsh (hrx5_head NS') (l_peers L)).
    pose proof H3 as Hok. destruct H3 as (Hpok & Hwf & Hnd & Hch & Hnp & Hnk & HT).
    change (ptable Tsh (l_ptd L) head') with (ptable Tsh (d_ptab (hrx5_DL x25519 R L sec birth)) head').
    assert_PROP (is_pointer_or_null head') as Hhp.
    { sep_apply (WgNoise.proof.protocol.prot3_shim_table2_pklookup.prot3_shim_table2_pkl_chain_ptr head' PS' Hch).
      entailer!. }
    forward_call (gv, Tsh, l_peers L, hrx5_head NS', NS', PS', Tsh, l_wd L, hrx5_DL x25519 R L sec birth, head', Tsh,
                  l_pub L, map Byte.repr bs, Int64.repr (1 + i)).
    { rewrite Zlength_map; repeat split; first [assumption | auto with share | lia]. }
    Intros vret. destruct vret as [[[n p] PSK] r]. cbn [fst snd] in *.
    sep_apply (hrx5_pc_pub_back (map Byte.repr bs) (l_pub L)); [rewrite Zlength_map; assumption |].
    destruct (eq_dec n nullval) as [Hn | Hn].
    + Intros. rewrite (hrx5_conv_hnodep_v Tsh (hrx5_head NS') (l_peers L)).
      Exists NS' PS' T' head'. unfold hrx5_lvars, hrx5_scr, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs; cbn [app].
      change (d_ptab (hrx5_DL x25519 R L sec birth)) with (l_ptd L). entailer!.
    + Intros. match goal with H: n <> nullval -> _ |- _ => destruct (H Hn) as [HPSK Hr] end.
      rewrite (hrx5_conv_hnodep_v Tsh n (l_peers L)).
      set (P := p_set_refs (setup_peer_val x25519 (hrx5_DL x25519 R L sec birth) (l_wd L) p head'
                              (map Byte.repr bs) PSK (Int64.repr (1 + i))) r).
      assert_PROP (~ In p (map peer_addr4 PS') /\ isptr p) as Hnd2.
      { sep_apply (hrx5_pc_new_facts p P PS' Hwf). entailer!. }
      destruct Hnd2 as [Hnin Hpp].
      destruct HH as (Hx & _).
      pose proof WgNoise.proof.protocol.prot_rep_lemmas3.prot_rep_lemmas3 as Hrep.
      destruct Hrep as (_ & _ & _ & _ & Hadd & _).
      sep_apply (Hadd Tsh (l_itd L) T' (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
      Exists (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')
        ((p, Ews, P) :: PS') (t_add T' (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)) p.
      unfold hrx5_lvars, hrx5_scr, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs; cbn [app].
      change (d_ptab (hrx5_DL x25519 R L sec birth)) with (l_ptd L).
      change (hrx5_head (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')) with n.
      entailer!.
      apply hrx5_pc_inv_new; auto. rewrite Zlength_map; assumption.
  - Intros NS' PS' T' head'. Exists R sec birth S w. Exists NS' PS' T' head' nk.
    unfold hrx5_lvars, hrx5_scr, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs; cbn [app]. entailer!.
Qed.

End PC.
