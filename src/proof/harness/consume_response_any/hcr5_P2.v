(* law consume_response_any, phase P2: statements 9..10 of main: n = draw_steps(); for (i = 0; i < n; i++) { nondet_bytes(pub, 32); hnodes_add(&peers, &wa, pub, 1 + i); }.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require WgNoise.harness.x_consume_response_any.code.

Require WgNoise.proof.protocol.prot3_shim_table2_pklookup.
Require WgNoise.proof.protocol.prot_body3_consume_init.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Local Open Scope Z_scope.

#[local] Instance hcr5_p2_cce_H : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.

Lemma hcr5_p2_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result (world) as an hbytes buffer (HCS) *)
Lemma hcr5_p2_pub (bs: list Z) p :
  Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_consume_response_any Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. unfold hbytes. rewrite Zlength_map, Hl, hcr5_p2_map_Vint by auto.
  rewrite (@data_at_change_composite HCS W_consume_response_any _ Tsh (tarray tuchar 32)
    (bytes (map Byte.repr bs)) (bytes (map Byte.repr bs)) (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_p2_pub_back PUB p : Zlength PUB = 32 -> hbytes Tsh PUB p |-- hout Tsh 32 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hcr5_p2_saddrs (PS: list (val * share * peer)) : saddrs PS = map peer_addr4 PS.
Proof. induction PS as [| [[a sh] P] PS IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma hcr5_p2_new_facts p P PS : peers_wf PS ->
  peers_rep ((p, Ews, P) :: PS) |-- !! (~ In p (map peer_addr4 PS) /\ isptr p).
Proof.
  intros Hwf. assert (Hw: peers_wf ((p, Ews, P) :: PS)) by (constructor; [apply writable_Ews | exact Hwf]).
  apply derives_trans with (!! NoDup (saddrs ((p, Ews, P) :: PS)) && peers_rep ((p, Ews, P) :: PS)).
  { apply andp_right; [apply WgNoise.proof.protocol.prot_body3_consume_init.prot3_cin_nodup; exact Hw | apply derives_refl]. }
  apply derives_extract_prop; intros Hnd.
  rewrite hcr5_p2_saddrs in Hnd. cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
  unfold peers_rep. cbn [iter_sepcon]. unfold peer_item_rep at 1. unfold peer_rep at 1. Intros.
  apply prop_right. split; [exact Hnin | destruct H as [Hp _]; exact Hp].
Qed.

Lemma hcr5_p2_pool PS T p P :
  hcr5_pool [] PS T ->
  hcr5_pool [] ((p, Ews, P) :: PS) (t_add T (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)).
Proof.
  intros [H1 H2]. unfold hcr5_pool in *; cbn [length firstn skipn] in *.
  split; [constructor |]. cbn. constructor; [cbn; auto | exact H2].
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the lists after a successful hnodes_add *)
Lemma hcr5_p2_list_new R L NS PS head nb n p PUB PSK r id :
  x25519_props x25519 -> Zlength PUB = 32 -> Zlength PSK = 32 -> 0 < Int.unsigned r < 2147483647 ->
  isptr p -> ~ In p (map peer_addr4 PS) ->
  hcr5_list_ok L [] NS PS head nb ->
  hcr5_list_ok L [] (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS)
    ((p, Ews, p_set_refs (setup_peer_val x25519 (hcr5_DAL x25519 R L) (l_wa L) p head PUB PSK id) r) :: PS)
    p nb.
Proof.
  intros Hx HPUB HPSK Hr Hp Hfresh (Hpok & Hwf & Hch & Hnp & Hnd & Hnb).
  unfold hcr5_list_ok. split; [| split; [| split; [| split; [| split]]]].
  - constructor; [| exact Hpok]. unfold hcr5_pok; simpl.
    repeat split; auto; try (simpl; lia).
    all: try (unfold hs_ok; simpl; repeat split; auto).
    all: try (unfold precomputed; destruct (andb _ _); auto).
    all: try apply Hx.
    all: repeat constructor; auto.
  - constructor; [apply writable_Ews | exact Hwf].
  - cbn. split; [reflexivity | exact Hch].
  - unfold hnodes_peers4 in *; cbn. f_equal. exact Hnp.
  - cbn. constructor; assumption.
  - destruct Hnb as [Hnb | Hnb]; [left; exact Hnb | right; right; exact Hnb].
Qed.

Lemma hcr5_P2_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SA x25519 gv L FR) hcr5_P2
    (overridePost (hcr5_SA x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_SA, hcr5_Delta, hcr5_R, hcr5_P2. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T.
  unfold hcr5_lvars, hcr5_scr, hcr5_world, hcr5_globs, hcr5_snaps0; cbn [app].
  forward_call tt. Intros nn.
  forward_for_simple_bound nn
    (EX i: Z, EX NS': list hnode4, EX PS': list (val * share * peer), EX head': val, EX T': tstate,
     PROPx [hcr5_run_ok R; hcr5_list_ok L [] NS' PS' head' nb; hcr5_pool [] PS' T']
     (LOCALx ([temp HR5._n (Vlong (Int64.repr nn)); temp HR5._nb nb] ++ hcr5_lvars gv L)
     (SEPx (hcr5_world x25519 R L NS' NS' head' T' ++
            [peers_rep PS'; hout Tsh 92 (l_img L)] ++ hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L)))).
  - Exists NS PS head T. unfold hcr5_world, hcr5_globs, hcr5_scr, hcr5_lvars, hcr5_snaps0; cbn [app]. entailer!.
  - Intros. unfold hcr5_world, hcr5_globs, hcr5_scr, hcr5_lvars, hcr5_snaps0; cbn [app].
    rewrite (hcr5_conv_bytes Tsh 32 (l_pub L)).
    forward_call (l_pub L, 32, Tsh). Intros bs.
    rewrite (hcr5_p2_pub bs) by tauto.
    rewrite <- (hcr5_conv_hnodep_v Tsh (hcr5_head NS') (l_peers L)).
    pose proof H4 as Hok. destruct H4 as (Hpok & Hwf & Hch & Hnp & Hnd & Hnb).
    change (ptable Tsh (l_pta L) head') with (ptable Tsh (d_ptab (hcr5_DAL x25519 R L)) head').
    assert_PROP (is_pointer_or_null head') as Hhp.
    { sep_apply (WgNoise.proof.protocol.prot3_shim_table2_pklookup.prot3_shim_table2_pkl_chain_ptr head' PS' Hch).
      entailer!. }
    forward_call (gv, Tsh, l_peers L, hcr5_head NS', NS', PS', Tsh, l_wa L, hcr5_DAL x25519 R L, head', Tsh,
                  l_pub L, map Byte.repr bs, Int64.repr (1 + i)).
    { rewrite Zlength_map; repeat split; first [assumption | auto with share | lia]. }
    Intros vret. destruct vret as [[[n p] PSK] r]. cbn [fst snd] in *.
    sep_apply (hcr5_p2_pub_back (map Byte.repr bs) (l_pub L)); [rewrite Zlength_map; assumption |].
    destruct (eq_dec n nullval) as [Hn | Hn].
    + Intros. rewrite (hcr5_conv_hnodep_v Tsh (hcr5_head NS') (l_peers L)).
      Exists NS' PS' head' T'. unfold hcr5_world, hcr5_globs, hcr5_scr, hcr5_lvars, hcr5_snaps0; cbn [app].
      change (d_ptab (hcr5_DAL x25519 R L)) with (l_pta L). entailer!.
    + Intros. destruct (H8 Hn) as [HPSK Hr].
      rewrite (hcr5_conv_hnodep_v Tsh n (l_peers L)).
      set (P := p_set_refs (setup_peer_val x25519 (hcr5_DAL x25519 R L) (l_wa L) p head'
                              (map Byte.repr bs) PSK (Int64.repr (1 + i))) r).
      assert_PROP (~ In p (map peer_addr4 PS') /\ isptr p) as Hnd2.
      { sep_apply (hcr5_p2_new_facts p P PS' Hwf). entailer!. }
      destruct Hnd2 as [Hnin Hpp].
      destruct HH as (Hx & Ha & Hxa & Hrep). destruct Hrep as (_ & _ & _ & _ & Hadd & _).
      sep_apply (Hadd Tsh (l_ita L) T' (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
      Exists (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')
        ((p, Ews, P) :: PS') p (t_add T' (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)).
      unfold hcr5_world, hcr5_globs, hcr5_scr, hcr5_lvars, hcr5_snaps0; cbn [app].
      change (d_ptab (hcr5_DAL x25519 R L)) with (l_pta L).
      change (hcr5_head (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')) with n.
      entailer!.
      split; [apply hcr5_p2_list_new; auto; rewrite Zlength_map; assumption | apply hcr5_p2_pool; assumption].
  - Intros NS' PS' head' T'. Exists R S NS' PS' head' nb T'.
    unfold hcr5_world, hcr5_globs, hcr5_scr, hcr5_lvars, hcr5_snaps0; cbn [app]. entailer!.
Qed.

End Phase.
