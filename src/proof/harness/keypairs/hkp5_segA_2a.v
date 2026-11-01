(* law keypairs, prologue A, piece 2a: statements 15..16 (n = draw_steps(); the loop adding the other peers: nondet_bytes(opub), bytes_eq, hnodes_add).
   States: hkp5_segA_defs.v. "Prologue A".
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.
Require Import VST.msl.iter_sepcon.
Require WgNoise.proof.protocol.prot_body3_consume_init.
Require WgNoise.proof.protocol.prot_rep_lemmas3.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

#[local] Instance hkp5A_2a_cce_H : change_composite_env HCS W_keypairs.
Proof. make_cs_preserve HCS W_keypairs. Defined.
#[local] Instance hkp5A_2a_cce_K : change_composite_env CKS W_keypairs.
Proof. make_cs_preserve CKS W_keypairs. Defined.

Lemma hkp5A_2a_conv_out sh n p : hout sh n p = @data_at_ W_keypairs sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_keypairs _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hkp5A_2a_conv_hnodep sh (v: val) p :
  @data_at CKS sh (tptr t_hnode4) v p = @data_at W_keypairs sh (tptr t_hnode4) v p.
Proof. rewrite (@data_at_change_composite CKS W_keypairs _ sh (tptr t_hnode4) v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hkp5A_2a_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hkp5A_2a_pub (bs: list Z) p :
  Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_keypairs Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. unfold hbytes. rewrite Zlength_map, Hl, hkp5A_2a_map_Vint by auto.
  rewrite (@data_at_change_composite HCS W_keypairs _ Tsh (tarray tuchar 32)
    (bytes (map Byte.repr bs)) (bytes (map Byte.repr bs)) (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hkp5A_2a_pub_back PUB p : Zlength PUB = 32 -> hbytes Tsh PUB p |-- hout Tsh 32 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hkp5A_2a_saddrs (PS: list (val * share * peer)) : saddrs PS = map peer_addr4 PS.
Proof. induction PS as [| [[a sh] P] PS IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma hkp5A_2a_hs_addr_inj p q : isptr p -> hs_addr q = hs_addr p -> q = p.
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

(* the new peer q is neither P's p nor one of PS *)
Lemma hkp5A_2a_new_facts p P q Q PS : peers_wf PS ->
  peer_rep Tsh p P * peers_rep ((q, Ews, Q) :: PS) |--
  !! (~ In q (p :: map peer_addr4 PS) /\ isptr q).
Proof.
  intros Hwf.
  assert (Hw: peers_wf ((p, Tsh, P) :: (q, Ews, Q) :: PS))
    by (constructor; [apply writable_share_top | constructor; [apply writable_Ews | exact Hwf]]).
  change (peer_rep Tsh p P * peers_rep ((q, Ews, Q) :: PS)) with (peers_rep ((p, Tsh, P) :: (q, Ews, Q) :: PS)).
  apply derives_trans with (!! NoDup (saddrs ((p, Tsh, P) :: (q, Ews, Q) :: PS)) &&
                            peers_rep ((p, Tsh, P) :: (q, Ews, Q) :: PS)).
  { apply andp_right; [| apply derives_refl].
    apply WgNoise.proof.protocol.prot_body3_consume_init.prot3_cin_nodup; exact Hw. }
  apply derives_extract_prop; intros Hnd.
  rewrite hkp5A_2a_saddrs in Hnd. cbn [map peer_addr4] in Hnd.
  inversion Hnd as [| ? ? Hn1 Hnd1]; subst. inversion Hnd1 as [| ? ? Hn2 Hnd2]; subst.
  unfold peers_rep. cbn [iter_sepcon]. unfold peer_item_rep at 1 2. unfold peer_rep at 2. Intros.
  apply prop_right. split.
  - intros [He | He]; [apply Hn1; left; symmetry; exact He | apply Hn2; exact He].
  - destruct H as [Hp _]; exact Hp.
Qed.

Lemma hkp5A_2a_sfind_none {A: Type} (l: list (val * share * A)) a : ~ In a (saddrs l) -> sfind l a = None.
Proof.
  induction l as [| [[x sh] v] l IH]; intros Hn; [reflexivity |].
  cbn. destruct (EqDec_val x a) as [He | He].
  - exfalso. apply Hn. left. exact He.
  - apply IH. intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma hkp5A_2a_inv_new x25519 F P NS PS T head n q D PUB PSK id r :
  hkp5A_inv F P NS PS [] T head -> isptr q -> ~ In q (f_p F :: map peer_addr4 PS) ->
  0 < Int.unsigned r < 2147483647 ->
  hkp5A_inv F P (mkHN4 n q (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS)
    ((q, Ews, p_set_refs (setup_peer_val x25519 D (f_w F) q head PUB PSK id) r) :: PS) []
    (t_add T (hs_addr q) Ews (mkEntry q IDX_HANDSHAKE Int.zero)) q.
Proof.
  intros (Hp & Hdev & Hsid & Hc & Hpv & Hnx & Hpk & Hnp & Hwf & Hnd & Hpa & Hka & Hall & Hhd & Hsa & Hsf & Hen & Hke & Hix & Hs1 & Hs2)
    Hq Hn Hr.
  cbn [map] in Hka, Hsa.
  assert (Hqp: q <> f_p F) by (intros He; apply Hn; left; symmetry; exact He).
  assert (Hqpa: ~ In q (map peer_addr4 PS)) by (intros He; apply Hn; right; exact He).
  assert (Haq: ~ In (hs_addr q) (saddrs (t_D T))).
  { rewrite Hsa. cbn [app]. intros Hi. apply in_app_or in Hi. destruct Hi as [Hi | Hi].
    - apply in_map_iff in Hi. destruct Hi as (x & Hx & Hi).
      apply Hqpa. apply hkp5A_2a_hs_addr_inj in Hx; [subst; exact Hi | exact Hq].

    - destruct Hi as [Hi | []]. apply Hqp. symmetry. apply hkp5A_2a_hs_addr_inj in Hi; [exact Hi | exact Hq]. }
  unfold hkp5A_inv; cbn [map].
  split; [exact Hp |]. split; [exact Hdev |]. split; [exact Hsid |]. split; [exact Hc |]. split; [exact Hpv |].
  split; [exact Hnx |]. split; [exact Hpk |].
  split. { unfold hnodes_peers4 in *; cbn. f_equal. exact Hnp. }
  split. { constructor; [apply writable_Ews | exact Hwf]. }
  split. { inversion Hnd as [| ? ? Hn1 Hnd1]; subst. constructor.
           - intros [He | He]; [apply Hqp; exact He | apply Hn1; exact He].
           - constructor; [exact Hqpa | exact Hnd1]. }
  split. { constructor; [exact Hq | exact Hpa]. }
  split. { constructor. }
  split.
  { constructor.
    - cbn. split; [reflexivity |]. split; [reflexivity |]. split; [exact Hr |].
      split; [repeat constructor; left; reflexivity |].
      right. destruct Hhd as [Hh | Hh]; [left; symmetry; exact Hh | right; right; exact Hh].
    - eapply Forall_impl; [| exact Hall]. intros [[x sh] Q]. intros (H1 & H2 & H3 & H4 & H5).
      split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |]. split; [exact H4 |].
      destruct H5 as [H5 | [H5 | H5]]; [left; exact H5 | right; left; exact H5 | right; right; right; exact H5]. }
  split. { right. left. reflexivity. }
  split. { cbn [t_add t_D saddrs map]. change (saddrs (t_D T)) with (map (fun '(x, _, _) => x) (t_D T)) in Hsa.
           cbn in Hsa |- *. rewrite Hsa. reflexivity. }
  split. { cbn [t_add t_D sfind]. match goal with |- context [if ?c then _ else _] => destruct c as [He | He] end.
           - exfalso. apply Hqp. apply hkp5A_2a_hs_addr_inj in He; [exact He | exact Hp].
           - exact Hsf. }
  split.
  { constructor.
    - unfold t_entry_d, t_entry; cbn. destruct (EqDec_val (hs_addr q) (hs_addr q)); [split; reflexivity | congruence].
    - rewrite Forall_forall in Hen |- *. intros x Hx. specialize (Hen x Hx).
      unfold t_entry_d, t_entry in *; cbn.
      destruct (EqDec_val (hs_addr q) (hs_addr x)) as [He | He].
      * exfalso. apply Hqpa. assert (isptr x) as Hxp by (rewrite Forall_forall in Hpa; apply Hpa; exact Hx).
        apply hkp5A_2a_hs_addr_inj in He; [subst; exact Hx | exact Hxp].
      * exact Hen. }
  split. { constructor. }
  split; [| split].
  2: { constructor; [reflexivity | exact Hs1]. }
  2: { cbn [t_add t_D]. constructor; [right; reflexivity | exact Hs2]. }
  replace (t_indices (t_add T (hs_addr q) Ews (mkEntry q IDX_HANDSHAKE Int.zero)) (t_L (t_add T (hs_addr q) Ews (mkEntry q IDX_HANDSHAKE Int.zero))))
    with (t_indices T (t_L T)); [exact Hix |].
  unfold t_indices. cbn [t_add t_L]. apply map_ext. intros a.
  unfold t_entry; cbn [t_add t_D sfind]. match goal with |- context [if ?c then _ else _] => destruct c as [He | He] end; [| reflexivity].
  subst a. rewrite (hkp5A_2a_sfind_none _ _ Haq). reflexivity.
Qed.

Lemma hkp5A_2a_head F P NS PS KE T head : hkp5A_inv F P NS PS KE T head -> isptr head.
Proof.
  intros (Hp & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpa & _ & _ & Hhd & _).
  destruct Hhd as [Hh | Hh]; [subst; exact Hp | rewrite Forall_forall in Hpa; apply Hpa; exact Hh].
Qed.

Lemma hkp5A_2a_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5A_S2 x25519 F FR) hkp5A_s2a (overridePost (hkp5A_S2 x25519 F FR) R).
Proof.
  intros Hx. unfold hkp5A_S2, hkp5A_s2a, hkp5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R0 P S w NS PS T head.
  unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
  forward_call tt. Intros nn.
  forward_for_simple_bound nn
    (EX i: Z, EX NS': list hnode4, EX PS': list (val * share * peer), EX T': tstate, EX head': val,
     PROPx [hkp5A_inv F P NS' PS' [] T' head']
     (LOCALx (temp KC._n (Vlong (Int64.repr nn)) :: hkp5A_temps R0 ++ hkp5_lvars F)
     (SEPx (hkp5A_world x25519 F R0 P T' head' ++ hk5_items (f_gv F) hkp5A_H0 ++ hkp5A_snaps0 F ++
            hkp5A_oth F (hkp5A_nhead NS') NS' PS' ++
            [data_at_ Ews (tptr (Tstruct KC._kent noattr)) (f_gv F KC._kes)] ++
            hkp5A_globs (f_gv F) S w ++ [FR])))).
  - Exists NS PS T head. unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
    entailer!.
  - Intros.
    unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
    rewrite (hkp5A_2a_conv_out Tsh 32 (f_opub F)).
    forward_call (f_opub F, 32, Tsh). Intros bs.
    rewrite (hkp5A_2a_pub bs) by tauto.
    assert (HPUBl: Zlength (a_PUB R0) = 32) by (unfold hkp5A_run_ok in H; tauto).
    forward_call (Tsh, f_opub F, map Byte.repr bs, Tsh, f_pub F, a_PUB R0).
    { rewrite Zlength_map, H5. entailer!. }
    { rewrite Zlength_map, H5, HPUBl. split; [reflexivity | rep_lia]. }
    forward_if.
    + rewrite <- (hkp5A_2a_conv_hnodep Ews (hkp5A_nhead NS') (f_gv F KC._others)).
      change (ptable Tsh (f_pt F) head') with (ptable Tsh (d_ptab (hkp5A_D x25519 F R0)) head').
      pose proof (hkp5A_2a_head _ _ _ _ _ _ _ H4) as Hhp.
      pose proof H4 as (_ & _ & _ & _ & _ & _ & _ & Hnp & Hwf & _).
      forward_call (f_gv F, Ews, f_gv F KC._others, hkp5A_nhead NS', NS', PS', Tsh, f_w F,
                    hkp5A_D x25519 F R0, head', Tsh, f_opub F, map Byte.repr bs, Int64.repr (2 + i)).
      { rewrite Zlength_map; assumption. }
      Intros vret. destruct vret as [[[n q] PSK] r]. cbn [fst snd] in *.
      sep_apply (hkp5A_2a_pub_back (map Byte.repr bs) (f_opub F)); [rewrite Zlength_map; assumption |].
      destruct (eq_dec n nullval) as [Hn | Hn].
      * Intros. rewrite (hkp5A_2a_conv_hnodep Ews (hkp5A_nhead NS') (f_gv F KC._others)).
        Exists NS' PS' T' head'.
        unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
        change (d_ptab (hkp5A_D x25519 F R0)) with (f_pt F). entailer!.
      * Intros. match goal with Hq: n <> nullval -> _ |- _ => destruct (Hq Hn) as [HPSK Hr] end.
        rewrite (hkp5A_2a_conv_hnodep Ews n (f_gv F KC._others)).
        set (Q := p_set_refs (setup_peer_val x25519 (hkp5A_D x25519 F R0) (f_w F) q head'
                                (map Byte.repr bs) PSK (Int64.repr (2 + i))) r).
        assert_PROP (~ In q (f_p F :: map peer_addr4 PS') /\ isptr q) as Hnd.
        { sep_apply (hkp5A_2a_new_facts (f_p F) P q Q PS' Hwf). entailer!. }
        destruct Hnd as [Hnin Hqp].
        pose proof WgNoise.proof.protocol.prot_rep_lemmas3.prot_rep_lemmas3 as (_ & _ & _ & _ & Hadd & _).
        sep_apply (Hadd Tsh (f_t F) T' (hs_addr q) Ews (mkEntry q IDX_HANDSHAKE Int.zero) writable_Ews).
        Exists (mkHN4 n q (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')
          ((q, Ews, Q) :: PS') (t_add T' (hs_addr q) Ews (mkEntry q IDX_HANDSHAKE Int.zero)) q.
        unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
        change (d_ptab (hkp5A_D x25519 F R0)) with (f_pt F).
        change (hkp5A_nhead (mkHN4 n q (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')) with n.
        entailer!.
        apply hkp5A_2a_inv_new; assumption.
    + forward. sep_apply (hkp5A_2a_pub_back (map Byte.repr bs) (f_opub F)); [rewrite Zlength_map; assumption |].
      Exists NS' PS' T' head'.
      unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
      entailer!.
  - Intros NS' PS' T' head'. destruct R. cbv match. Exists R0 P S w NS' PS' T' head'.
    unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app]. entailer!.
Qed.
