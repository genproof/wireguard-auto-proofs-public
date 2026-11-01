(* law cookie_reply: phase P6 of main, statements
   48..50: np = hnodes_add(&peers, &wa, B's public key, 0), n = draw_steps, the loop of hnodes_add.

   (+ its children's files). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.

Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.proof.protocol.prot3_shim_table2_pklookup.
Require WgNoise.proof.protocol.prot_body3_consume_init.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* conversions                                                            *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p6_cceK : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p6_hnodep (sh: share) (v p: val) :
  @data_at CKS sh (tptr t_hnode4) v p = @data_at W_cookie_reply sh (tptr t_hnode4) v p.
Proof.
  rewrite (@data_at_change_composite CKS W_cookie_reply _ sh (tptr t_hnode4) v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcy5_p6_empty (sh: share) (p: val) :
  @data_at W_cookie_reply sh (tptr t_hnode4) nullval p =
  (@data_at CKS sh (tptr t_hnode4) nullval p * hnodes_rep4 W_cookie_reply nullval [] * peers_rep [])%logic.
Proof.
  rewrite hcy5_p6_hnodep. unfold peers_rep; simpl iter_sepcon; simpl hnodes_rep4.
  rewrite prop_true_andp by reflexivity. rewrite !sepcon_emp. reflexivity.
Qed.

Lemma hcy5_p6_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result (world) as an hbytes buffer (HCS) *)
Lemma hcy5_p6_pub (bs: list Z) p :
  Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_cookie_reply Tsh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. unfold hbytes. rewrite Zlength_map, Hl, hcy5_p6_map_Vint by auto.
  apply data_at_tarray_tuchar_cs.
Qed.

Lemma hcy5_p6_out (sh: share) (n: Z) (p: val) : hout sh n p = @data_at_ W_cookie_reply sh (tarray tuchar n) p.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

Lemma hcy5_p6_pub_back PUB p : Zlength PUB = 32 -> hbytes Tsh PUB p |-- hout Tsh 32 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

(* ---------------------------------------------------------------------- *)
(* B's public key inside hcy5_drest                                       *)
(* ---------------------------------------------------------------------- *)

Section NoiseCS.
#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition hcy5_p6_drest_rest (sh: share) (wg: val) (D: device) : mpred :=
  !! (field_compatible t_dev [] wg /\ id_ok (d_id D) /\ field_compatible t_sid [] (id_addr wg)) &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   (EX lk: val, field_at sh t_sid (DOT I._static_private) (bytes (id_priv (d_id D))) (id_addr wg) *
      field_at sh t_sid (DOT I._lock) lk (id_addr wg) *
      field_at sh t_sid (DOT I._has_identity) (Val.of_bool (id_has (d_id D))) (id_addr wg) *
      spacer sh 69 72 (id_addr wg)) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hcy5_p6_drest_split sh wg D :
  hcy5_drest sh wg D |-- hbytes sh (id_pub (d_id D)) (id_addr wg) * hcy5_p6_drest_rest sh wg D.
Proof.
  unfold hcy5_drest, hcy5_p6_drest_rest, identity_rep. Intros lk.
  assert_PROP (field_compatible t_sid [] (id_addr wg)) as FC by entailer!.
  unfold_data_at (data_at _ t_sid _ (id_addr wg)).
  rewrite (field_at_data_at sh t_sid (DOT I._static_public)).
  rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite isptr_offset_val_zero by (destruct FC; auto).
  unfold hbytes. pose proof H0 as [Hp _]. rewrite Hp.
  rewrite (@data_at_tarray_tuchar_cs HCS Noise.CS).
  Exists lk. entailer!.
Qed.

Lemma hcy5_p6_drest_join sh wg D :
  hbytes sh (id_pub (d_id D)) (id_addr wg) * hcy5_p6_drest_rest sh wg D |-- hcy5_drest sh wg D.
Proof.
  unfold hcy5_drest, hcy5_p6_drest_rest, identity_rep. Intros lk.
  pose proof H0 as [Hp Hq]. Exists lk.
  unfold_data_at (data_at sh t_sid _ (id_addr wg)).
  rewrite (field_at_data_at sh t_sid (DOT I._static_public)).
  rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite isptr_offset_val_zero by (destruct H1; auto).
  unfold hbytes. rewrite Hp.
  rewrite (@data_at_tarray_tuchar_cs HCS Noise.CS).
  entailer!.
Qed.

End NoiseCS.

(* ---------------------------------------------------------------------- *)
(* the pool, the lists                                                    *)
(* ---------------------------------------------------------------------- *)

(* A's table during P6: the peers' handshake entries (index 0, as setup_peer leaves them), none hashed *)
Definition hcy5_p6_T (PS: list (val * share * peer)) : tstate :=
  mkT (map (hcy5_hent (fun _ => Int.zero)) (map peer_addr4 PS)) [].

Lemma hcy5_p6_T_add PS p sh P :
  t_add (hcy5_p6_T PS) (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero) = hcy5_p6_T ((p, sh, P) :: PS).
Proof. reflexivity. Qed.

Lemma hcy5_p6_T_ok PS : hcy5_T_ok PS [] (hcy5_p6_T PS).
Proof.
  split; [| constructor].
  exists (fun _ => nullval), (fun _ => Int.zero). split; [reflexivity | constructor].
Qed.

Lemma hcy5_p6_saddrs (PS: list (val * share * peer)) : saddrs PS = map peer_addr4 PS.
Proof. induction PS as [| [[a sh] P] PS IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma hcy5_p6_new_facts p P PS : peers_wf PS ->
  (peers_rep ((p, Ews, P) :: PS) |-- !! (~ In p (map peer_addr4 PS) /\ isptr p))%logic.
Proof.
  intros Hwf. assert (Hw: peers_wf ((p, Ews, P) :: PS)) by (constructor; [apply writable_Ews | exact Hwf]).
  apply derives_trans with (!! NoDup (saddrs ((p, Ews, P) :: PS)) && peers_rep ((p, Ews, P) :: PS))%logic.
  { apply andp_right; [apply WgNoise.proof.protocol.prot_body3_consume_init.prot3_cin_nodup; exact Hw | apply derives_refl]. }
  apply derives_extract_prop; intros Hnd.
  rewrite hcy5_p6_saddrs in Hnd. cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
  unfold peers_rep. cbn [iter_sepcon]. unfold peer_item_rep at 1. unfold peer_rep at 1. Intros.
  apply prop_right. split; [exact Hnin | destruct H as [Hp _]; exact Hp].
Qed.

Lemma hcy5_p6_dconf (v v': @reptype CKS t_hnode4) a :
  (@data_at CKS Ews t_hnode4 v a * @data_at CKS Ews t_hnode4 v' a |-- FF)%logic.
Proof.
  apply data_at_conflict; [apply readable_nonidentity, writable_readable, writable_Ews |].
  assert (Hs: 0 < @sizeof CKS t_hnode4) by (vm_compute; reflexivity). lia.
Qed.

Lemma hcy5_p6_node_notin n v l NS :
  (@data_at CKS Ews t_hnode4 v n * hnodes_rep4 W_cookie_reply l NS |-- !! (~ In n (map hn_addr NS)))%logic.
Proof.
  revert l. induction NS as [| N NS IH]; intros l.
  - simpl. entailer!.
  - simpl hnodes_rep4. Intros nx. subst l.
    destruct (eq_dec (hn_addr N) n) as [<- | Hne].
    + sep_apply (hcy5_p6_dconf v (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
      rewrite ?FF_sepcon, ?sepcon_FF. apply FF_left.
    + sep_apply (IH nx). Intros. entailer!.
      match goal with Hx: In _ (map _ (_ :: _)) |- False => simpl in Hx; destruct Hx as [Heq | Hin]; [congruence | contradiction] end.
Qed.

Lemma hcy5_p6_nodes_new l N NS :
  (hnodes_rep4 W_cookie_reply l (N :: NS) |-- !! (~ In (hn_addr N) (map hn_addr NS)))%logic.
Proof.
  simpl hnodes_rep4. Intros nx. subst l.
  sep_apply (hcy5_p6_node_notin (hn_addr N) (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) nx NS). entailer!.
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* every new peer satisfies the invariant *)
Lemma hcy5_p6_pok R L p head PUB PSK id r :
  0 < Int.unsigned r < 2147483647 ->
  hcy5_pok L [] (p, Ews, p_set_refs (setup_peer_val x25519 (hcy5_DA x25519 R L) (l_wa L) p head PUB PSK id) r).
Proof.
  intros Hr. unfold hcy5_pok. cbv beta iota.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Hr |]. split; [reflexivity |].
  constructor; [left; reflexivity |]. constructor; [left; reflexivity |].
  constructor; [left; reflexivity | constructor].
Qed.

Lemma hcy5_p6_lists_new R L NS PS n p PUB PSK id r :
  0 < Int.unsigned r < 2147483647 ->
  hcy5_lists_ok L [] NS PS -> ~ In p (map peer_addr4 PS) -> ~ In n (map hn_addr NS) ->
  hcy5_lists_ok L [] (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS)
    ((p, Ews, p_set_refs (setup_peer_val x25519 (hcy5_DA x25519 R L) (l_wa L) p (hcy5_phead PS) PUB PSK id) r)
       :: PS).
Proof.
  intros Hr (Hf & Hnp & Hd1 & Hd2 & Hch) Hp Hn. split; [| split; [| split; [| split]]].
  - constructor; [apply hcy5_p6_pok; auto | auto].
  - unfold hnodes_peers4 in *; cbn [map hn_p peer_addr4]; f_equal; auto.
  - cbn [map peer_addr4]; constructor; auto.
  - cbn [map hn_addr]; constructor; auto.
  - cbn [pk_chain hcy5_phead]. split; [reflexivity | exact Hch].
Qed.

Lemma hcy5_p6_lists_nil L : hcy5_lists_ok L [] [] [].
Proof. repeat split; try constructor. Qed.

Lemma hcy5_p6_np_cons pubB NS PS np N x :
  hcy5_np_ok pubB NS PS np -> hcy5_np_ok pubB (N :: NS) (x :: PS) np.
Proof.
  intros [H | (N' & a & P & Hin & Ha & Hr)]; [left; auto |].
  right; exists N', a, P; split; [simpl; right; auto | auto].
Qed.

Lemma hcy5_p6_wf L PS : Forall (hcy5_pok L []) PS -> peers_wf PS.
Proof. unfold peers_wf. apply Forall_impl. intros [[a sh] P] (H & _). subst; apply writable_Ews. Qed.

(* the state's SEP during P6 (A's table: hcy5_p6_T PS) *)
Definition hcy5_p6_sep (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (S: shim) (m c rp: val)
  (Q: hcy5_pkt) (rr CK: list byte) (CM: cookie_msg) (NS: list hnode4) (PS: list (val * share * peer))
  : list mpred :=
  hcy5_aside x25519 R L (hcy5_p6_T PS) NS PS ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
  hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
  [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L)] ++
  hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR.

Lemma hcy5_P6_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S5b x25519 xaead_enc gv L FR) hcy5_P6
    (overridePost (hcy5_S6 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S5b, hcy5_Delta, hcy5_R, hcy5_P6. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  sep_apply (hcy5_p6_drest_split Tsh (l_wb L) (hcy5_DB x25519 R L)).
  assert_PROP (Zlength (hcy5_pubB x25519 R L) = 32) as HPB.
  { unfold hcy5_p6_drest_rest. entailer!. match goal with Hx: id_ok _ |- _ => apply Hx end. }
  Intros.
  change (ptable Tsh (l_pta L) nullval) with (ptable Tsh (d_ptab (hcy5_DA x25519 R L)) nullval).
  rewrite (hcy5_p6_empty Tsh (l_peers L)). flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_peers L, nullval, @nil hnode4, @nil (val * share * peer), Tsh, l_wa L,
                hcy5_DA x25519 R L, nullval, Tsh, id_addr (l_wb L), hcy5_pubB x25519 R L, Int64.repr 0).
  { repeat split; first [assumption | solve [auto with share] | apply Forall_nil | constructor | reflexivity]. }
  Intros vret. destruct vret as [[[n p] PSK] r]. cbn [fst snd] in *.
  change (hbytes Tsh (hcy5_pubB x25519 R L) (id_addr (l_wb L)))
    with (hbytes Tsh (id_pub (d_id (hcy5_DB x25519 R L))) (id_addr (l_wb L))).
  sep_apply (hcy5_p6_drest_join Tsh (l_wb L) (hcy5_DB x25519 R L)).
  apply semax_pre with
    (EX NS: list hnode4, EX PS: list (val * share * peer),
     PROPx [hcy5_lists_ok L [] NS PS; hcy5_np_ok (hcy5_pubB x25519 R L) NS PS n]
     (LOCALx ([temp HY._np n; temp HY._cns nullval;
               temp HY._len (Vlong (Int64.repr (q_n Q))); temp HY._msg m; temp HY._copy c;
               temp HY._reply rp] ++ hcy5_lvars gv L)
     (SEPx (hcy5_p6_sep gv L FR R S m c rp Q rr CK CM NS PS)))).
  { destruct (eq_dec n nullval) as [Hn | Hn].
    - subst n. Intros.
      Exists (@nil hnode4) (@nil (val * share * peer)).
      unfold hcy5_p6_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs,
        hcy5_lvars; cbn [app].
      change (d_ptab (hcy5_DA x25519 R L)) with (l_pta L).
      change (itable Tsh (l_ita L) {| t_D := []; t_L := [] |}) with (itable Tsh (l_ita L) (hcy5_p6_T [])).
      change (hcy5_head []) with nullval. change (hcy5_phead []) with nullval.
      entailer!.
      split; [apply hcy5_p6_lists_nil | left; reflexivity].
    - Intros. match goal with Hx: n <> nullval -> _ |- _ => destruct (Hx Hn) as [HPSK Hr] end.
      set (P0 := p_set_refs (setup_peer_val x25519 (hcy5_DA x25519 R L) (l_wa L) p nullval
                               (hcy5_pubB x25519 R L) PSK (Int64.repr 0)) r).
      assert_PROP (~ In p (map peer_addr4 []) /\ isptr p) as Hnd.
      { sep_apply (hcy5_p6_new_facts p P0 [] ltac:(constructor)). entailer!. }
      destruct Hnd as [Hnin Hpp].
      sep_apply (prot_rep3_pool_add Tsh (l_ita L) (mkT [] []) (hs_addr p) Ews
                   (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
      Exists [mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)] [(p, Ews, P0)].
      unfold hcy5_p6_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs,
        hcy5_lvars; cbn [app].
      change (d_ptab (hcy5_DA x25519 R L)) with (l_pta L).
      change (hcy5_head [mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)]) with n.
      change (hcy5_phead [(p, Ews, P0)]) with p.
      change (t_add {| t_D := []; t_L := [] |} (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero))
        with (hcy5_p6_T [(p, Ews, P0)]).
      entailer!.
      2: apply derives_refl.
      split.
      + apply (hcy5_p6_lists_new R L [] [] n p _ PSK (Int64.repr 0) r Hr (hcy5_p6_lists_nil L));
          [intros [] | intros []].
      + right. exists (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)), p, P0.
        split; [left; reflexivity | split; reflexivity]. }
  Intros NS PS. unfold hcy5_lvars; cbn [app].
  forward_call tt. Intros nn.
  forward_for_simple_bound nn
    (EX i: Z, EX NS': list hnode4, EX PS': list (val * share * peer),
     PROPx [hcy5_lists_ok L [] NS' PS'; hcy5_np_ok (hcy5_pubB x25519 R L) NS' PS' n]
     (LOCALx [temp HY._n (Vlong (Int64.repr nn)); temp HY._np n; temp HY._cns nullval;
              temp HY._len (Vlong (Int64.repr (q_n Q))); temp HY._msg m; temp HY._copy c; temp HY._reply rp;
              lvar HY._wa t_dev (l_wa L); lvar HY._wb t_dev (l_wb L);
              lvar HY._ita t_itab (l_ita L); lvar HY._itb t_itab (l_itb L);
              lvar HY._pta t_ptab (l_pta L); lvar HY._ptb t_ptab (l_ptb L);
              lvar HY._ib t_mident (l_ib L); lvar HY._skb t_skb (l_skb L);
              lvar HY._raw_a (tarray tuchar 32) (l_rawa L); lvar HY._raw_b (tarray tuchar 32) (l_rawb L);
              lvar HY._pub (tarray tuchar 32) (l_pub L); lvar HY._secret (tarray tuchar 32) (l_secret L);
              lvar HY._cookie__1 (tarray tuchar 16) (l_cookie L); lvar HY._k (tarray tuchar 32) (l_k L);
              lvar HY._enc (tarray tuchar 32) (l_enc L); lvar HY._img (tarray tuchar 64) (l_img L);
              lvar HY._img2 (tarray tuchar 64) (l_img2 L); lvar HY._peers (tptr t_hnode4) (l_peers L);
              lvar HY._da t_devsnap (l_da L); lvar HY._db t_devsnap (l_db L);
              lvar HY._sks t_skbsnap (l_sks L); lvar HY._ss t_shimsnap (l_ss L);
              lvar HY._pt (tarray tuchar 16) (l_pt L); gvars gv]
     (SEPx (hcy5_p6_sep gv L FR R S m c rp Q rr CK CM NS' PS')))).
  - Exists NS PS. entailer!.
  - unfold hcy5_p6_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs;
      cbn [app].
    rewrite (hcy5_p6_out Tsh 32 (l_pub L)).
    forward_call (l_pub L, 32, Tsh). Intros bs.
    rewrite (hcy5_p6_pub bs) by tauto.
    rewrite <- (hcy5_p6_hnodep Tsh (hcy5_head NS') (l_peers L)).
    match goal with Hl: hcy5_lists_ok _ _ NS' PS' |- _ => pose proof Hl as (Hpok & Hnp & Hd1 & Hd2 & Hch) end.
    assert_PROP (is_pointer_or_null (hcy5_phead PS')) as Hhp.
    { sep_apply (WgNoise.proof.protocol.prot3_shim_table2_pklookup.prot3_shim_table2_pkl_chain_ptr
                   (hcy5_phead PS') PS' Hch). entailer!. }
    change (ptable Tsh (l_pta L) (hcy5_phead PS'))
      with (ptable Tsh (d_ptab (hcy5_DA x25519 R L)) (hcy5_phead PS')).
    forward_call (gv, Tsh, l_peers L, hcy5_head NS', NS', PS', Tsh, l_wa L, hcy5_DA x25519 R L, hcy5_phead PS',
                  Tsh, l_pub L, map Byte.repr bs, Int64.repr (1 + i)).
    { rewrite Zlength_map. repeat split; first [assumption | solve [auto with share] | eapply hcy5_p6_wf; eauto]. }
    Intros vret. destruct vret as [[[n' p'] PSK'] r']. cbn [fst snd] in *.
    sep_apply (hcy5_p6_pub_back (map Byte.repr bs) (l_pub L)); [rewrite Zlength_map; assumption |].
    destruct (eq_dec n' nullval) as [Hn | Hn].
    + Intros.
      Exists NS' PS'.
      unfold hcy5_p6_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs;
        cbn [app].
      change (d_ptab (hcy5_DA x25519 R L)) with (l_pta L).
      entailer!.
    + Intros. match goal with Hx: n' <> nullval -> _ |- _ => destruct (Hx Hn) as [HPSK Hr] end.
      set (P0 := p_set_refs (setup_peer_val x25519 (hcy5_DA x25519 R L) (l_wa L) p' (hcy5_phead PS')
                               (map Byte.repr bs) PSK' (Int64.repr (1 + i))) r').
      assert_PROP (~ In p' (map peer_addr4 PS') /\ isptr p') as Hnd.
      { sep_apply (hcy5_p6_new_facts p' P0 PS' (hcy5_p6_wf L PS' Hpok)). entailer!. }
      destruct Hnd as [Hnin Hpp].
      assert_PROP (~ In n' (map hn_addr NS')) as Hnn.
      { sep_apply (hcy5_p6_nodes_new n'
          (mkHN4 n' p' (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)) NS'). entailer!. }
      sep_apply (prot_rep3_pool_add Tsh (l_ita L) (hcy5_p6_T PS') (hs_addr p') Ews
                   (mkEntry p' IDX_HANDSHAKE Int.zero) writable_Ews).
      rewrite (hcy5_p6_T_add PS' p' Ews P0).
      Exists (mkHN4 n' p' (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS')
        ((p', Ews, P0) :: PS').
      unfold hcy5_p6_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs;
        cbn [app].
      change (d_ptab (hcy5_DA x25519 R L)) with (l_pta L).
      change (hcy5_head (mkHN4 n' p' (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS'))
        with n'.
      change (hcy5_phead ((p', Ews, P0) :: PS')) with p'.
      entailer!.
      all: try apply derives_refl.
      split; [apply hcy5_p6_lists_new; assumption | apply hcy5_p6_np_cons; assumption].
  - Intros NS' PS'. unfold hcy5_S6.
    Exists R S m c rp Q nonce rr. Exists CK CM NS' PS' (hcy5_p6_T PS') n.
    unfold hcy5_p6_sep, hcy5_lvars; cbn [app]. entailer!.
    apply hcy5_p6_T_ok.
Qed.

End Phase.
