(* law handshake_receive: B8 branch R segment D: the node loop's glue: pure lemmas, the node list, the init / ifb / ifc /
   incr steps and the loop from hrx5_B8RD_P0 to hrx5_B8RD_X modulo the parts CHK and HIF. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_chk.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_hif.
#[local] Existing Instance W_handshake_receive.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* pure lemmas                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RDg_len_snap T NS PS : Zlength NS = Zlength PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength NS.
Proof. intros H. unfold hnodes_snapped4. rewrite Zlength_map, Zlength_combine. lia. Qed.

Lemma hrx5_B8RDg_addr_snap T NS PS : Zlength NS = Zlength PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  revert PS; induction NS as [| N NS IH]; intros [| x PS] H; try reflexivity.
  - rewrite Zlength_cons, Zlength_nil in H. pose proof (Zlength_nonneg NS). lia.
  - rewrite !Zlength_cons in H. destruct x as [[a sh] P]. cbn. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8RDg_Znth_snap T NS PS k : Zlength NS = Zlength PS -> 0 <= k < Zlength NS ->
  Znth k (hnodes_snapped4 T NS PS) = hn_snapshot4 T (Znth k NS) (Znth k PS).
Proof.
  intros H Hk. unfold hnodes_snapped4. rewrite Znth_map by (rewrite Zlength_combine; lia).
  rewrite Znth_combine by exact H. reflexivity.
Qed.

Lemma hrx5_B8RDg_len NS PS : hnodes_peers4 NS PS -> Zlength NS = Zlength PS.
Proof.
  unfold hnodes_peers4. intros H.
  rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS), H. reflexivity.
Qed.

Lemma hrx5_B8RDg_hnp NS PS k : hnodes_peers4 NS PS -> 0 <= k < Zlength NS -> hn_p (Znth k NS) = peer_addr4 (Znth k PS).
Proof.
  intros H Hk. pose proof (hrx5_B8RDg_len _ _ H) as HL. unfold hnodes_peers4 in H.
  rewrite <- (Znth_map k hn_p) by lia. rewrite H, Znth_map by lia. reflexivity.
Qed.

Lemma hrx5_B8RDg_nh_snoc T p l x : hrx5_B8R_nh T p (l ++ [x]) =
  hrx5_B8R_nh T p l + (if andb (negb (veqb (peer_addr4 x) p)) (vin (hs_addr (peer_addr4 x)) (t_L T)) then 1 else 0).
Proof.
  unfold hrx5_B8R_nh. rewrite filter_app, Zlength_app. cbn [filter].
  destruct (andb _ _); reflexivity.
Qed.

Lemma hrx5_B8RDg_firstn_S {A} {d: Inhabitant A} (l: list A) k : 0 <= k < Zlength l ->
  firstn (Z.to_nat (k + 1)) l = firstn (Z.to_nat k) l ++ [Znth k l].
Proof.
  intros Hk. rewrite <- !sublist_firstn. rewrite (sublist_split 0 k (k + 1)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hrx5_B8RDg_skipn_S {A} {d: Inhabitant A} (l: list A) k : 0 <= k < Zlength l ->
  skipn (Z.to_nat k) l = Znth k l :: skipn (Z.to_nat (k + 1)) l.
Proof.
  intros Hk. rewrite <- !sublist_skip by lia. rewrite (sublist_split k (k + 1) (Zlength l)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hrx5_B8RDg_skipn_end {A} (l: list A) : skipn (Z.to_nat (Zlength l)) l = [].
Proof. rewrite Zlength_correct, Nat2Z.id. apply skipn_all. Qed.

Lemma hrx5_B8RDg_firstn_end {A} (l: list A) : firstn (Z.to_nat (Zlength l)) l = l.
Proof. rewrite Zlength_correct, Nat2Z.id. apply firstn_all. Qed.

Lemma hrx5_B8RDg_head_map A B : map hn_addr A = map hn_addr B -> hrx5_head A = hrx5_head B.
Proof. destruct A, B; cbn; intros H; try discriminate; [reflexivity | injection H as H _; exact H]. Qed.

Lemma hrx5_B8RDg_in_firstn {A} {d: Inhabitant A} (l: list A) i k : 0 <= i < k -> k <= Zlength l ->
  In (Znth i l) (firstn (Z.to_nat k) l).
Proof.
  intros Hi Hk. rewrite <- sublist_firstn.
  replace (Znth i l) with (Znth i (sublist 0 k l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma hrx5_B8RDg_in_skipn {A} {d: Inhabitant A} (l: list A) i k : 0 <= k <= i -> i < Zlength l ->
  In (Znth i l) (skipn (Z.to_nat k) l).
Proof.
  intros Hi Hk. rewrite <- sublist_skip by lia.
  replace (Znth i l) with (Znth (i - k) (sublist k (Zlength l) l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma hrx5_B8RDg_head_skip A B k : map hn_addr A = map hn_addr B ->
  hrx5_head (skipn k A) = hrx5_head (skipn k B).
Proof. intros H. apply hrx5_B8RDg_head_map. rewrite <- !skipn_map, H. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the node list                                                           *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hrx5_B8RDg_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.

Lemma hrx5_B8RDg_seg_app l e NS1 NS2 :
  hrx5_B8RD_seg l e NS1 * hnodes_rep4 W_handshake_receive e NS2 |--
  hnodes_rep4 W_handshake_receive l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hrx5_B8RDg_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hrx5_B8RD_seg l e NS1 *
  (@malloc_token W_handshake_receive Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_handshake_receive Ews t_peer (hn_p N)) |--
  hrx5_B8RD_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hrx5_B8RDg_vp l NS : hnodes_rep4 W_handshake_receive l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hrx5_B8RDg_pn l NS : hnodes_rep4 W_handshake_receive l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hrx5_B8RDg_vp : valid_pointer.

Lemma hrx5_B8RDg_rep_head l NS : hnodes_rep4 W_handshake_receive l NS |-- !! (l = hrx5_head NS).
Proof. destruct NS as [| N NS]; simpl; [Intros; entailer! | Intros nx; entailer!]. Qed.

Lemma hrx5_B8RDg_nin_aux a v l NS :
  @data_at CKS Ews t_hnode4 v a * hnodes_rep4 W_handshake_receive l NS |-- !! (~ In a (map hn_addr NS)).
Proof.
  revert l; induction NS as [| N NS IH]; intros l; simpl.
  - Intros. apply prop_right. auto.
  - Intros nx. subst l.
    destruct (eq_dec a (hn_addr N)) as [-> | Hne].
    + sep_apply (@data_at_conflict CKS Ews t_hnode4 v
                   (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
      { apply readable_nonidentity, writable_readable, writable_Ews. }
      rewrite !FF_sepcon. apply FF_left.
    + sep_apply (IH nx). Intros. apply prop_right. intros [Hx | Hx]; [congruence | contradiction].
Qed.

Lemma hrx5_B8RDg_nodup l NS : hnodes_rep4 W_handshake_receive l NS |-- !! NoDup (map hn_addr NS).
Proof.
  revert l; induction NS as [| N NS IH]; intros l; simpl.
  - Intros. apply prop_right. constructor.
  - Intros nx. subst l.
    match goal with |- ?A |-- _ => apply derives_trans with (!! (~ In (hn_addr N) (map hn_addr NS)) && A) end.
    { apply andp_right; [| apply derives_refl].
      sep_apply (hrx5_B8RDg_nin_aux (hn_addr N) (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) nx NS).
      Intros. apply prop_right. assumption. }
    apply derives_extract_prop; intros Hn. sep_apply (IH nx). Intros. apply prop_right. constructor; assumption.
Qed.

Lemma hrx5_B8RDg_seg_vp a l e NS : In a (map hn_addr NS) -> hrx5_B8RD_seg l e NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [| N NS IH]; intros l Ha; simpl in *; [contradiction |].
  Intros nx. subst l. destruct Ha as [<- | Ha].
  - apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable, writable_Ews | simpl; lia].
  - apply sepcon_valid_pointer2, IH, Ha.
Qed.

Lemma hrx5_B8RDg_rep_vp a l NS : In a (map hn_addr NS) -> hnodes_rep4 W_handshake_receive l NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [| N NS IH]; intros l Ha; simpl in *; [contradiction |].
  Intros nx. subst l. destruct Ha as [<- | Ha].
  - apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable, writable_Ews | simpl; lia].
  - apply sepcon_valid_pointer2, IH, Ha.
Qed.

Lemma hrx5_B8RDg_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_handshake_receive Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_handshake_receive _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_B8RDg_seg_snocW l e N nx NS1 : e = hn_addr N ->
  hrx5_B8RD_seg l e NS1 *
  (@malloc_token W_handshake_receive Ews t_hnode4 e *
   @data_at W_handshake_receive Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_handshake_receive Ews t_peer (hn_p N)) |--
  hrx5_B8RD_seg l nx (NS1 ++ [N]).
Proof. intros He. rewrite <- hrx5_B8RDg_node_W. apply hrx5_B8RDg_seg_snoc, He. Qed.

(* the cell of the node of peer (q, Ews, Q) as the W constant hrx5_B8RD_nv (no reptype conversion in the loop) *)
Lemma hrx5_B8RDg_nvN_eq q sn Q nx l :
  @data_at CKS Ews t_hnode4 (q, (hsnap_val sn, (Vint (p_refs Q), (prsnap_val Q, nx)))) l =
  @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q sn Q nx) l.
Proof. unfold hrx5_B8RD_nv. apply hrx5_B8RDg_node_W. Qed.

Lemma hrx5_B8RDg_rep_cons_nv l a q sn Q NS :
  hnodes_rep4 W_handshake_receive l (mkHN4 a q (hsnap_val sn) (Vint (p_refs Q)) (prsnap_val Q) :: NS) =
  (!! (l = a) && EX nx: val,
     @malloc_token W_handshake_receive Ews t_hnode4 l *
     @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q sn Q nx) l *
     @malloc_token W_handshake_receive Ews t_peer q *
     hnodes_rep4 W_handshake_receive nx NS).
Proof.
  unfold hnodes_rep4 at 1; fold (hnodes_rep4 W_handshake_receive). cbn [hn_p hn_snap hn_refs hn_rest hn_addr].
  apply pred_ext.
  - Intros nx. apply andp_right; [apply prop_right; auto |]. Exists nx.
    apply sepcon_derives; [| apply derives_refl]. apply sepcon_derives; [| apply derives_refl].
    apply sepcon_derives; [apply derives_refl |].
    apply derives_refl'. apply hrx5_B8RDg_nvN_eq.
  - Intros nx. apply andp_right; [apply prop_right; auto |]. Exists nx.
    apply sepcon_derives; [| apply derives_refl]. apply sepcon_derives; [| apply derives_refl].
    apply sepcon_derives; [apply derives_refl |].
    apply derives_refl'. symmetry. apply hrx5_B8RDg_nvN_eq.
Qed.

Lemma hrx5_B8RDg_seg_snoc_nv l e q sn Q nx NS1 :
  hrx5_B8RD_seg l e NS1 *
  (@malloc_token W_handshake_receive Ews t_hnode4 e *
   @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q sn Q nx) e *
   @malloc_token W_handshake_receive Ews t_peer q) |--
  hrx5_B8RD_seg l nx (NS1 ++ [mkHN4 e q (hsnap_val sn) (Vint (p_refs Q)) (prsnap_val Q)]).
Proof.
  unfold hrx5_B8RD_nv.
  exact (hrx5_B8RDg_seg_snocW l e (mkHN4 e q (hsnap_val sn) (Vint (p_refs Q)) (prsnap_val Q)) nx NS1 eq_refl).
Qed.

(* the node without its link, and the link: the load of nd->next without unfolding hrx5_B8RD_nv *)
Definition hrx5_B8RDg_nhead (q: val) (sn: hsnap) (Q: peer) (l: val) : mpred :=
  (@field_at W_handshake_receive Ews t_hnode4 (DOT HM._p) q l *
  @field_at W_handshake_receive Ews t_hnode4 (DOT HM._snap) (hsnap_val sn) l *
  @field_at W_handshake_receive Ews t_hnode4 (DOT HM._refs) (Vint (p_refs Q)) l *
  spacer Ews 300 304 l *
  @field_at W_handshake_receive Ews t_hnode4 (DOT HM._rest) (prsnap_val Q) l)%logic.

Lemma hrx5_B8RDg_next_split q sn Q nx l :
  @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q sn Q nx) l =
  (hrx5_B8RDg_nhead q sn Q l * @field_at W_handshake_receive Ews t_hnode4 (DOT HM._next) nx l)%logic.
Proof.
  unfold hrx5_B8RD_nv, hrx5_B8RDg_nhead. unfold_data_at (data_at _ _ _ l).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hrx5_B8RDg_seg_snoc_snap l T N x nx NS1 q Q : x = (q, Ews, Q) -> hn_p N = q ->
  hrx5_B8RD_seg l (hn_addr N) NS1 *
  (@malloc_token W_handshake_receive Ews t_hnode4 (hn_addr N) *
   @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q (hs_snap_cur T q Q) Q nx) (hn_addr N) *
   @malloc_token W_handshake_receive Ews t_peer q) |--
  hrx5_B8RD_seg l nx (NS1 ++ [hn_snapshot4 T N x]).
Proof.
  intros -> Hq. unfold hn_snapshot4. rewrite <- Hq.
  apply hrx5_B8RDg_seg_snoc_nv.
Qed.

Lemma hrx5_B8RDg_next_join q sn Q nx l :
  hrx5_B8RDg_nhead q sn Q l * @field_at W_handshake_receive Ews t_hnode4 (DOT HM._next) nx l |--
  @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q sn Q nx) l.
Proof. rewrite hrx5_B8RDg_next_split. apply derives_refl. Qed.

Lemma hrx5_B8RDg_nhk0 T a : hrx5_B8R_nh T a (firstn (Z.to_nat 0) []) = 0.
Proof. reflexivity. Qed.

Section Loop.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variables (gv: globals) (L: hrx5_loc) (R: hrx5_run) (NS: list hnode4) (PS: list (val * share * peer))
  (KE: list kent4) (T: tstate) (head nk: val) (j: Z) (a tg: val) (Pf: peer) (Tf: tstate) (D: device) (FRM: mpred).
Variables (vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0
           vpath: val).

Local Notation DL := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).
Local Notation HYP := (hrx5_B8RD_hyp x25519 L R NS PS KE T head nk j a tg Tf).
Local Notation P0 := (hrx5_B8RD_P0 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation X := (hrx5_B8RD_X gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation INV := (hrx5_B8RD_inv gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation QQ := (hrx5_B8RD_Q gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation Q0 := (hrx5_B8RD_Q0 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation Q1 := (hrx5_B8RD_Q1 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation CONT := (hrx5_B8RD_cont gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul
  vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath).
Local Notation NHK := (hrx5_B8RD_nhk PS T a).

Definition hrx5_B8RDg_I : environ -> mpred := EX k: Z, INV k.

Definition hrx5_B8RDg_A (k: Z) : environ -> mpred :=
  EX nx: val, EX q: val, EX Q: peer, QQ k nx q Q (NHK k) [].

Lemma hrx5_B8RDg_init_ok (Rp: ret_assert) : HYP ->
  semax DL P0 hrx5_B8RD_s0 (overridePost hrx5_B8RDg_I Rp).
Proof.
  intros HY. destruct Rp as [Rn Rb Rc Rr].
  unfold hrx5_B8RD_P0, hrx5_Delta, hrx5_B8RD_s0. simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B8RD_fix, hrx5_B8RD_lcr, hrx5_lvars; cbn [app].
  destruct HY as (Hinv & Hj & Hja & Htg & Hnd & HTf).
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & _ & Hnp & _); apply hrx5_B8RDg_len, Hnp).
  assert (HA: map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS) by (apply hrx5_B8RDg_addr_snap, HL).
  assert_PROP (is_pointer_or_null (hrx5_head (hnodes_snapped4 T NS PS))) as Hpn.
  { sep_apply (hrx5_B8RDg_pn (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  forward.
  unfold hrx5_B8RDg_I. Exists 0. unfold hrx5_B8RD_inv, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars;
    cbn [app].
  unfold hrx5_B8RD_at, hrx5_B8RD_nhk. simpl firstn. simpl skipn. simpl hrx5_B8RD_seg.
  rewrite <- (hrx5_B8RDg_head_map _ _ HA).
  entailer!.
Qed.

(* the loop body's ret_assert *)
Definition hrx5_B8RDg_RL (Rp: ret_assert) : ret_assert := loop1_ret_assert CONT (overridePost X Rp).

Lemma hrx5_B8RDg_ifb_ok (Rp: ret_assert) k : HYP ->
  semax DL (INV k) hrx5_B8RD_ifb (overridePost (hrx5_B8RDg_A k) (hrx5_B8RDg_RL Rp)).
Proof.
  intros HY. unfold hrx5_B8RDg_RL. destruct Rp as [Rn Rb Rc Rr].
  unfold hrx5_B8RD_inv, hrx5_Delta, hrx5_B8RD_ifb. simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app]. Intros.
  destruct HY as (Hinv & Hj & Hja & Htg & Hnd & HTf).
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & _ & Hnp & _); apply hrx5_B8RDg_len, Hnp).
  destruct (Z.eq_dec k (Zlength NS)) as [Hk | Hk].
  - subst k.
    assert (E1: skipn (Z.to_nat (Zlength NS)) (hnodes_snapped4 T NS PS) = []).
    { rewrite <- (hrx5_B8RDg_len_snap T NS PS HL). apply hrx5_B8RDg_skipn_end. }
    assert (E2: hrx5_B8RD_at NS (Zlength NS) = nullval).
    { unfold hrx5_B8RD_at. rewrite hrx5_B8RDg_skipn_end. reflexivity. }
    assert (E3: firstn (Z.to_nat (Zlength NS)) (hnodes_snapped4 T NS PS) = hnodes_snapped4 T NS PS).
    { rewrite <- (hrx5_B8RDg_len_snap T NS PS HL). apply hrx5_B8RDg_firstn_end. }
    assert (E4: firstn (Z.to_nat (Zlength NS)) PS = PS) by (rewrite HL; apply hrx5_B8RDg_firstn_end).
    unfold hrx5_B8RD_nhk. rewrite E1, E2, E3, E4.
    forward_if; [contradiction |].
    forward. unfold hrx5_B8RD_X, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app].
    sep_apply (hrx5_B8RDg_seg_app (hrx5_head (hnodes_snapped4 T NS PS)) nullval (hnodes_snapped4 T NS PS) []).
    rewrite app_nil_r.
    entailer!.
  - assert (Hk': 0 <= k < Zlength NS) by lia. clear Hk.
    rewrite (hrx5_B8RDg_skipn_S (hnodes_snapped4 T NS PS) k) by (rewrite hrx5_B8RDg_len_snap by exact HL; lia).
    assert (E2: hrx5_B8RD_at NS k = hn_addr (Znth k NS)).
    { unfold hrx5_B8RD_at. rewrite (hrx5_B8RDg_skipn_S NS k) by lia. reflexivity. }
    rewrite E2.
    rewrite (hrx5_B8RDg_Znth_snap T NS PS k HL Hk').
    assert (Hpk: hn_p (Znth k NS) = peer_addr4 (Znth k PS)).
    { destruct Hinv as (_ & _ & _ & _ & Hnp & _). apply hrx5_B8RDg_hnp; assumption. }
    destruct (Znth k PS) as [[q sh] Q] eqn:HPk.
    assert (Hsh: sh = Ews).
    { destruct Hinv as (Hpok & _). rewrite Forall_forall in Hpok.
      assert (Hin: In (q, sh, Q) PS) by (rewrite <- HPk; apply Znth_In; lia).
      apply Hpok in Hin. destruct Hin as [Hs _]. exact Hs. }
    subst sh. cbn [hn_snapshot4 peer_addr4] in Hpk |- *. rewrite Hpk.
    rewrite hrx5_B8RDg_rep_cons_nv. Intros nx.
    assert_PROP (isptr (hn_addr (Znth k NS))) as Hptr.
    { entailer!; match goal with Hf: field_compatible t_hnode4 [] _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end. }
    forward_if.
    2: { match goal with Hn: _ = nullval |- _ => change (hn_addr (Znth k NS) = nullval) in Hn; rewrite Hn in Hptr;
           contradiction end. }
    forward. unfold hrx5_B8RDg_A. Exists nx q Q.
    unfold hrx5_B8RD_Q, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app]. entailer!.
Qed.

Lemma hrx5_B8RDg_ifc_ok (Rp: ret_assert) k nx q Q : HYP ->
  semax DL (QQ k nx q Q (NHK k) []) hrx5_B8RD_ifc (overridePost (Q0 k nx q Q) (hrx5_B8RDg_RL Rp)).
Proof.
  intros HY. unfold hrx5_B8RDg_RL. destruct Rp as [Rn Rb Rc Rr].
  unfold hrx5_B8RD_Q, hrx5_Delta, hrx5_B8RD_ifc. simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app]. Intros.
  destruct HY as (Hinv & Hj & Hja & Htg & Hnd & HTf). subst tg.
  match goal with Hp: Znth k PS = _ |- _ => rename Hp into HPk end.
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & _ & Hnp & _); apply hrx5_B8RDg_len, Hnp).
  assert (HA: map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS) by (apply hrx5_B8RDg_addr_snap, HL).
  assert (Hpk: hn_p (Znth k NS) = q).
  { destruct Hinv as (_ & _ & _ & _ & Hnp & _). rewrite (hrx5_B8RDg_hnp NS PS k Hnp), HPk by lia. reflexivity. }
  forward_if.
  { apply denote_tc_test_eq_split.
    - auto 50 with valid_pointer.
    - destruct (Z.lt_trichotomy j k) as [Hik | [Hik | Hik]].
      + assert (Hin: In (hn_addr (Znth j NS)) (map hn_addr (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS)))).
        { rewrite <- firstn_map, HA. rewrite <- (Znth_map j hn_addr) by lia.
          apply hrx5_B8RDg_in_firstn; [lia | rewrite Zlength_map; lia]. }
        sep_apply (hrx5_B8RDg_seg_vp (hn_addr (Znth j NS)) (hrx5_head (hnodes_snapped4 T NS PS))
                     (hn_addr (Znth k NS)) _ Hin).
        auto 50 with valid_pointer.
      + subst j. auto 50 with valid_pointer.
      + assert (Hin: In (hn_addr (Znth j NS))
                      (map hn_addr (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS)))).
        { rewrite <- skipn_map, HA. rewrite <- (Znth_map j hn_addr) by lia.
          apply hrx5_B8RDg_in_skipn; [lia | rewrite Zlength_map; lia]. }
        sep_apply (hrx5_B8RDg_rep_vp (hn_addr (Znth j NS)) nx _ Hin). auto 50 with valid_pointer. }
  { assert (k = j).
    { apply (NoDup_Znth_inj (map hn_addr NS) k j); auto; rewrite ?Zlength_map; try lia.
      rewrite !Znth_map by lia. assumption. }
    subst j. forward.
    unfold hrx5_B8RD_cont, hrx5_B8RD_Q1, hrx5_B8RD_Q, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars;
      cbn [app]. Exists k nx q Q.
    unfold hrx5_B8RD_nhk.
    rewrite (hrx5_B8RDg_firstn_S PS k) by lia. rewrite hrx5_B8RDg_nh_snoc, HPk. cbn [peer_addr4].
    assert (Hv: veqb q a = true)
      by (rewrite <- Hja, Hpk; unfold veqb; destruct (eq_dec q q); congruence).
    rewrite Hv. cbn [negb andb]. rewrite Z.add_0_r.
    entailer!. }
  forward. unfold hrx5_B8RD_Q0, hrx5_B8RD_Q, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hrx5_B8RDg_incr_ok (Rp: ret_assert) k nx q Q : HYP ->
  semax DL (Q1 k nx q Q) hrx5_B8RD_incr (loop2_ret_assert hrx5_B8RDg_I (overridePost X Rp)).
Proof.
  intros HY. destruct Rp as [Rn Rb Rc Rr].
  unfold hrx5_B8RD_Q1, hrx5_B8RD_Q, hrx5_Delta, hrx5_B8RD_incr. simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app]. Intros.
  destruct HY as (Hinv & Hj & Hja & Htg & Hnd & HTf).
  match goal with Hp: Znth k PS = _ |- _ => rename Hp into HPk end.
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & _ & Hnp & _); apply hrx5_B8RDg_len, Hnp).
  assert (HA: map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS) by (apply hrx5_B8RDg_addr_snap, HL).
  assert (Hk': 0 <= k < Zlength NS) by lia.
  assert (HLs: Zlength (hnodes_snapped4 T NS PS) = Zlength NS) by apply (hrx5_B8RDg_len_snap T NS PS HL).
  assert (Hpk: hn_p (Znth k NS) = q).
  { destruct Hinv as (_ & _ & _ & _ & Hnp & _). rewrite (hrx5_B8RDg_hnp NS PS k Hnp Hk'), HPk. reflexivity. }
  assert_PROP (nx = hrx5_head (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS))) as Hnx.
  { sep_apply (hrx5_B8RDg_rep_head nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS))). entailer!. }
  assert_PROP (is_pointer_or_null nx) as Hnxp.
  { sep_apply (hrx5_B8RDg_pn nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS))). entailer!. }
  rewrite (hrx5_B8RDg_next_split q (hs_snap_cur T q Q) Q nx (hn_addr (Znth k NS))). Intros.
  forward.
  sep_apply (hrx5_B8RDg_next_join q (hs_snap_cur T q Q) Q nx (hn_addr (Znth k NS))).
  unfold hrx5_B8RDg_I. Exists (k + 1).
  unfold hrx5_B8RD_inv, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars; cbn [app].
  assert (E: hrx5_B8RD_at NS (k + 1) = nx).
  { unfold hrx5_B8RD_at. rewrite Hnx. symmetry. apply hrx5_B8RDg_head_skip, HA. }
  rewrite E.
  rewrite (hrx5_B8RDg_firstn_S (hnodes_snapped4 T NS PS) k) by lia.
  rewrite (hrx5_B8RDg_Znth_snap T NS PS k HL Hk').
  sep_apply (hrx5_B8RDg_seg_snoc_snap (hrx5_head (hnodes_snapped4 T NS PS)) T (Znth k NS) (Znth k PS) nx
               (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS)) q Q HPk Hpk).
  entailer!.
Qed.

Lemma hrx5_B8RDg_loop_ok (Rp: ret_assert) : HYP ->
  semax DL P0 hrx5_B8RD_s9 (overridePost X Rp).
Proof.
  intros HY.
  rewrite hrx5_B8RD_s9_eq.
  eapply semax_seq.
  { apply (hrx5_B8RDg_init_ok (overridePost X Rp) HY). }
  apply semax_loop with (Q' := CONT).
  - unfold hrx5_B8RDg_I at 1. apply extract_exists_pre; intro k.
    rewrite hrx5_B8RD_body_eq.
    eapply semax_seq; [apply (hrx5_B8RDg_ifb_ok Rp k HY) |].
    unfold hrx5_B8RDg_A. apply extract_exists_pre; intro nx. apply extract_exists_pre; intro q.
    apply extract_exists_pre; intro Q.
    eapply semax_seq; [apply (hrx5_B8RDg_ifc_ok Rp k nx q Q HY) |].
    eapply semax_seq.
    { apply (hrx5_B8RD_chk_ok x25519 aead_dec xaead_enc xaead_dec gv L R NS PS KE T head nk j a tg Pf Tf D FRM
               vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath
               (hrx5_B8RDg_RL Rp) k nx q Q HY). }
    eapply semax_post; [| | | | apply (hrx5_B8RD_hif_ok x25519 aead_dec xaead_enc xaead_dec gv L R NS PS KE T head nk
               j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind
               vai var vhead0 vpath (hrx5_B8RDg_RL Rp) k nx q Q HY)];
      unfold hrx5_B8RDg_RL; destruct Rp as [Rn Rb Rc Rr]; simpl; intros; try (apply andp_left2, derives_refl).
    apply andp_left2. unfold hrx5_B8RD_cont. simpl. apply (exp_right k), (exp_right nx), (exp_right q), (exp_right Q), derives_refl.
  - unfold hrx5_B8RD_cont. apply extract_exists_pre; intro k. apply extract_exists_pre; intro nx.
    apply extract_exists_pre; intro q. apply extract_exists_pre; intro Q.
    apply (hrx5_B8RDg_incr_ok Rp k nx q Q HY).
Qed.

End Loop.
