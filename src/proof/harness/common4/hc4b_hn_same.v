(* the body of hnodes_same_except, adapted from v1's
   hc_hnodes_bodies3.v (hnb3_same_A): the other peers of the list and the index table are LENT to hs_same /
   pr_same (vobjs), so that every pointer they compare is valid. *)
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
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HI := WgNoise.harness.x_consume_initiation_any.code.

(* ---- a node's fields, the snapshots hidden in constants (no reptype conversion in the body proof) ---- *)
Section Cell.
#[local] Existing Instance CKS.
Definition hc4b_hs_snapf (N: hnode4) (l: val) : mpred :=
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) l.
Definition hc4b_hs_restf (N: hnode4) (l: val) : mpred :=
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l.

Lemma hc4b_hs_cell N nx l :
  hn4_cell N nx l =
  @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) l * hc4b_hs_snapf N l *
  @field_at CS4 Ews t_hnode4 (DOT HC._refs) (hn_refs N) l * spacer Ews 300 304 l * hc4b_hs_restf N l *
  @field_at CS4 Ews t_hnode4 (DOT HC._next) nx l.
Proof.
  unfold hn4_cell, hc4b_hs_snapf, hc4b_hs_restf. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS CS4 _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4 _ Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_refs N) l) by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS CS4 _ Ews t_hnode4 (DOT HC._next) nx nx l) by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.
Lemma hc4b_hs_cell_fold N nx l :
  @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) l * hc4b_hs_snapf N l *
  @field_at CS4 Ews t_hnode4 (DOT HC._refs) (hn_refs N) l * spacer Ews 300 304 l * hc4b_hs_restf N l *
  @field_at CS4 Ews t_hnode4 (DOT HC._next) nx l |-- hn4_cell N nx l.
Proof. rewrite hc4b_hs_cell. apply derives_refl. Qed.
Lemma hc4b_hs_cell_fc N nx l : hn4_cell N nx l = !! @field_compatible CS4 t_hnode4 [] l && hn4_cell N nx l.
Proof.
  apply pred_ext; [|apply andp_left2, derives_refl].
  apply andp_right; [|apply derives_refl].
  unfold hn4_cell. eapply derives_trans; [apply (@data_at_local_facts CKS)|]. apply prop_derives. intros [Hc _].
  apply (@field_compatible_change_composite CKS CS4 hc4b_hn_CKS_4); [reflexivity | auto].
Qed.
End Cell.

Lemma hc4b_hs_fa f l :
  In f [HC._snap; HC._rest] ->
  @field_address CKS t_hnode4 (DOT f) l = @field_address CS4 t_hnode4 (DOT f) l.
Proof.
  intros Hf. unfold field_address.
  assert (Hc: @field_compatible CKS t_hnode4 (DOT f) l <-> @field_compatible CS4 t_hnode4 (DOT f) l)
    by (apply (@field_compatible_change_composite CKS CS4 hc4b_hn_CKS_4); reflexivity).
  destruct (@field_compatible_dec CKS t_hnode4 (DOT f) l) as [H1|H1];
  destruct (@field_compatible_dec CS4 t_hnode4 (DOT f) l) as [H2|H2]; try tauto.
Qed.

Definition hc4b_hs_head (N: hnode4) (sn: hsnap) : Prop := @eq (@reptype CKS t_hsnap) (hn_snap N) (hsnap_val sn).

Lemma hc4b_hs_snap N sn l :
  hc4b_hs_head N sn ->
  hc4b_hs_snapf N l = @data_at HCS Ews t_hsnap (hsnap_val sn) (@field_address CS4 t_hnode4 (DOT HC._snap) l).
Proof.
  unfold hc4b_hs_snapf, hc4b_hs_head. intros E. rewrite E.
  rewrite (@field_at_data_at CKS), hc4b_hs_fa by (simpl; auto).
  rewrite (@data_at_cs_eq CKS CS4 hc4b_hn_CKS_4 Ews t_hsnap (hsnap_val sn) (hsnap_val sn)) by (apply JMeq_refl || reflexivity).
  apply (@data_at_cs_eq CS4 HCS hc4b_hn_4_HCS); [apply JMeq_refl | reflexivity].
Qed.

Lemma hc4b_hs_rest N P0 l :
  hn_rest N = prsnap_val P0 ->
  hc4b_hs_restf N l = @data_at CKS Ews t_prsnap (prsnap_val P0) (@field_address CS4 t_hnode4 (DOT HC._rest) l).
Proof.
  unfold hc4b_hs_restf. intros E. rewrite E.
  rewrite (@field_at_data_at CKS), hc4b_hs_fa by (simpl; auto). reflexivity.
Qed.

(* the reference count of a peer, at CS4 *)
Section Kref.
#[local] Existing Instance CS4.
Lemma hc4b_hs_kref sh p (v: val) :
  @field_at CS4 sh t_peer (DOT HC._refcount) v p = @field_at CS4 sh t_peer (DOT HC._refcount DOT HC._refcount) v p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hc4b_hs_refs sh p P :
  peer_rep sh p P |--
  @field_at CS4 sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p *
  (@field_at CS4 sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p -* peer_rep sh p P).
Proof.
  unfold peer_rep. Intros.
  match goal with |- ?a1 * ?a2 * ?a3 * ?a4 * ?a5 * ?a6 * ?F * ?a8 * ?a9 * ?a10 * ?a11 |-- _ =>
    apply derives_trans with (F * (a1 * a2 * a3 * a4 * a5 * a6 * a8 * a9 * a10 * a11)); [cancel|] end.
  assert (EQ: @field_at Noise.CS sh t_peer (DOT I._refcount) (Vint (p_refs P)) p =
              @field_at CS4 sh t_peer (DOT HC._refcount) (Vint (p_refs P)) p)
    by (apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  rewrite EQ, hc4b_hs_kref. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite <- hc4b_hs_kref, <- EQ. entailer!.
Qed.
End Kref.

(* ---- peers ---- *)
Lemma hc4b_hs_peers_split PS PS1 x PS2 :
  PS = PS1 ++ x :: PS2 -> peers_rep PS = peers_rep PS1 * peer_item_rep x * peers_rep PS2.
Proof. intros ->. unfold peers_rep. rewrite iter_sepcon_app. simpl. symmetry; apply sepcon_assoc. Qed.

Lemma hc4b_hs_peers_join PS PS1 p sh P PS2 :
  PS = PS1 ++ (p, sh, P) :: PS2 -> peers_rep PS1 * peer_rep sh p P * peers_rep PS2 |-- peers_rep PS.
Proof. intros HP. rewrite (hc4b_hs_peers_split PS PS1 (p, sh, P) PS2 HP). apply derives_refl. Qed.

Lemma hc4b_hs_peer_valid sh p P : readable_share sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep. Intros.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | simpl; lia | reflexivity].
Qed.

Lemma hc4b_hs_peers_valid PS q :
  peers_wf PS -> In q (map peer_addr4 PS) -> peers_rep PS |-- valid_pointer q.
Proof.
  unfold peers_rep, peers_wf. induction PS as [|[[a sh] P] PS IH]; simpl; intros Hwf Hq; [contradiction|].
  inversion Hwf; subst. destruct Hq as [<-|Hq].
  - apply sepcon_valid_pointer1. apply hc4b_hs_peer_valid; auto.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hc4b_hs_except_valid PS PS1 p sh P PS2 except :
  peers_wf PS -> PS = PS1 ++ (p, sh, P) :: PS2 -> except = nullval \/ In except (map peer_addr4 PS) ->
  peers_rep PS1 * peer_rep sh p P * peers_rep PS2 |-- valid_pointer except.
Proof.
  intros Hwf HPS [->|Hin]; [apply valid_pointer_null|].
  change (peer_rep sh p P) with (peer_item_rep (p, sh, P)).
  rewrite <- (hc4b_hs_peers_split PS) by auto. apply hc4b_hs_peers_valid; auto.
Qed.

Lemma hc4b_hs_wf_sh PS PS1 p sh P PS2 : peers_wf PS -> PS = PS1 ++ (p, sh, P) :: PS2 -> writable_share sh.
Proof.
  intros Hwf ->. unfold peers_wf in Hwf. rewrite Forall_app in Hwf. destruct Hwf as [_ Hwf].
  inversion Hwf; auto.
Qed.

Lemma hc4b_hs_wf_others PS PS1 x PS2 :
  peers_wf PS -> PS = PS1 ++ x :: PS2 ->
  Forall (fun x => match x with (_, sh, _) => readable_share sh end) (PS1 ++ PS2).
Proof.
  intros Hwf ->. unfold peers_wf in Hwf. rewrite Forall_app in Hwf. destruct Hwf as [H1 H2].
  inversion H2; subst. rewrite Forall_app. split.
  - eapply Forall_impl; [|exact H1]. intros [[a s] Q] Hs. apply writable_readable_share; auto.
  - eapply Forall_impl; [|eassumption]. intros [[a s] Q] Hs. apply writable_readable_share; auto.
Qed.

(* ---- the model ---- *)
Definition hc4b_hs_one (T: tstate) (except: val) (sn: hsnap) (r: int) (P0: peer) (x: val * share * peer) : bool :=
  match x with (p, _, P) =>
    if eq_dec p except then true
    else (snap_eqb sn (hs_snap_cur T p P) && Int.eq r (p_refs P) && pr_eqb P0 P)%bool
  end.

Lemma hc4b_hs_same_cons T e sn sns r rs P0 prs x PS :
  hnodes_same4 T e (sn :: sns) (r :: rs) (P0 :: prs) (x :: PS) =
  (hc4b_hs_one T e sn r P0 x && hnodes_same4 T e sns rs prs PS)%bool.
Proof. destruct x as [[p sh] P]. reflexivity. Qed.

Lemma hc4b_hs_same_nil T e sns rs prs : hnodes_same4 T e sns rs prs [] = true.
Proof. destruct sns, rs, prs; reflexivity. Qed.

Lemma hc4b_hs_Forall_app {A} (Q: A -> Prop) l1 l2 : Forall Q (l1 ++ l2) -> Forall Q l1 /\ Forall Q l2.
Proof. rewrite Forall_app. auto. Qed.

(* lending the other peers (and the index table) *)
Lemma hc4b_hs_lend1 (CSw: compspecs) PS1 PS2 VO :
  peers_rep PS1 * peers_rep PS2 * vobjs CSw VO = vobjs CSw (VPeers (PS1 ++ PS2) :: VO).
Proof. unfold vobjs at 2. simpl iter_sepcon. unfold peers_rep. rewrite iter_sepcon_app. reflexivity. Qed.

Lemma hc4b_hs_lend2 (CSw: compspecs) PS1 PS2 sht tab T VO :
  peers_rep PS1 * peers_rep PS2 * itable sht tab T * vobjs CSw VO =
  vobjs CSw (VPeers (PS1 ++ PS2) :: VItab sht tab T :: VO).
Proof.
  unfold vobjs at 2. simpl iter_sepcon. unfold peers_rep. rewrite iter_sepcon_app.
  fold (vobjs CSw VO). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc4b_hs_lend1d (CSw: compspecs) PS1 PS2 VO :
  peers_rep PS1 * peers_rep PS2 * vobjs CSw VO |-- vobjs CSw (VPeers (PS1 ++ PS2) :: VO).
Proof. rewrite hc4b_hs_lend1. apply derives_refl. Qed.
Lemma hc4b_hs_lend1r (CSw: compspecs) PS1 PS2 VO :
  vobjs CSw (VPeers (PS1 ++ PS2) :: VO) |-- peers_rep PS1 * peers_rep PS2 * vobjs CSw VO.
Proof. rewrite hc4b_hs_lend1. apply derives_refl. Qed.
Lemma hc4b_hs_lend2d (CSw: compspecs) PS1 PS2 sht tab T VO :
  peers_rep PS1 * peers_rep PS2 * itable sht tab T * vobjs CSw VO |--
  vobjs CSw (VPeers (PS1 ++ PS2) :: VItab sht tab T :: VO).
Proof. rewrite hc4b_hs_lend2. apply derives_refl. Qed.
Lemma hc4b_hs_lend2r (CSw: compspecs) PS1 PS2 sht tab T VO :
  vobjs CSw (VPeers (PS1 ++ PS2) :: VItab sht tab T :: VO) |--
  peers_rep PS1 * peers_rep PS2 * itable sht tab T * vobjs CSw VO.
Proof. rewrite hc4b_hs_lend2. apply derives_refl. Qed.

Lemma hc4b_hs_rebuild (CSw: compspecs) l NS1 N NS2 nx :
  hnodes_seg4 CSw l (hn_addr N) NS1 * @malloc_token CSw Ews t_hnode4 (hn_addr N) * hn4_cell N nx (hn_addr N) *
  @malloc_token CSw Ews t_peer (hn_p N) * hnodes_rep4 CSw nx NS2
  |-- hnodes_rep4 CSw l (NS1 ++ N :: NS2).
Proof.
  sep_apply (hnodes_seg4_snoc CSw l (hn_addr N) nx N NS1 eq_refl).
  sep_apply (hnodes_seg4_rep CSw l nx (NS1 ++ [N]) NS2). rewrite <- app_assoc. apply derives_refl.
Qed.

Lemma hc4b_hs_one_ex T e sn r P0 p sh P : p = e -> hc4b_hs_one T e sn r P0 (p, sh, P) = true.
Proof. intros ->. unfold hc4b_hs_one. rewrite if_true by auto. reflexivity. Qed.

Lemma hc4b_hs_one_ne T e sn r P0 p sh P : p <> e ->
  hc4b_hs_one T e sn r P0 (p, sh, P) = (snap_eqb sn (hs_snap_cur T p P) && Int.eq r (p_refs P) && pr_eqb P0 P)%bool.
Proof. intros Hn. unfold hc4b_hs_one. rewrite if_false by auto. reflexivity. Qed.

Lemma hc4b_hs_own_hs PS PS1 p sh P PS2 T VO x :
  PS = PS1 ++ (p, sh, P) :: PS2 ->
  vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs VO) x ->
  vp_ok (hs_own p T (VPeers (PS1 ++ PS2) :: VO)) x.
Proof.
  intros -> [Hx|Hx]; [left; auto | right]. unfold hs_own, vobjs_addrs. simpl. unfold vobjs_addrs in Hx.
  rewrite !map_app, !in_app_iff in *. simpl in Hx. tauto.
Qed.

Lemma hc4b_hs_own_pr PS PS1 p sh P PS2 sht tab T VO x :
  PS = PS1 ++ (p, sh, P) :: PS2 ->
  vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs VO) x ->
  vp_ok (p :: vobjs_addrs (VPeers (PS1 ++ PS2) :: VItab sht tab T :: VO)) x.
Proof.
  intros -> [Hx|Hx]; [left; auto | right]. unfold vobjs_addrs. simpl. unfold vobjs_addrs in Hx.
  rewrite !map_app, !in_app_iff in *. simpl in *. rewrite ?in_app_iff in *. tauto.
Qed.

(* ---- the facts of the unprocessed suffix ---- *)
Definition hc4b_hs_invg {A: Type} (fs: hnode4 -> A) (gs: hsnap -> A) (own: list val) (T: tstate)
  (NS2: list hnode4) (PS2: list (val * share * peer)) (sns2: list hsnap) (rs2: list int) (prs2: list peer) : Prop :=
  hnodes_peers4 NS2 PS2 /\ Zlength sns2 = Zlength NS2 /\ Zlength rs2 = Zlength NS2 /\ Zlength prs2 = Zlength NS2 /\
  map fs NS2 = map gs sns2 /\ map hn_refs NS2 = map Vint rs2 /\ map hn_rest NS2 = map prsnap_val prs2 /\
  hn4_cmp_ok own T sns2 prs2 PS2.

Lemma hc4b_hs_invg_nil {A: Type} (fs: hnode4 -> A) gs own T PS2 sns2 rs2 prs2 :
  hc4b_hs_invg fs gs own T [] PS2 sns2 rs2 prs2 -> PS2 = [].
Proof. intros (HP & _). unfold hnodes_peers4 in HP. destruct PS2; [reflexivity | discriminate]. Qed.

Lemma hc4b_hs_cons_inj {A} (a b: A) l1 l2 : a :: l1 = b :: l2 -> a = b /\ l1 = l2.
Proof. intros H; inversion H; auto. Qed.

Lemma hc4b_hs_invg_step {A: Type} (fs: hnode4 -> A) gs own T N NS2 PS2 sns2 rs2 prs2 :
  hc4b_hs_invg fs gs own T (N :: NS2) PS2 sns2 rs2 prs2 ->
  exists p sh P PS2' sn sns2' r rs2' P0 prs2',
    PS2 = (p, sh, P) :: PS2' /\ sns2 = sn :: sns2' /\ rs2 = r :: rs2' /\ prs2 = P0 :: prs2' /\
    hn_p N = p /\ fs N = gs sn /\ hn_refs N = Vint r /\ hn_rest N = prsnap_val P0 /\
    In (hs_addr p) (saddrs (t_D T)) /\ Forall (vp_ok own) (hs_ptrs sn (hs_snap_cur T p P) ++ pr_ptrs P0 P) /\
    hc4b_hs_invg fs gs own T NS2 PS2' sns2' rs2' prs2'.
Proof.
  intros (HP & HL1 & HL2 & HL3 & HS & HR & HQ & HC). unfold hnodes_peers4 in HP.
  pose proof (Zlength_nonneg NS2).
  destruct PS2 as [|[[p sh] P] PS2']; [discriminate|].
  destruct sns2 as [|sn sns2']; [rewrite Zlength_nil, Zlength_cons in HL1; lia|].
  destruct rs2 as [|r rs2']; [rewrite Zlength_nil, Zlength_cons in HL2; lia|].
  destruct prs2 as [|P0 prs2']; [rewrite Zlength_nil, Zlength_cons in HL3; lia|].
  simpl map in HP, HS, HR, HQ.
  apply hc4b_hs_cons_inj in HP, HS, HR, HQ.
  destruct HP as [HP1 HP2], HS as [HS1 HS2], HR as [HR1 HR2], HQ as [HQ1 HQ2].
  simpl in HC. destruct HC as [[HC1 HC2] HC3].
  rewrite !Zlength_cons in HL1, HL2, HL3.
  exists p, sh, P, PS2', sn, sns2', r, rs2', P0, prs2'.
  do 11 (split; [first [reflexivity | assumption] |]).
  unfold hc4b_hs_invg, hnodes_peers4. repeat split; auto; lia.
Qed.

Definition hc4b_hs_inv := @hc4b_hs_invg (@reptype CKS t_hsnap) hn_snap hsnap_val.

Lemma hc4b_hs_inv_intro own T NS PS sns rs prs :
  hnodes_peers4 NS PS -> Zlength sns = Zlength NS -> Zlength rs = Zlength NS -> Zlength prs = Zlength NS ->
  map hn_snap NS = map hsnap_val sns -> map hn_refs NS = map Vint rs -> map hn_rest NS = map prsnap_val prs ->
  hn4_cmp_ok own T sns prs PS ->
  hc4b_hs_inv own T NS PS sns rs prs.
Proof. intros H1 H2 H3 H4 H5 H6 H7 H8. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))). Qed.

Lemma hc4b_hs_inv_nil own T PS2 sns2 rs2 prs2 : hc4b_hs_inv own T [] PS2 sns2 rs2 prs2 -> PS2 = [].
Proof. apply hc4b_hs_invg_nil. Qed.

Lemma hc4b_hs_inv_step own T N NS2 PS2 sns2 rs2 prs2 :
  hc4b_hs_inv own T (N :: NS2) PS2 sns2 rs2 prs2 ->
  exists p sh P PS2' sn sns2' r rs2' P0 prs2',
    PS2 = (p, sh, P) :: PS2' /\ sns2 = sn :: sns2' /\ rs2 = r :: rs2' /\ prs2 = P0 :: prs2' /\
    hn_p N = p /\ hc4b_hs_head N sn /\ hn_refs N = Vint r /\ hn_rest N = prsnap_val P0 /\
    In (hs_addr p) (saddrs (t_D T)) /\ Forall (vp_ok own) (hs_ptrs sn (hs_snap_cur T p P) ++ pr_ptrs P0 P) /\
    hc4b_hs_inv own T NS2 PS2' sns2' rs2' prs2'.
Proof. exact (hc4b_hs_invg_step hn_snap hsnap_val own T N NS2 PS2 sns2 rs2 prs2). Qed.

(* the world compspecs as a hypothesis that typeclass resolution does not take for the proof's compspecs CS4 *)
Definition hc4b_hs_csw := compspecs.
#[local] Typeclasses Opaque hc4b_hs_csw.

Section Same.
#[local] Existing Instance CS4.

Lemma hc4b_hn_same_body (CSw: hc4b_hs_csw) :
  @semax_body [] (hc4_G_hnodes_same_except CSw) CS4 HI.f_hnodes_same_except (hnodes_same_except4_spec CSw).
Proof.
  start_function.
  set (own := map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs VO).
  assert (Hinv0: hc4b_hs_inv own T NS PS sns rs prs) by (apply hc4b_hs_inv_intro; auto).
  clear H3 H4 H5 H6 H7 H8. rename H9 into Hex.
  forward_loop (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX PS2: list (val * share * peer), EX sns2: list hsnap, EX rs2: list int, EX prs2: list peer,
                EX l': val,
    PROP (NS = NS1 ++ NS2; PS = PS1 ++ PS2; hc4b_hs_inv own T NS2 PS2 sns2 rs2 prs2;
          hnodes_same4 T except sns rs prs PS = hnodes_same4 T except sns2 rs2 prs2 PS2)
    LOCAL (temp HI._l l'; temp HI._except except)
    SEP (hnodes_seg4 CSw l l' NS1; hnodes_rep4 CSw l' NS2; peers_rep PS; itable sht tab T; vobjs CSw VO))
  continue: (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX PS2: list (val * share * peer), EX sns2: list hsnap, EX rs2: list int, EX prs2: list peer,
                EX l': val, EX nx: val,
    PROP (NS = NS1 ++ N :: NS2; PS = PS1 ++ PS2; l' = hn_addr N; hc4b_hs_inv own T NS2 PS2 sns2 rs2 prs2;
          hnodes_same4 T except sns rs prs PS = hnodes_same4 T except sns2 rs2 prs2 PS2)
    LOCAL (temp HI._l l'; temp HI._except except)
    SEP (hnodes_seg4 CSw l l' NS1; @malloc_token CSw Ews t_hnode4 l'; hn4_cell N nx l';
         @malloc_token CSw Ews t_peer (hn_p N);
         hnodes_rep4 CSw nx NS2; peers_rep PS; itable sht tab T; vobjs CSw VO))
  break: (PROP (hnodes_same4 T except sns rs prs PS = true) LOCAL ()
    SEP (hnodes_rep4 CSw l NS; peers_rep PS; itable sht tab T; vobjs CSw VO)).
  - Exists (@nil hnode4) NS (@nil (val * share * peer)) PS sns rs prs l. entailer!. apply hnodes_seg4_nil.
  - Intros NS1 NS2 PS1 PS2 sns2 rs2 prs2 l'.
    match goal with HA: NS = NS1 ++ NS2, HB: PS = PS1 ++ PS2, HC: hc4b_hs_inv _ _ _ _ _ _ _,
                    HD: hnodes_same4 _ _ sns rs prs PS = _ |- _ =>
      rename HA into HNS, HB into HPS, HC into Hinv, HD into Hsame end.
    forward_if.
    2: { assert_PROP (NS2 = []) as HN2.
         { entailer!. match goal with Hn: nullval = nullval <-> _ |- _ => apply (proj1 Hn eq_refl) end. }
         subst NS2. pose proof (hc4b_hs_inv_nil _ _ _ _ _ _ Hinv). subst PS2. forward.
         rewrite <- !app_nil_end in *. subst. entailer!.
         { rewrite Hsame. apply hc4b_hs_same_nil. }
         sep_apply (hnodes_seg4_rep CSw l nullval NS1 []). rewrite <- app_nil_end. cancel. }
    destruct NS2 as [|N NS2].
    { rewrite hnodes_rep4_nil. Intros. subst l'. contradiction. }
    destruct (hc4b_hs_inv_step own T N NS2 PS2 sns2 rs2 prs2 Hinv)
      as (p & sh & P & PS2' & sn & sns2' & r & rs2' & P0 & prs2' & -> & -> & -> & -> & Hp & Hsn & Hr & Hq &
          Hin & Hcmp & Hinv').
    clear Hinv.
    rewrite hnodes_rep4_cons. Intros nx. subst l'.
    rewrite hc4b_hs_cell_fc. Intros. rewrite hc4b_hs_cell. rewrite Hp.
    rewrite (hc4b_hs_peers_split PS PS1 (p, sh, P) PS2' HPS). simpl peer_item_rep.
    assert (Hsh: writable_share sh) by (eapply hc4b_hs_wf_sh; eauto).
    assert (Hok: Forall vobj_ok (VPeers (PS1 ++ PS2') :: VO)).
    { constructor; [simpl; eapply hc4b_hs_wf_others; eauto | auto]. }
    assert (Hok2: Forall vobj_ok (VPeers (PS1 ++ PS2') :: VItab sht tab T :: VO)).
    { constructor; [simpl; eapply hc4b_hs_wf_others; eauto | constructor; [simpl; auto | auto]]. }
    apply hc4b_hs_Forall_app in Hcmp. destruct Hcmp as [Hcmp1 Hcmp2].
    assert (Hv1: Forall (vp_ok (hs_own p T (VPeers (PS1 ++ PS2') :: VO))) (hs_ptrs sn (hs_snap_cur T p P))).
    { eapply Forall_impl; [|exact Hcmp1]. intros x; apply (hc4b_hs_own_hs PS PS1 p sh P PS2' T VO x HPS). }
    assert (Hv2: Forall (vp_ok (p :: vobjs_addrs (VPeers (PS1 ++ PS2') :: VItab sht tab T :: VO))) (pr_ptrs P0 P)).
    { eapply Forall_impl; [|exact Hcmp2]. intros x; apply (hc4b_hs_own_pr PS PS1 p sh P PS2' sht tab T VO x HPS). }
    clear Hcmp1 Hcmp2. subst p.
    assert_PROP (field_compatible t_peer [] (hn_p N)) as Hfp.
    { unfold peer_rep. Intros. apply prop_right.
      apply (@field_compatible_change_composite Noise.CS CS4 hc4b_hn_N_4); [reflexivity | auto]. }
    Intros. forward.
    freeze FR := (hnodes_seg4 _ _ _ _) (hnodes_rep4 _ _ _) (itable _ _ _) (vobjs _ _) (hc4b_hs_snapf _ _)
                 (hc4b_hs_restf _ _) (malloc_token _ _ _) (malloc_token _ _ _).
    forward_if (PROP ()
      LOCAL (temp HI._t'1 (Vint (if hc4b_hs_one T except sn r P0 (hn_p N, sh, P) then Int.zero else Int.one));
             temp HI._l (hn_addr N); temp HI._except except)
      SEP (hnodes_seg4 CSw l (hn_addr N) NS1; @malloc_token CSw Ews t_hnode4 (hn_addr N);
           @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N); hc4b_hs_snapf N (hn_addr N);
           @field_at CS4 Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_addr N); spacer Ews 300 304 (hn_addr N);
           hc4b_hs_restf N (hn_addr N); @field_at CS4 Ews t_hnode4 (DOT HC._next) nx (hn_addr N);
           @malloc_token CSw Ews t_peer (hn_p N); hnodes_rep4 CSw nx NS2;
           peers_rep PS1; peer_rep sh (hn_p N) P; peers_rep PS2'; itable sht tab T; vobjs CSw VO)).
    { apply denote_tc_test_eq_split.
      - eapply derives_trans; [|apply (sepcon_valid_pointer1 (peer_rep sh (hn_p N) P) TT); apply hc4b_hs_peer_valid;
          apply writable_readable_share; auto].
        cancel.
      - eapply derives_trans;
          [|apply (sepcon_valid_pointer1 (peers_rep PS1 * peer_rep sh (hn_p N) P * peers_rep PS2') TT);
            eapply hc4b_hs_except_valid; eauto].
        cancel. }
    { (* p != except *)
      thaw FR. forward. rewrite (hc4b_hs_snap N sn (hn_addr N) Hsn).
      sep_apply (hc4b_hs_lend1d CSw PS1 PS2' VO).
      change (peer_rep sh (hn_p N) P) with (hs_mem true sh (hn_p N) P).
      forward_call (Ews, field_address t_hnode4 (DOT HC._snap) (hn_addr N), sn, sh, hn_p N, P, true, sht, tab, T,
                    VPeers (PS1 ++ PS2') :: VO).
      change (hs_mem true sh (hn_p N) P) with (peer_rep sh (hn_p N) P).
      sep_apply (hc4b_hs_lend1r CSw PS1 PS2' VO). Intros.
      rewrite <- (hc4b_hs_snap N sn (hn_addr N) Hsn).
      freeze FR1 := (hnodes_seg4 _ _ _ _) (hnodes_rep4 _ _ _) (itable _ _ _) (vobjs _ _) (hc4b_hs_snapf _ _)
                   (hc4b_hs_restf _ _) (malloc_token _ _ _) (malloc_token _ _ _).
      forward_if (PROP ()
        LOCAL (temp HI._t'3 (Vint (if (snap_eqb sn (hs_snap_cur T (hn_p N) P) && Int.eq r (p_refs P))%bool
                                   then Int.zero else Int.one));
               temp HI._l (hn_addr N); temp HI._except except)
        SEP (hnodes_seg4 CSw l (hn_addr N) NS1; @malloc_token CSw Ews t_hnode4 (hn_addr N);
           @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N); hc4b_hs_snapf N (hn_addr N);
           @field_at CS4 Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_addr N); spacer Ews 300 304 (hn_addr N);
           hc4b_hs_restf N (hn_addr N); @field_at CS4 Ews t_hnode4 (DOT HC._next) nx (hn_addr N);
           @malloc_token CSw Ews t_peer (hn_p N); hnodes_rep4 CSw nx NS2;
           peers_rep PS1; peer_rep sh (hn_p N) P; peers_rep PS2'; itable sht tab T; vobjs CSw VO)).
      { thaw FR1. forward. entailer!.
        destruct (snap_eqb _ _); [discriminate | reflexivity]. }
      { thaw FR1. forward. sep_apply (hc4b_hs_refs sh (hn_p N) P). Intros. rewrite Hr. forward. forward. forward.
        sep_apply (modus_ponens_wand (@field_at CS4 sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) (hn_p N))).
        entailer!.
        - destruct (snap_eqb _ _); [| contradiction H6; reflexivity]. rewrite andb_true_l.
          rewrite (Int.eq_sym (p_refs P)). destruct (Int.eq _ _); reflexivity.
        - rewrite Hr. apply derives_refl. }
      freeze FR2 := (hnodes_seg4 _ _ _ _) (hnodes_rep4 _ _ _) (itable _ _ _) (vobjs _ _) (hc4b_hs_snapf _ _)
                   (hc4b_hs_restf _ _) (malloc_token _ _ _) (malloc_token _ _ _).
      forward_if.
      { thaw FR2. forward. entailer!. rewrite hc4b_hs_one_ne by auto.
        destruct (snap_eqb _ _ && Int.eq _ _)%bool; [contradiction | reflexivity]. }
      { thaw FR2. forward. rewrite (hc4b_hs_rest N P0 (hn_addr N) Hq).
        sep_apply (hc4b_hs_lend2d CSw PS1 PS2' sht tab T VO).
        forward_call (Ews, field_address t_hnode4 (DOT HC._rest) (hn_addr N), P0, sh, hn_p N, P,
                      VPeers (PS1 ++ PS2') :: VItab sht tab T :: VO).
        sep_apply (hc4b_hs_lend2r CSw PS1 PS2' sht tab T VO). Intros.
        rewrite <- (hc4b_hs_rest N P0 (hn_addr N) Hq).
        forward. forward. entailer!.
        rewrite hc4b_hs_one_ne by auto.
        destruct (snap_eqb _ _ && Int.eq _ _)%bool; [| discriminate].
        rewrite andb_true_l. destruct (pr_eqb P0 P); reflexivity. } }
    { thaw FR. forward. entailer!. rewrite hc4b_hs_one_ex by auto. reflexivity. }
    sep_apply (hc4b_hs_cell_fold N nx (hn_addr N)).
    sep_apply (hc4b_hs_peers_join PS PS1 (hn_p N) sh P PS2' HPS).
    destruct (hc4b_hs_one T except sn r P0 (hn_p N, sh, P)) eqn:Hhs.
    + forward_if; [contradiction|].
      forward. Exists NS1 N NS2 (PS1 ++ [(hn_p N, sh, P)]) PS2' sns2' rs2' prs2' (hn_addr N) nx.
      entailer!.
      split; [rewrite <- app_assoc; reflexivity|]. rewrite Hsame, hc4b_hs_same_cons, Hhs. reflexivity.
    + forward_if; [|discriminate].
      forward. rewrite Hsame, hc4b_hs_same_cons, Hhs. simpl andb.
      sep_apply (hc4b_hs_rebuild CSw l NS1 N NS2 nx). entailer!.
  - Intros NS1 N NS2 PS1 PS2 sns2 rs2 prs2 l' nx. subst l'. rewrite hc4b_hs_cell. Intros. forward.
    Exists (NS1 ++ [N]) NS2 PS1 PS2 sns2 rs2 prs2 nx. entailer!.
    { rewrite <- app_assoc. reflexivity. }
    sep_apply (hc4b_hs_cell_fold N nx (hn_addr N)).
    sep_apply (hnodes_seg4_snoc CSw l (hn_addr N) nx N NS1 eq_refl). cancel.
  - forward. match goal with Hb: hnodes_same4 _ _ _ _ _ _ = true |- _ => rewrite Hb end. entailer!.
Qed.
End Same.
