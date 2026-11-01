(* law cookie_reply, phase P12, segment X, the branch target != NULL: tn = target->n; CHECK(hnodes_same_except(peers, tn->p)); CHECK(hs_same(&tn->snap, &tn->p->handshake) && tn->p->refcount.refcount == tn->refs && pr_same_but_cookie(&tn->rest, tn->p)).
   St -> St over fixed values (hcy5_p12_defs.v). *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_spure.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers (prefix hcy5_p12_x_some_)                                       *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p12_x_some_cceK : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.
#[local] Instance hcy5_p12_x_some_cceKH : change_composite_env CKS HCS.
Proof. make_cs_preserve CKS HCS. Defined.
#[local] Instance hcy5_p12_x_some_cceN : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Section Helpers.
Local Open Scope logic.

Lemma hcy5_p12_x_some_wf (A F B: mpred) : A * (F * (F -* B)) |-- F * (F -* (A * B)).
Proof.
  rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

(* the field n of a cnode of the list *)
Lemma hcy5_p12_x_some_cn CL : forall l c nd o, In (c, nd, o) CL ->
  hcy5_cns l CL |-- @field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd c *
                    (@field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd c -* hcy5_cns l CL).
Proof.
  induction CL as [|[[c1 nd1] o1] CL IH]; intros l c nd o Hin; [destruct Hin|].
  cbn [hcy5_cns]. destruct Hin as [E|Hin].
  - inv E. Intros. subst l.
    match goal with |- ?t * ?F * ?cs * ?nx * ?r |-- _ =>
      apply derives_trans with (F * (t * cs * nx * r)); [cancel|] end.
    apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. entailer!.
  - Intros. subst l. sep_apply (IH (hcy5_chead CL) c nd o Hin).
    match goal with |- ?F * ?Wd * ?A |-- _ => apply derives_trans with (A * (F * Wd)); [cancel|] end.
    eapply derives_trans; [apply hcy5_p12_x_some_wf|].
    apply sepcon_derives; [apply derives_refl|]. apply wand_derives; [apply derives_refl|]. entailer!.
Qed.

(* a node's fields *)
Definition hcy5_p12_x_some_flds (N: hnode4) (nx: val) : mpred :=
  @field_at W_cookie_reply Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) (hn_addr N) *
  @field_at W_cookie_reply Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_addr N) *
  spacer Ews 300 304 (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._next) nx (hn_addr N).

Lemma hcy5_p12_x_some_cell N nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) =
  hcy5_p12_x_some_flds N nx.
Proof.
  unfold hcy5_p12_x_some_flds. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS W_cookie_reply _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS W_cookie_reply _ Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_refs N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hcy5_p12_x_some_node NS1 N NS2 : forall l,
  hnodes_rep4 W_cookie_reply l (NS1 ++ N :: NS2) |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hcy5_p12_x_some_flds N nx *
     (hcy5_p12_x_some_flds N nx -* hnodes_rep4 W_cookie_reply l (NS1 ++ N :: NS2))).
Proof.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx.
    assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as Hfc.
    { sep_apply (@data_at_local_facts CKS). entailer!. }
    rewrite hcy5_p12_x_some_cell. entailer!.
    rewrite <- wand_sepcon_adjoint. Exists nx. rewrite hcy5_p12_x_some_cell. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. entailer!.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hcy5_p12_x_some_node' NS NS1 N NS2 l : NS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W_cookie_reply l NS |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hcy5_p12_x_some_flds N nx * (hcy5_p12_x_some_flds N nx -* hnodes_rep4 W_cookie_reply l NS)).
Proof. intros ->. apply hcy5_p12_x_some_node. Qed.

Lemma hcy5_p12_x_some_hn_pn l NS : hnodes_rep4 W_cookie_reply l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    apply isptr_is_pointer_or_null; exact Hp.
Qed.

Lemma hcy5_p12_x_some_snap N sn l : @field_compatible CKS t_hnode4 [] l -> hn_snap N = hsnap_val sn ->
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) l = @data_at HCS Ews t_hsnap (hsnap_val sn) (offset_val 8 l).
Proof.
  intros Hfc E. rewrite E.
  rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
  apply (@data_at_cs_eq CKS HCS hcy5_p12_x_some_cceKH); [apply JMeq_refl | reflexivity].
Qed.

Lemma hcy5_p12_x_some_rest N P0 l : @field_compatible CKS t_hnode4 [] l -> hn_rest N = prsnap_val P0 ->
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l = @data_at CKS Ews t_prsnap (prsnap_val P0) (offset_val 304 l).
Proof.
  intros Hfc E. rewrite E.
  rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible. reflexivity.
Qed.

(* the reference count of a peer, at the world *)
Lemma hcy5_p12_x_some_kref sh p (v: val) :
  @field_at W_cookie_reply sh t_peer (DOT HC._refcount) v p =
  @field_at W_cookie_reply sh t_peer (DOT HC._refcount DOT HC._refcount) v p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hcy5_p12_x_some_refs sh p P :
  peer_rep sh p P |--
  @field_at W_cookie_reply sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p *
  (@field_at W_cookie_reply sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p -* peer_rep sh p P).
Proof.
  unfold peer_rep. Intros.
  match goal with |- ?a1 * ?a2 * ?a3 * ?a4 * ?a5 * ?a6 * ?F * ?a8 * ?a9 * ?a10 * ?a11 |-- _ =>
    apply derives_trans with (F * (a1 * a2 * a3 * a4 * a5 * a6 * a8 * a9 * a10 * a11)); [cancel|] end.
  assert (EQ: @field_at Noise.CS sh t_peer (DOT I._refcount) (Vint (p_refs P)) p =
              @field_at W_cookie_reply sh t_peer (DOT HC._refcount) (Vint (p_refs P)) p)
    by (apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  rewrite EQ, hcy5_p12_x_some_kref. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite <- hcy5_p12_x_some_kref, <- EQ. entailer!.
Qed.

Lemma hcy5_p12_x_some_papp PS1 x PS2 : peers_rep (PS1 ++ x :: PS2) = peer_item_rep x * peers_rep (PS1 ++ PS2).
Proof. unfold peers_rep. rewrite !iter_sepcon_app. simpl. apply pred_ext; cancel. Qed.

(* the lent objects *)
Lemma hcy5_p12_x_some_vo1 x25519 R L T KE :
  device_rep Tsh (l_wa L) (hcy5_DA x25519 R L) * kents_rep W_cookie_reply (hcy5_khead KE) (map (kent_snapped T) KE) =
  vobjs W_cookie_reply (hcy5_p12_x_VO x25519 R L T KE).
Proof. unfold vobjs, hcy5_p12_x_VO. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcy5_p12_x_some_vo2 x25519 R L T KE PS :
  device_rep Tsh (l_wa L) (hcy5_DA x25519 R L) * kents_rep W_cookie_reply (hcy5_khead KE) (map (kent_snapped T) KE) *
  peers_rep PS = vobjs W_cookie_reply (hcy5_p12_x_VO x25519 R L T KE ++ [VPeers PS]).
Proof. unfold vobjs, hcy5_p12_x_VO. simpl. rewrite sepcon_emp, !sepcon_assoc. reflexivity. Qed.

(* common4 v4.1: the slots (kent addresses) are lent through A's index table *)
Lemma hcy5_p12_x_some_vo3 x25519 R L T KE PS :
  device_rep Tsh (l_wa L) (hcy5_DA x25519 R L) * kents_rep W_cookie_reply (hcy5_khead KE) (map (kent_snapped T) KE) *
  peers_rep PS * itable Tsh (l_ita L) T =
  vobjs W_cookie_reply (hcy5_p12_x_VO x25519 R L T KE ++ [VPeers PS; VItab Tsh (l_ita L) T]).
Proof. unfold vobjs, hcy5_p12_x_VO. simpl. rewrite sepcon_emp, !sepcon_assoc. reflexivity. Qed.

End Helpers.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_x_some_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2) <> nullval ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)
    hcy5_p12_x_sS
    (normal_ret_assert (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)).
Proof.
  intros HH Hinv Ht.
  unfold hcy5_p12_St, hcy5_Delta. simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  assert_PROP (itable_wf T) as HwfT by (unfold itable at 1; entailer!).
  destruct (hcy5_p12_x_spure_ok x25519 xaead_enc xaead_dec R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2
              Hinv HwfT Ht)
    as (nd & o & N & NS1 & NS2 & a & P & P' & PS1 & PS2 & Hc & HNS & HNa & HNp & HNs & HNr & HNrest & HPS' &
        HPr & Hcur & Hsnq & Hnc & Hvo & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9 & Hq10 & Hsame &
        Hin & Hvh & Hvo2 & Hvp).
  unfold hcy5_p12_x_sS.
  assert_PROP (@field_compatible CKS t_hnode4 [] nd) as Hfcn.
  { rewrite HNS. sep_apply (hcy5_p12_x_some_node NS1 N NS2 (hcy5_head (NS1 ++ N :: NS2))). Intros nx.
    rewrite HNa in *. entailer!. }
  sep_apply (hcy5_p12_x_some_cn CL (hcy5_chead CL) _ nd o Hc). Intros.
  forward.
  { apply field_compatible_isptr in Hfcn. entailer!. }
  match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  freeze FR := - (data_at Tsh (tptr t_hnode4) _ _) (hnodes_rep4 _ _ _) (peers_rep _) (itable Tsh (l_ita L) _)
                 (device_rep _ _ _) (kents_rep _ _ _).
  subst nd.
  assert_PROP (is_pointer_or_null (hcy5_head (hnodes_snapped4 T NS PS))) as Hhd.
  { sep_apply (hcy5_p12_x_some_hn_pn (hcy5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca.
  { rewrite HPS', hcy5_p12_x_some_papp. unfold peer_item_rep, peer_rep. Intros. entailer!. }
  assert (Hpa: isptr a) by exact (@field_compatible_isptr Noise.CS _ _ _ Hfca).
  match goal with |- semax _ ?Pre (Ssequence (Sloop _ _) _) _ =>
    apply semax_seq with Pre; [forward_loop Pre continue: Pre break: Pre |] end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (hcy5_p12_x_some_node' _ NS1 N NS2 (hcy5_head (hnodes_snapped4 T NS PS)) HNS). Intros nx.
    unfold hcy5_p12_x_some_flds. Intros.
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    rewrite HNp.
    sep_apply (derives_refl' _ _ (hcy5_p12_x_some_vo1 x25519 R L T KE)).
    forward_call (hcy5_head (hnodes_snapped4 T NS PS), hnodes_snapped4 T NS PS,
                  peers_after PS (hcy5_res xaead_dec T PS CM' now2),
                  hcy5_p12_x_sns T PS, hcy5_p12_x_rs PS, hcy5_p12_x_prs PS, a, Tsh, l_ita L, T,
                  hcy5_p12_x_VO x25519 R L T KE).
    rewrite Hsame.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    sep_apply (derives_refl' _ _ (eq_sym (hcy5_p12_x_some_vo1 x25519 R L T KE))).
    entailer!. }
  { forward. apply ENTAIL_refl. }
  { apply ENTAIL_refl. }
  unfold MORE_COMMANDS, abbreviate.
  (* CHECK(hs_same(&tn->snap, &tn->p->handshake) && tn->p->refcount.refcount == tn->refs &&
           pr_same_but_cookie(&tn->rest, tn->p)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hcy5_p12_x_some_node' _ NS1 N NS2 (hcy5_head (hnodes_snapped4 T NS PS)) HNS). Intros nx.
    unfold hcy5_p12_x_some_flds. Intros.
    rewrite HPS', hcy5_p12_x_some_papp. unfold peer_item_rep. Intros.
    rewrite HNp.
    forward.
    rewrite (hcy5_p12_x_some_snap N (hs_snap_cur T a P) (hn_addr N) Hfcn HNs).
    change (peer_rep Ews a P') with (hs_mem true Ews a P').
    sep_apply (derives_refl' _ _ (hcy5_p12_x_some_vo1 x25519 R L T KE)).
    forward_call (Ews, offset_val 8 (hn_addr N), hs_snap_cur T a P, Ews, a, P', true, Tsh, l_ita L, T,
                  hcy5_p12_x_VO x25519 R L T KE).
    rewrite Hsnq.
    change (hs_mem true Ews a P') with (peer_rep Ews a P').
    sep_apply (derives_refl' _ _ (eq_sym (hcy5_p12_x_some_vo1 x25519 R L T KE))). Intros.
    rewrite <- (hcy5_p12_x_some_snap N (hs_snap_cur T a P) (hn_addr N) Hfcn HNs).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'65 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward.
      sep_apply (hcy5_p12_x_some_refs Ews a P'). Intros.
      forward.
      forward.
      { rewrite HNr. entailer!. }
      rewrite HNr.
      forward.
      match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
      entailer!.
      { rewrite HPr, Int.eq_true. reflexivity. }
      rewrite HNr. apply derives_refl. }
    { exfalso. apply Int.one_not_zero. assumption. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'66 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward.
      rewrite (hcy5_p12_x_some_rest N P (hn_addr N) Hfcn HNrest).
      sep_apply (derives_refl' _ _ (hcy5_p12_x_some_vo3 x25519 R L T KE (PS1 ++ PS2))).
      forward_call (Ews, offset_val 304 (hn_addr N), P, Ews, a, P',
                    hcy5_p12_x_VO x25519 R L T KE ++ [VPeers (PS1 ++ PS2); VItab Tsh (l_ita L) T]).
      { apply Forall_app; split; [exact Hvo | constructor; [exact Hvo2 | constructor; [| constructor]]].
        simpl. apply writable_readable_share; apply writable_share_top. }
      rewrite Hnc.
      sep_apply (derives_refl' _ _ (eq_sym (hcy5_p12_x_some_vo3 x25519 R L T KE (PS1 ++ PS2)))). Intros.
      rewrite <- (hcy5_p12_x_some_rest N P (hn_addr N) Hfcn HNrest).
      forward.
      entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    change (peer_rep Ews a P') with (peer_item_rep (a, Ews, P')).
    sep_apply (derives_refl' _ _ (eq_sym (hcy5_p12_x_some_papp PS1 (a, Ews, P') PS2))).
    rewrite HPS'.
    entailer!.
  }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. thaw FR0.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  entailer!.
Qed.

End Seg.
