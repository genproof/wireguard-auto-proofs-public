(* law handshake_receive, B8 branch R segment A: separation helpers (node fields,
   the shim's allocation failures, the shim snapshot's alloc_failures, the accepted peer's device field and
   reference count).  Node helpers ported from hrx5_B8_C_T_sep.v, peer helpers from
   hrx5_recv_RS_lem.v; prefix hrx5_B8RA_. *)
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
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope Z_scope.
Local Open Scope logic.

#[local] Instance hrx5_B8RA_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_B8RA_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_B8RA_lend (A B C: mpred) : (A |-- B * C)%logic -> (B * C |-- A)%logic -> (A |-- B * (B -* A))%logic.
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hrx5_B8RA_lendF (A B: mpred) (F: list mpred) :
  (A |-- B * fold_right_sepcon F)%logic -> (B * fold_right_sepcon F |-- A)%logic -> (A |-- B * (B -* A))%logic.
Proof. apply hrx5_B8RA_lend. Qed.

Ltac hrx5_B8RA_frame :=
  match goal with |- ?L |-- fold_right_sepcon ?F => unify F (L :: nil) end;
  simpl fold_right_sepcon; rewrite sepcon_emp; apply derives_refl.

(* ---- the nodes ---- *)

Definition hrx5_B8RA_flds (N: hnode4) (nx: val) : mpred :=
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) (hn_addr N) *
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_addr N) *
  spacer Ews 300 304 (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._next) nx (hn_addr N).

Lemma hrx5_B8RA_cell N nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) =
  hrx5_B8RA_flds N nx.
Proof.
  unfold hrx5_B8RA_flds. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS W_handshake_receive _ Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_p N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS W_handshake_receive _ Ews t_hnode4 [StructField HC._refs] (hn_refs N) (hn_refs N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hrx5_B8RA_node NS1 N NS2 : forall l,
  hnodes_rep4 W_handshake_receive l (NS1 ++ N :: NS2) |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hrx5_B8RA_flds N nx *
     (hrx5_B8RA_flds N nx -* hnodes_rep4 W_handshake_receive l (NS1 ++ N :: NS2))).
Proof.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx.
    assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as Hfc.
    { sep_apply (@data_at_local_facts CKS). entailer!. }
    rewrite hrx5_B8RA_cell. entailer!.
    rewrite <- wand_sepcon_adjoint. Exists nx. rewrite hrx5_B8RA_cell. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. entailer!.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hrx5_B8RA_node' NS NS1 N NS2 l : NS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W_handshake_receive l NS |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hrx5_B8RA_flds N nx * (hrx5_B8RA_flds N nx -* hnodes_rep4 W_handshake_receive l NS)).
Proof. intros ->. apply hrx5_B8RA_node. Qed.

(* the node's rest snapshot: its is_dead field at the world *)
Lemma hrx5_B8RA_dead P l :
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (prsnap_val P) l |--
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._rest DOT HC._is_dead) (Val.of_bool (p_dead P)) l *
  (@field_at W_handshake_receive Ews t_hnode4 (DOT HC._rest DOT HC._is_dead) (Val.of_bool (p_dead P)) l -*
   @field_at CKS Ews t_hnode4 (DOT HC._rest) (prsnap_val P) l).
Proof.
  assert (EQ: @field_at CKS Ews t_hnode4 (DOT HC._rest DOT HC._is_dead) (Val.of_bool (p_dead P)) l =
     @field_at W_handshake_receive Ews t_hnode4 (DOT HC._rest DOT HC._is_dead) (Val.of_bool (p_dead P)) l)
    by (apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  rewrite <- EQ.
  assert_PROP (@field_compatible CKS t_hnode4 [StructField HC._rest] l) as FC by entailer!.
  assert (FC2: @field_compatible CKS t_hnode4 [StructField HC._is_dead; StructField HC._rest] l)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (@nested_field_ramif CKS Ews t_hnode4 [StructField HC._rest] [StructField HC._is_dead] (prsnap_val P)
    (Val.of_bool (p_dead P)) l (JMeq_refl _) FC2) as RM.
  eapply derives_trans; [exact RM|].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (Val.of_bool (p_dead P))). apply (allp_left _ (Val.of_bool (p_dead P))).
  rewrite prop_imp by apply JMeq_refl.
  apply derives_refl.
Qed.

(* ---- the shim ---- *)

Lemma hrx5_B8RA_fails gv S w :
  shim_state4 gv S w |--
  @data_at W_handshake_receive Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) *
  (@data_at W_handshake_receive Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) -*
   shim_state4 gv S w).
Proof.
  assert (EQ: @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) =
    @data_at W_handshake_receive Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures))
    by (apply data_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert_PROP (shim_ok S) as HS by (unfold shim_state4, shim_core; entailer!).
  eapply hrx5_B8RA_lendF; unfold shim_state4, shim_core; rewrite <- EQ.
  - Intros. cancel. hrx5_B8RA_frame.
  - simpl. entailer!.
Qed.

Lemma hrx5_B8RA_ss S w p :
  @data_at CKS Tsh t_shimsnap (shimsnap_val S w) p |--
  @field_at W_handshake_receive Tsh t_shimsnap (DOT HC._alloc_failures) (Vlong (s_fails S)) p *
  (@field_at W_handshake_receive Tsh t_shimsnap (DOT HC._alloc_failures) (Vlong (s_fails S)) p -*
   @data_at CKS Tsh t_shimsnap (shimsnap_val S w) p).
Proof.
  assert (EQ: @field_at CKS Tsh t_shimsnap (DOT HC._alloc_failures) (Vlong (s_fails S)) p =
     @field_at W_handshake_receive Tsh t_shimsnap (DOT HC._alloc_failures) (Vlong (s_fails S)) p)
    by (apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  rewrite <- EQ.
  assert_PROP (@field_compatible CKS t_shimsnap [] p) as FC by entailer!.
  assert (FC2: @field_compatible CKS t_shimsnap [StructField HC._alloc_failures] p)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (@nested_field_ramif CKS Tsh t_shimsnap [] [StructField HC._alloc_failures] (shimsnap_val S w)
    (Vlong (s_fails S)) p (JMeq_refl _) FC2) as RM.
  unfold data_at at 1.
  eapply derives_trans; [exact RM|].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (Vlong (s_fails S))). apply (allp_left _ (Vlong (s_fails S))).
  rewrite prop_imp by apply JMeq_refl.
  apply derives_refl.
Qed.

(* ---- the accepted peer ---- *)

Lemma hrx5_B8RA_sfind_supd {A: Type} (l: list (val * share * A)) a sh v0 v :
  sfind l a = Some (sh, v0) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - inv H. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | auto].
Qed.

Lemma hrx5_B8RA_sdel_supd {A: Type} (l: list (val * share * A)) a v : sdel (supd l a v) a = sdel l a.
Proof.
  induction l as [|[[x shx] u] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - destruct (EqDec_val x a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | rewrite IH; reflexivity].
Qed.

Lemma hrx5_B8RA_peers_supd PS a sh P P1 : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a P1) = peer_rep sh a P1 * iter_sepcon peer_item_rep (sdel PS a).
Proof.
  intros Hf. unfold peers_rep.
  rewrite (prot_rep3_split (supd PS a P1) a sh P1) by (eapply hrx5_B8RA_sfind_supd; eauto).
  rewrite hrx5_B8RA_sdel_supd. reflexivity.
Qed.

Lemma hrx5_B8RA_pfield sh p P :
  peer_rep sh p P |-- rx_pfield sh p (p_device P) * (rx_pfield sh p (p_device P) -* peer_rep sh p P).
Proof.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as FC by (unfold peer_rep; entailer!).
  eapply hrx5_B8RA_lendF; unfold peer_rep, rx_pfield.
  - Intros. cancel. hrx5_B8RA_frame.
  - simpl. entailer!.
Qed.

Lemma hrx5_B8RA_refs sh p P :
  peer_rep sh p P |--
  @field_at W_handshake_receive sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p *
  (@field_at W_handshake_receive sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p -* peer_rep sh p P).
Proof.
  unfold peer_rep. Intros.
  match goal with |- ?a1 * ?a2 * ?a3 * ?a4 * ?a5 * ?a6 * ?F * ?a8 * ?a9 * ?a10 * ?a11 |-- _ =>
    apply derives_trans with (F * (a1 * a2 * a3 * a4 * a5 * a6 * a8 * a9 * a10 * a11)); [cancel|] end.
  assert (EQ: @field_at Noise.CS sh t_peer (DOT I._refcount) (Vint (p_refs P)) p =
              @field_at W_handshake_receive sh t_peer (DOT HC._refcount) (Vint (p_refs P)) p)
    by (apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (KR: @field_at W_handshake_receive sh t_peer (DOT HC._refcount) (Vint (p_refs P)) p =
              @field_at W_handshake_receive sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p)
    by (unfold_field_at 1%nat; reflexivity).
  rewrite EQ, KR. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite <- KR, <- EQ. entailer!.
Qed.

(* ---- the accepted peer's node ---- *)

Lemma hrx5_B8RA_snapped_len T NS PS : Zlength NS = Zlength PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength PS.
Proof.
  intros HL. unfold hnodes_snapped4. rewrite Zlength_map, !Zlength_correct, combine_length.
  rewrite !Zlength_correct in HL. lia.
Qed.

Lemma hrx5_B8RA_split T NS PS j : Zlength NS = Zlength PS -> 0 <= j < Zlength PS ->
  hnodes_snapped4 T NS PS =
  sublist 0 j (hnodes_snapped4 T NS PS) ++ hn_snapshot4 T (Znth j NS) (Znth j PS) ::
  sublist (j + 1) (Zlength PS) (hnodes_snapped4 T NS PS).
Proof.
  intros HL Hj. pose proof (hrx5_B8RA_snapped_len T NS PS HL) as HL2.
  set (l := hnodes_snapped4 T NS PS) in *.
  transitivity (sublist 0 j l ++ sublist j (Zlength PS) l).
  { rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. }
  f_equal. rewrite (sublist_next j (Zlength PS) l) by lia. f_equal.
  unfold l, hnodes_snapped4. rewrite Znth_map.
  - rewrite Znth_combine by exact HL. reflexivity.
  - assert (E: Zlength (combine NS PS) = Zlength PS); [| rewrite E; lia].
    rewrite !Zlength_correct, combine_length. rewrite !Zlength_correct in HL. lia.
Qed.
