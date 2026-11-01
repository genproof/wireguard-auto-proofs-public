(* law handshake_receive, B8 branch C part T: separation helpers of segment C2
   (node fields, snapshot / rest at their offsets, the peer's reference count, the lent objects).
   Port of cookie_reply's hcy5_p12_x_some.v helpers (prefix hrx5_B8CT_). *)
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_T_pure.
Local Open Scope Z_scope.

#[local] Instance hrx5_B8CT_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_B8CT_cceKH : change_composite_env CKS HCS.
Proof. make_cs_preserve CKS HCS. Defined.
#[local] Instance hrx5_B8CT_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Section Helpers.
Local Open Scope logic.

Lemma hrx5_B8CT_wf (A F B: mpred) : A * (F * (F -* B)) |-- F * (F -* (A * B)).
Proof.
  rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

(* a node's fields *)
Definition hrx5_B8CT_flds (N: hnode4) (nx: val) : mpred :=
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) (hn_addr N) *
  @field_at W_handshake_receive Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_addr N) *
  spacer Ews 300 304 (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 (DOT HC._next) nx (hn_addr N).

Lemma hrx5_B8CT_cell N nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) =
  hrx5_B8CT_flds N nx.
Proof.
  unfold hrx5_B8CT_flds. unfold data_at. unfold_field_at 1%nat.
  rewrite (@field_at_cs_eq CKS W_handshake_receive _ Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_p N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  rewrite (@field_at_cs_eq CKS W_handshake_receive _ Ews t_hnode4 (DOT HC._refs) (hn_refs N) (hn_refs N) (hn_addr N))
    by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Lemma hrx5_B8CT_node NS1 N NS2 : forall l,
  hnodes_rep4 W_handshake_receive l (NS1 ++ N :: NS2) |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hrx5_B8CT_flds N nx *
     (hrx5_B8CT_flds N nx -* hnodes_rep4 W_handshake_receive l (NS1 ++ N :: NS2))).
Proof.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx.
    assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as Hfc.
    { sep_apply (@data_at_local_facts CKS). entailer!. }
    rewrite hrx5_B8CT_cell. entailer!.
    rewrite <- wand_sepcon_adjoint. Exists nx. rewrite hrx5_B8CT_cell. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. entailer!.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hrx5_B8CT_node' NS NS1 N NS2 l : NS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W_handshake_receive l NS |--
  EX nx: val, !! @field_compatible CKS t_hnode4 [] (hn_addr N) &&
    (hrx5_B8CT_flds N nx * (hrx5_B8CT_flds N nx -* hnodes_rep4 W_handshake_receive l NS)).
Proof. intros ->. apply hrx5_B8CT_node. Qed.

Lemma hrx5_B8CT_hn_pn l NS : hnodes_rep4 W_handshake_receive l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    apply isptr_is_pointer_or_null; exact Hp.
Qed.

Lemma hrx5_B8CT_snap N sn l : @field_compatible CKS t_hnode4 [] l -> hn_snap N = hsnap_val sn ->
  @field_at CKS Ews t_hnode4 (DOT HC._snap) (hn_snap N) l = @data_at HCS Ews t_hsnap (hsnap_val sn) (offset_val 8 l).
Proof.
  intros Hfc E. rewrite E.
  rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
  apply (@data_at_cs_eq CKS HCS hrx5_B8CT_cceKH); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_B8CT_rest N P0 l : @field_compatible CKS t_hnode4 [] l -> hn_rest N = prsnap_val P0 ->
  @field_at CKS Ews t_hnode4 (DOT HC._rest) (hn_rest N) l = @data_at CKS Ews t_prsnap (prsnap_val P0) (offset_val 304 l).
Proof.
  intros Hfc E. rewrite E.
  rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible. reflexivity.
Qed.

(* the reference count of a peer, at the world *)
Lemma hrx5_B8CT_kref sh p (v: val) :
  @field_at W_handshake_receive sh t_peer (DOT HC._refcount) v p =
  @field_at W_handshake_receive sh t_peer (DOT HC._refcount DOT HC._refcount) v p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hrx5_B8CT_refs sh p P :
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
  rewrite EQ, hrx5_B8CT_kref. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite <- hrx5_B8CT_kref, <- EQ. entailer!.
Qed.

Lemma hrx5_B8CT_papp PS1 x PS2 : peers_rep (PS1 ++ x :: PS2) = peer_item_rep x * peers_rep (PS1 ++ PS2).
Proof. unfold peers_rep. rewrite !iter_sepcon_app. simpl. apply pred_ext; cancel. Qed.

(* the lent objects *)
Lemma hrx5_B8CT_vo1 x25519 R L sec birth T KE :
  device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth) *
  kents_rep W_handshake_receive (hrx5_khead (map (kent_snapped T) KE)) (map (kent_snapped T) KE) =
  vobjs W_handshake_receive (hrx5_B8CT_VO x25519 R L sec birth T KE).
Proof. unfold vobjs, hrx5_B8CT_VO. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_B8CT_vo2 x25519 R L sec birth T KE PS :
  device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth) *
  kents_rep W_handshake_receive (hrx5_khead (map (kent_snapped T) KE)) (map (kent_snapped T) KE) *
  peers_rep PS = vobjs W_handshake_receive (hrx5_B8CT_VO x25519 R L sec birth T KE ++ [VPeers PS]).
Proof. unfold vobjs, hrx5_B8CT_VO. simpl. rewrite sepcon_emp, !sepcon_assoc. reflexivity. Qed.

End Helpers.
