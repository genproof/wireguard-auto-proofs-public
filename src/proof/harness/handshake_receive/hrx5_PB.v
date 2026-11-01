(* law handshake_receive: main's phase PB = K's node (statement 14: nk = hnodes_add(&peers, &wd, ik.pub, 0)).
   From hrx5_SA to hrx5_SB (hrx5_defs.v; the cut: hrx5_cut.v). *)
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

Require WgNoise.proof.protocol.prot_rep_lemmas3.

#[local] Instance hrx5_PB_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.

Section HCSl.
#[local] Existing Instance HCS.

(* m_identity without its pub field *)
Definition hrx5_PB_mrest (sh: share) (I: mident) (p: val) : mpred :=
  (field_at sh t_mident (DOT HM._priv) (bytes (mi_priv I)) p *
   field_at sh t_mident (DOT HM._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.

Lemma hrx5_PB_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  data_at sh t_mident (mident_val I) p |--
  (hbytes sh (mi_pub I) (offset_val 32 p) * hrx5_PB_mrest sh I p)%logic.
Proof.
  intros Hl. unfold hrx5_PB_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HM._pub)).
  assert_PROP (field_compatible t_mident (DOT HM._pub) p). { entailer!. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

Lemma hrx5_PB_mident_join sh I p : Zlength (mi_pub I) = 32 ->
  (hbytes sh (mi_pub I) (offset_val 32 p) * hrx5_PB_mrest sh I p)%logic |--
  data_at sh t_mident (mident_val I) p.
Proof.
  intros Hl. unfold hrx5_PB_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HM._pub)).
  assert_PROP (field_compatible t_mident (DOT HM._priv) p). { entailer!. }
  assert (field_compatible t_mident (DOT HM._pub) p).
  { destruct H as (?&?&?&?&?). repeat split; auto. simpl. unfold in_members. simpl. auto. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

End HCSl.

Section PB.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* K's peer satisfies the invariant *)
Lemma hrx5_PB_pok R L sec birth p PSK r :
  x25519_props x25519 -> Zlength PSK = 32 -> 0 < Int.unsigned r < 2147483647 ->
  hrx5_pok x25519 R L
    (p, Ews, p_set_refs (setup_peer_val x25519 (hrx5_DL x25519 R L sec birth) (l_wd L) p nullval
                           (mi_pub (hrx5_IK x25519 R)) PSK (Int64.repr 0)) r).
Proof.
  intros Hx Hpsk Hr. unfold hrx5_pok; simpl.
  assert (Hq: Zlength (mi_pub (hrx5_IK x25519 R)) = 32) by apply Hx.
  repeat split; auto; try (simpl; lia).
  all: try (unfold hs_ok; simpl; repeat split; auto).
  all: try (unfold precomputed; destruct (andb _ _); auto).
  all: try apply Hx.
  all: rep_lia.
Qed.

Lemma hrx5_PB_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SA x25519 gv L FR) hrx5_PB
    (overridePost (hrx5_SB x25519 gv L FR) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_SA, hrx5_Delta, hrx5_R, hrx5_PB. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_lvars, hrx5_scr, hrx5_skb0; cbn [app hrx5_head hrx5_khead].
  assert (HIK: Zlength (mi_pub (hrx5_IK x25519 R)) = 32) by (destruct HH as [Hx _]; apply Hx).
  rewrite <- (hrx5_conv_hnodep_v Tsh nullval (l_peers L)).
  sep_apply (hrx5_PB_mident_split Tsh (hrx5_IK x25519 R) (l_ik L) HIK).
  change (ptable Tsh (l_ptd L) nullval) with (ptable Tsh (d_ptab (hrx5_DL x25519 R L sec birth)) nullval).
  forward_call (gv, Tsh, l_peers L, nullval, @nil hnode4, @nil (val * share * peer), Tsh, l_wd L,
                hrx5_DL x25519 R L sec birth, nullval, Tsh, offset_val 32 (l_ik L), mi_pub (hrx5_IK x25519 R),
                Int64.repr 0).
  { unfold peers_rep; simpl iter_sepcon. rewrite emp_sepcon. cancel. }
  { constructor. }
  Unshelve. all: try exact hrx5_PB_cceK.
  Intros vret. destruct vret as [[[n p] PSK] r]. simpl fst in *; simpl snd in *.
  forward.
  change (d_ptab (hrx5_DL x25519 R L sec birth)) with (l_ptd L).
  destruct (eq_dec n nullval) as [Hn | Hn].
  - subst n. repeat flatten_sepcon_in_SEP.
    sep_apply (hrx5_PB_mident_join Tsh (hrx5_IK x25519 R) (l_ik L) HIK).
    unfold hrx5_SB.
    Exists R sec birth S w (@nil hnode4) (@nil (val * share * peer)) (mkT [] []) nullval nullval.
    unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_lvars, hrx5_scr, hrx5_skb0;
      cbn [app hrx5_head hrx5_khead].
    entailer!.
    unfold hrx5_inv. repeat split; try constructor; auto.
  - destruct (H1 Hn) as [Hpsk Hr].
    destruct HH as [Hx _].
    repeat flatten_sepcon_in_SEP.
    sep_apply (hrx5_PB_mident_join Tsh (hrx5_IK x25519 R) (l_ik L) HIK).
    assert_PROP (isptr p) as Hpp.
    { unfold peers_rep; simpl iter_sepcon. unfold peer_rep. Intros. entailer!.
      match goal with H: field_compatible t_peer [] p |- _ => destruct H as [? _]; assumption end. }
    sep_apply (WgNoise.proof.protocol.prot_rep_lemmas3.prot_rep3_pool_add Tsh (l_itd L) (mkT [] []) (hs_addr p) Ews
                 (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
    unfold hrx5_SB.
    Exists R sec birth S w [mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)]
      [(p, Ews, p_set_refs (setup_peer_val x25519 (hrx5_DL x25519 R L sec birth) (l_wd L) p nullval
                              (mi_pub (hrx5_IK x25519 R)) PSK (Int64.repr 0)) r)]
      (t_add (mkT [] []) (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)) p n.
    unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_lvars, hrx5_scr, hrx5_skb0;
      cbn [app hrx5_head hrx5_khead].
    entailer!.
    2: apply derives_refl.
    unfold hrx5_inv. split; [| split; [| split; [| split; [| split; [| split]]]]].
    + constructor; [apply hrx5_PB_pok; auto | constructor].
    + constructor; [apply writable_Ews | constructor].
    + simpl. constructor; [intros [] | constructor].
    + simpl. auto.
    + reflexivity.
    + right; simpl; auto.
    + unfold hrx5cr_pool. simpl. split; [constructor |].
      constructor; [simpl; auto | constructor].
Qed.

End PB.
