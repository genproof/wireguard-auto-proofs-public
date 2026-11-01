(* law handshake_clear, phase P7: segment chk of the loop body.
   CHK = CHECK(hs_same_but_next(&nd->snap, &nd->p->handshake) && nd->p->refcount.refcount == nd->refs && pr_same(&nd->rest, nd->p)) for the node k <> i: the state does not change.
   States and statements: hcl5_p7_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_chk_lem.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_chk_body.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p7_chk_ok {Espec: OracleKind} gv L FR R S w NS PS T head KE i k nx q Q :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_p7_Q0 x25519 gv L FR R S w NS PS T head KE i k nx q Q) hcl5_p7_chk
    (overridePost (hcl5_p7_Q0 x25519 gv L FR R S w NS PS T head KE i k nx q Q) (hcl5_R gv)).
Proof.
  intros HH.
  unfold hcl5_p7_Q0 at 1. unfold hcl5_p7_Q at 1. cbn [app].
  Intros.
  match goal with H: hcl5_inv _ _ _ _ _ _ |- _ => pose proof H as Hinv0; destruct H as (Hpok & Hwf & Hch & Hnp & Htok & Hslots) end.
  match goal with H: Znth k PS = (q, Ews, Q) |- _ => rename H into EK end.
  match goal with H: k <> i |- _ => rename H into Hki end.
  match goal with H: 0 <= i < Zlength NS |- _ => rename H into Hi end.
  match goal with H: 0 <= k < Zlength NS |- _ => rename H into Hk end.
  pose proof (hcl5_p7_chk_len_peers _ _ Hnp) as HL.
  assert (Hpq: hcl5_pok L (q, Ews, Q)) by (rewrite <- EK; apply Forall_Znth; [first [exact Hpok | lia] | first [exact Hpok | lia]]).
  destruct Hpq as (_ & Hdev & Hsid & _ & _).
  pose proof (Znth_In k PS ltac:(lia)) as HinQ. rewrite EK in HinQ.
  pose proof Htok as Htok0. destruct Htok as (Hsa & Hsh & Hep & _).
  assert (Hin: In (hs_addr q) (saddrs (t_D T))).
  { rewrite Hsa, in_app_iff. right. apply in_map_iff. eexists. split; [|exact HinQ]. reflexivity. }
  assert (Hep1: e_peer (t_entry_d T (hs_addr q)) = q).
  { rewrite Forall_forall in Hep. exact (Hep _ HinQ). }
  assert (Hsl: Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur Q; p_prev Q; p_next Q]).
  { unfold hcl5_slots_ok in Hslots. rewrite Forall_forall in Hslots. exact (Hslots _ HinQ). }
  assert (Hke: incl (map ke_addr KE) (saddrs (t_D T))).
  { intros kk Hkk. rewrite Hsa, in_app_iff. left. exact Hkk. }
  set (C := hcl5_clr i PS).
  set (others := sublist 0 k C ++ sublist (k + 1) (Zlength C) C).
  assert (Hpkn: p_pknext Q = nullval \/ In (p_pknext Q) (map peer_addr4 others)).
  { subst others C. rewrite hcl5_p7_chk_others_addrs by lia.
    exact (hcl5_p7_chk_pknext head PS k q Ews Q Hch ltac:(lia) EK). }
  assert (Hoth: Forall (fun y => match y with (_, sh, _) => sh = Ews end) others).
  { subst others C. apply hcl5_p7_chk_others_sh; [lia|].
    eapply Forall_impl; [|exact Hpok]. intros [[b sh] Q'] Hq. exact (proj1 Hq). }
  assert (EC: Znth k C = (q, Ews, Q)) by (subst C; rewrite hcl5_p7_chk_clr_nth by lia; exact EK).
  assert (HLC: Zlength C = Zlength PS) by (subst C; apply hcl5_p7_chk_clr_len; lia).
  assert (Ehp: hn_p (Znth i NS) = peer_addr4 (Znth i PS)) by (apply hcl5_p7_chk_hn_p; auto).
  unfold hcl5_p7_fix. cbn [app].
  assert_PROP (NoDup (saddrs (t_D T))) as Hnd.
  { unfold itable. Intros. match goal with Hw: itable_wf _ |- _ => destruct Hw as (_ & _ & Hw0 & _) end. apply prop_right. exact Hw0. }
  assert (Hne: hs_addr q <> hs_addr (hn_p (Znth i NS))).
  { rewrite Ehp. replace q with (peer_addr4 (Znth k PS)) by (rewrite EK; reflexivity).
    apply (hcl5_p7_chk_ne (t_D T) KE PS i k Hsa Hnd); lia. }
  change (peers_rep (hcl5_clr i PS)) with (peers_rep C).
  rewrite (hcl5_p7_chk_peers_at k C) by lia. fold others. rewrite EC. cbn [peer_item_rep].
  set (FRM := (ptable Tsh (l_pt L) head * hbytes Tsh (r_raw R) (l_raw L) *
               @data_at W_handshake_clear Tsh (tptr t_hnode4) (hcl5_head NS) (l_peers L) *
               @data_at CKS Tsh t_devsnap (devsnap_val (hcl5_D x25519 R L) head) (l_ds L) *
               @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L) *
               mem_mgr gv * shim_state4 gv S w * wg_consts gv * FR * hout Tsh 32 (l_pub L) *
               hcl5_p7_seg (hcl5_head NS) (hn_addr (Znth k NS)) (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS)) *
               @malloc_token W_handshake_clear Ews t_hnode4 (hn_addr (Znth k NS)) *
               @malloc_token W_handshake_clear Ews t_peer q *
               hnodes_rep4 W_handshake_clear nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS)))%logic).
  apply semax_pre with (P' := hcl5_p7_chk_S gv L KE (hn_addr (Znth k NS))
     (Vlong (Int64.repr (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat k) PS))))
     (hn_addr (Znth i NS)) q Q T (hs_addr (hn_p (Znth i NS))) nx (hcl5_D x25519 R L) others FRM).
  { unfold hcl5_p7_chk_S, FRM. cbn [app]. go_lowerx.
    apply andp_right; [apply prop_right; repeat (split; [assumption|]); auto |]. cancel. }
  eapply semax_post; [| | | | apply (hcl5_p7_chk_body x25519 gv L KE (hn_addr (Znth k NS))
     (Vlong (Int64.repr (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat k) PS))))
     (hn_addr (Znth i NS)) q Q T (hs_addr (hn_p (Znth i NS))) nx (hcl5_D x25519 R L) others FRM (hcl5_R gv)); auto].
  2-4: unfold overridePost; destruct (hcl5_R gv) as [Rn Rb Rc Rr]; simpl; try intros; apply andp_left2, derives_refl.
  unfold overridePost; destruct (hcl5_R gv) as [Rn Rb Rc Rr]; simpl RA_normal.
  unfold hcl5_p7_chk_S, hcl5_p7_Q0, hcl5_p7_Q, hcl5_p7_fix, FRM. cbn [app].
  change (peers_rep (hcl5_clr i PS)) with (peers_rep C).
  rewrite (hcl5_p7_chk_peers_at k C) by lia. fold others. rewrite EC. cbn [peer_item_rep].
  go_lowerx.
  apply andp_right; [apply prop_right; repeat (split; [first [assumption | lia]|]); auto |].
  apply andp_right; [apply prop_right; repeat (split; [assumption|]); auto |]. cancel.
Qed.

End Seg.
