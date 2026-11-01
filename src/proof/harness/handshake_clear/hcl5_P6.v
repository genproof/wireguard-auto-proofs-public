(* law handshake_clear: main's phase P6, statements 16..18: CHECK(hs_zeroed_from(&target->snap, h) && !h->entry.hashed && h->entry.index == target->snap.index); if (target->snap.hashed) CHECK(h->entry.next == NULL) else CHECK(h->entry.next == target->snap.next); CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p)).
   (states: hcl5_defs.v). *)
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
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_lem.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_defs.
Require WgNoise.harness.x_handshake_clear.code.

Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_s16.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_s17.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_s18.
#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

Section P6.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_P6_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_S5 x25519 gv L FR) hcl5_P6
    (overridePost (hcl5_S5 x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_S5 at 1.
  Intros R S w NS PS T head KE i.
  unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_scr; cbn [app].
  match goal with H: hcl5_inv _ _ _ _ _ _ |- _ => pose proof H as Hinv0; destruct H as (Hpok & Hwf & Hch & Hnp & Htok & Hslots) end.
  rename H1 into Hi.
  pose proof (hcl5_p6_len_peers _ _ Hnp) as HL.
  destruct (Znth i PS) as [[p sh] P] eqn:EP.
  assert (Hpk: hcl5_pok L (p, sh, P)) by (rewrite <- EP; apply Forall_Znth; [first [exact Hpok | lia] | first [exact Hpok | lia]]).
  destruct Hpk as (-> & Hdev & Hsid & _ & _).
  assert (Ehp: hn_p (Znth i NS) = p) by (rewrite (hcl5_p6_hn_p NS PS i Hnp Hi), EP; reflexivity).
  set (others := sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS).
  pose proof (Znth_In i PS ltac:(lia)) as HinP. rewrite EP in HinP.
  destruct Htok as (Hsa & Hsh & Hep & _).
  assert (Hin: In (hs_addr p) (saddrs (t_D T))).
  { rewrite Hsa, in_app_iff. right. apply in_map_iff. eexists. split; [|exact HinP]. reflexivity. }
  assert (Hep1: e_peer (t_entry_d T (hs_addr p)) = p).
  { rewrite Forall_forall in Hep. exact (Hep _ HinP). }
  assert (Hsl: Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P]).
  { unfold hcl5_slots_ok in Hslots. rewrite Forall_forall in Hslots. exact (Hslots _ HinP). }
  assert (Hke: incl (map ke_addr KE) (saddrs (t_D T))).
  { intros k Hk. rewrite Hsa, in_app_iff. left. exact Hk. }
  assert (Hpkn: p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 others)).
  { exact (hcl5_p6_pknext head PS i p _ P Hch ltac:(lia) EP). }
  assert (Hoth: Forall (fun y => match y with (_, sh, _) => sh = Ews end) others).
  { subst others. apply Forall_app; split; apply Forall_sublist;
      (eapply Forall_impl; [|exact Hpok]); intros [[a sh] Q] Hq; exact (proj1 Hq). }
  rewrite Ehp.
  unfold hcl5_clr. rewrite EP. cbn [hcl5_clr1].
  rewrite (hcl5_p6_peers_split i PS _ ltac:(lia)). cbn [peer_item_rep]. fold others.
  sep_apply (hcl5_p6_node_open T NS PS i p _ P Hnp Hi EP). Intros nx.
  set (WN := (@data_at W Ews t_hnode4 (hcl5_p6_nv p (hs_snap_cur T p P) (p_refs P) P nx) (hn_addr (Znth i NS)) -*
              hnodes_rep4 W (hcl5_head NS) (hnodes_snapped4 T NS PS))%logic).
  set (FRM := (ptable Tsh (l_pt L) head * hbytes Tsh (r_raw R) (l_raw L) *
               @data_at W Tsh (tptr t_hnode4) (hcl5_head NS) (l_peers L) *
               @data_at CKS Tsh t_devsnap (devsnap_val (hcl5_D x25519 R L) head) (l_ds L) *
               @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L) *
               mem_mgr gv * shim_state4 gv S w * wg_consts gv * FR * hout Tsh 32 (l_pub L))%logic).
  apply semax_pre with (P' := hcl5_p6_Q gv L KE (hn_addr (Znth i NS)) p P T nx (hcl5_D x25519 R L) others WN FRM).
  { unfold hcl5_p6_Q, WN, FRM. entailer!. }
  rewrite hcl5_p6_stmts.
  eapply semax_seq; [apply hcl5_p6_seg16; auto |].
  eapply semax_seq; [apply hcl5_p6_seg17; auto |].
  eapply semax_post; [| | | | apply (hcl5_p6_seg18 x25519 gv L KE (hn_addr (Znth i NS)) p P T nx (hcl5_D x25519 R L)
                                       others WN FRM (hcl5_R gv)); auto].
  2-4: unfold overridePost; destruct (hcl5_R gv) as [Rn Rb Rc Rr]; simpl; try intros; apply andp_left2, derives_refl.
  unfold overridePost; destruct (hcl5_R gv) as [Rn Rb Rc Rr]; simpl RA_normal.
  unfold hcl5_p6_Q, hcl5_S5, WN, FRM.
  Exists R S w NS PS T head KE i.
  unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_scr; cbn [app].
  rewrite Ehp. unfold hcl5_clr. rewrite EP. cbn [hcl5_clr1].
  rewrite (hcl5_p6_peers_split i PS _ ltac:(lia)). cbn [peer_item_rep]. fold others.
  sep_apply (hcl5_p6_mp (@data_at W Ews t_hnode4 (hcl5_p6_nv p (hs_snap_cur T p P) (p_refs P) P nx) (hn_addr (Znth i NS)))
               (hnodes_rep4 W (hcl5_head NS) (hnodes_snapped4 T NS PS))).
  entailer!.
Qed.

End P6.
